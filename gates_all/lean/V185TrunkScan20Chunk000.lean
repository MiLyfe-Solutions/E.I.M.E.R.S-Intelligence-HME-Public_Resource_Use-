import V185TrunkScan19Incremental

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_29 : List Nat := [1, 4, 2, 2, 2, 3, 2, 1, 3]
def baseStart_29 : Nat := 118140960795 + 29 * 2 ^ 59
def prefixEnd_29 : Nat := 4983230072969 + 3 ^ 40 * 29 * 2
def baseEnd_29 : Nat := 13236390298329099887

theorem tailTrace_29 : CollatzResearch.WordTrace tailWord_29 prefixEnd_29 13236390298329099887 := by
  unfold tailWord_29
  simp only [CollatzResearch.WordTrace]
  refine ⟨1057716902412797915141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 705144601608531943427 1057716902412797915141)
  ·
    refine ⟨198321919202399609089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1057716902412797915141 198321919202399609089)
    ·
      refine ⟨148741439401799706817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198321919202399609089 148741439401799706817)
      ·
        refine ⟨111556079551349780113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148741439401799706817 111556079551349780113)
        ·
          refine ⟨83667059663512335085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111556079551349780113 83667059663512335085)
          ·
            refine ⟨31375147373817125657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83667059663512335085 31375147373817125657)
            ·
              refine ⟨23531360530362844243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31375147373817125657 23531360530362844243)
              ·
                refine ⟨35297040795544266365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23531360530362844243 35297040795544266365)
                ·
                  refine ⟨13236390298329099887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35297040795544266365 13236390298329099887)
                  ·
                    rfl

theorem cell20_29_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_29 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29 prefixEnd_29 := by exact prefixLift 29
  have htrace : WordTrace (prefixWord ++ tailWord_29) baseStart_29 baseEnd_29 := by
    simpa [prefixWord, tailWord_29, baseEnd_29] using wordTrace_append hprefix tailTrace_29
  have hstable : (prefixWord ++ tailWord_29).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29).length < 2 ^ (prefixWord ++ tailWord_29).sum := by decide
  have hdescent : baseEnd_29 < baseStart_29 := by decide
  rcases family_descends (prefixWord ++ tailWord_29) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68 : List Nat := [2, 3, 15]
def baseStart_68 : Nat := 118140960795 + 68 * 2 ^ 59
def prefixEnd_68 : Nat := 4983230072969 + 3 ^ 40 * 68 * 2
def baseEnd_68 : Nat := 42574832630352263

theorem tailTrace_68 : CollatzResearch.WordTrace tailWord_68 prefixEnd_68 42574832630352263 := by
  unfold tailWord_68
  simp only [CollatzResearch.WordTrace]
  refine ⟨1240081880561229292429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1653442507414972389905 1240081880561229292429)
  ·
    refine ⟨465030705210460984661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1240081880561229292429 465030705210460984661)
    ·
      refine ⟨42574832630352263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 15 465030705210460984661 42574832630352263)
      ·
        rfl

theorem cell20_68_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 15].length) (baseStart_68 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68 prefixEnd_68 := by exact prefixLift 68
  have htrace : WordTrace (prefixWord ++ tailWord_68) baseStart_68 baseEnd_68 := by
    simpa [prefixWord, tailWord_68, baseEnd_68] using wordTrace_append hprefix tailTrace_68
  have hstable : (prefixWord ++ tailWord_68).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68).length < 2 ^ (prefixWord ++ tailWord_68).sum := by decide
  have hdescent : baseEnd_68 < baseStart_68 := by decide
  rcases family_descends (prefixWord ++ tailWord_68) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71 : List Nat := [1, 1, 4, 1, 3, 1, 4, 2, 3]
def baseStart_71 : Nat := 118140960795 + 71 * 2 ^ 59
def prefixEnd_71 : Nat := 4983230072969 + 3 ^ 40 * 71 * 2
def baseEnd_71 : Nat := 32406334732849699715

theorem tailTrace_71 : CollatzResearch.WordTrace tailWord_71 prefixEnd_71 32406334732849699715 := by
  unfold tailWord_71
  simp only [CollatzResearch.WordTrace]
  refine ⟨2589582750253970944067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1726388500169313962711 2589582750253970944067)
  ·
    refine ⟨3884374125380956416101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2589582750253970944067 3884374125380956416101)
    ·
      refine ⟨728320148508929328019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3884374125380956416101 728320148508929328019)
      ·
        refine ⟨1092480222763393992029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 728320148508929328019 1092480222763393992029)
        ·
          refine ⟨409680083536272747011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1092480222763393992029 409680083536272747011)
          ·
            refine ⟨614520125304409120517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409680083536272747011 614520125304409120517)
            ·
              refine ⟨115222523494576710097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 614520125304409120517 115222523494576710097)
              ·
                refine ⟨86416892620932532573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115222523494576710097 86416892620932532573)
                ·
                  refine ⟨32406334732849699715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86416892620932532573 32406334732849699715)
                  ·
                    rfl

theorem cell20_71_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 3].length) (baseStart_71 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71 prefixEnd_71 := by exact prefixLift 71
  have htrace : WordTrace (prefixWord ++ tailWord_71) baseStart_71 baseEnd_71 := by
    simpa [prefixWord, tailWord_71, baseEnd_71] using wordTrace_append hprefix tailTrace_71
  have hstable : (prefixWord ++ tailWord_71).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71).length < 2 ^ (prefixWord ++ tailWord_71).sum := by decide
  have hdescent : baseEnd_71 < baseStart_71 := by decide
  rcases family_descends (prefixWord ++ tailWord_71) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85 : List Nat := [1, 3, 2, 2, 1, 3, 3, 5]
def baseStart_85 : Nat := 118140960795 + 85 * 2 ^ 59
def prefixEnd_85 : Nat := 4983230072969 + 3 ^ 40 * 85 * 2
def baseEnd_85 : Nat := 12932105403674410997

theorem tailTrace_85 : CollatzResearch.WordTrace tailWord_85 prefixEnd_85 12932105403674410997 := by
  unfold tailWord_85
  simp only [CollatzResearch.WordTrace]
  refine ⟨3100204699534361953709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2066803133022907969139 3100204699534361953709)
  ·
    refine ⟨1162576762325385732641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3100204699534361953709 1162576762325385732641)
    ·
      refine ⟨871932571744039299481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1162576762325385732641 871932571744039299481)
      ·
        refine ⟨653949428808029474611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 871932571744039299481 653949428808029474611)
        ·
          refine ⟨980924143212044211917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653949428808029474611 980924143212044211917)
          ·
            refine ⟨367846553704516579469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 980924143212044211917 367846553704516579469)
            ·
              refine ⟨137942457639193717301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 367846553704516579469 137942457639193717301)
              ·
                refine ⟨12932105403674410997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137942457639193717301 12932105403674410997)
                ·
                  rfl

theorem cell20_85_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 5].length) (baseStart_85 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_85 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_85 prefixEnd_85 := by exact prefixLift 85
  have htrace : WordTrace (prefixWord ++ tailWord_85) baseStart_85 baseEnd_85 := by
    simpa [prefixWord, tailWord_85, baseEnd_85] using wordTrace_append hprefix tailTrace_85
  have hstable : (prefixWord ++ tailWord_85).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85).length < 2 ^ (prefixWord ++ tailWord_85).sum := by decide
  have hdescent : baseEnd_85 < baseStart_85 := by decide
  rcases family_descends (prefixWord ++ tailWord_85) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 6]
def baseStart_99 : Nat := 118140960795 + 99 * 2 ^ 59
def prefixEnd_99 : Nat := 4983230072969 + 3 ^ 40 * 99 * 2
def baseEnd_99 : Nat := 45186297689196766267

theorem tailTrace_99 : CollatzResearch.WordTrace tailWord_99 prefixEnd_99 45186297689196766267 := by
  unfold tailWord_99
  simp only [CollatzResearch.WordTrace]
  refine ⟨3610826648814752963351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2407217765876501975567 3610826648814752963351)
  ·
    refine ⟨5416239973222129445027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3610826648814752963351 5416239973222129445027)
    ·
      refine ⟨8124359959833194167541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5416239973222129445027 8124359959833194167541)
      ·
        refine ⟨761658746234361953207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8124359959833194167541 761658746234361953207)
        ·
          refine ⟨1142488119351542929811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 761658746234361953207 1142488119351542929811)
          ·
            refine ⟨1713732179027314394717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1142488119351542929811 1713732179027314394717)
            ·
              refine ⟨642649567135242898019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1713732179027314394717 642649567135242898019)
              ·
                refine ⟨963974350702864347029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 642649567135242898019 963974350702864347029)
                ·
                  refine ⟨45186297689196766267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 963974350702864347029 45186297689196766267)
                  ·
                    rfl

theorem cell20_99_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_99 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99 prefixEnd_99 := by exact prefixLift 99
  have htrace : WordTrace (prefixWord ++ tailWord_99) baseStart_99 baseEnd_99 := by
    simpa [prefixWord, tailWord_99, baseEnd_99] using wordTrace_append hprefix tailTrace_99
  have hstable : (prefixWord ++ tailWord_99).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99).length < 2 ^ (prefixWord ++ tailWord_99).sum := by decide
  have hdescent : baseEnd_99 < baseStart_99 := by decide
  rcases family_descends (prefixWord ++ tailWord_99) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133 : List Nat := [1, 3, 1, 1, 5, 1, 2, 4, 2]
def baseStart_133 : Nat := 118140960795 + 133 * 2 ^ 59
def prefixEnd_133 : Nat := 4983230072969 + 3 ^ 40 * 133 * 2
def baseEnd_133 : Nat := 60704824136189632795

theorem tailTrace_133 : CollatzResearch.WordTrace tailWord_133 prefixEnd_133 60704824136189632795 := by
  unfold tailWord_133
  simp only [CollatzResearch.WordTrace]
  refine ⟨4850908525638559701053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3233939017092373134035 4850908525638559701053)
  ·
    refine ⟨1819090697114459887895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4850908525638559701053 1819090697114459887895)
    ·
      refine ⟨2728636045671689831843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1819090697114459887895 2728636045671689831843)
      ·
        refine ⟨4092954068507534747765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2728636045671689831843 4092954068507534747765)
        ·
          refine ⟨383714443922581382603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4092954068507534747765 383714443922581382603)
          ·
            refine ⟨575571665883872073905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383714443922581382603 575571665883872073905)
            ·
              refine ⟨431678749412904055429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575571665883872073905 431678749412904055429)
              ·
                refine ⟨80939765514919510393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 431678749412904055429 80939765514919510393)
                ·
                  refine ⟨60704824136189632795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80939765514919510393 60704824136189632795)
                  ·
                    rfl

theorem cell20_133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 2].length) (baseStart_133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133 prefixEnd_133 := by exact prefixLift 133
  have htrace : WordTrace (prefixWord ++ tailWord_133) baseStart_133 baseEnd_133 := by
    simpa [prefixWord, tailWord_133, baseEnd_133] using wordTrace_append hprefix tailTrace_133
  have hstable : (prefixWord ++ tailWord_133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133).length < 2 ^ (prefixWord ++ tailWord_133).sum := by decide
  have hdescent : baseEnd_133 < baseStart_133 := by decide
  rcases family_descends (prefixWord ++ tailWord_133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144 : List Nat := [2, 1, 1, 1, 1, 1, 6, 7]
def baseStart_144 : Nat := 118140960795 + 144 * 2 ^ 59
def prefixEnd_144 : Nat := 4983230072969 + 3 ^ 40 * 144 * 2
def baseEnd_144 : Nat := 21908507956346755361

theorem tailTrace_144 : CollatzResearch.WordTrace tailWord_144 prefixEnd_144 21908507956346755361 := by
  unfold tailWord_144
  simp only [CollatzResearch.WordTrace]
  refine ⟨2626055742893719175743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3501407657191625567657 2626055742893719175743)
  ·
    refine ⟨3939083614340578763615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2626055742893719175743 3939083614340578763615)
    ·
      refine ⟨5908625421510868145423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3939083614340578763615 5908625421510868145423)
      ·
        refine ⟨8862938132266302218135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5908625421510868145423 8862938132266302218135)
        ·
          refine ⟨13294407198399453327203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8862938132266302218135 13294407198399453327203)
          ·
            refine ⟨19941610797599179990805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13294407198399453327203 19941610797599179990805)
            ·
              refine ⟨934763006137461562069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19941610797599179990805 934763006137461562069)
              ·
                refine ⟨21908507956346755361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 934763006137461562069 21908507956346755361)
                ·
                  rfl

theorem cell20_144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144 prefixEnd_144 := by exact prefixLift 144
  have htrace : WordTrace (prefixWord ++ tailWord_144) baseStart_144 baseEnd_144 := by
    simpa [prefixWord, tailWord_144, baseEnd_144] using wordTrace_append hprefix tailTrace_144
  have hstable : (prefixWord ++ tailWord_144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144).length < 2 ^ (prefixWord ++ tailWord_144).sum := by decide
  have hdescent : baseEnd_144 < baseStart_144 := by decide
  rcases family_descends (prefixWord ++ tailWord_144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161 : List Nat := [1, 2, 3, 3, 1, 3, 1, 6]
def baseStart_161 : Nat := 118140960795 + 161 * 2 ^ 59
def prefixEnd_161 : Nat := 4983230072969 + 3 ^ 40 * 161 * 2
def baseEnd_161 : Nat := 24494929030845566449

theorem tailTrace_161 : CollatzResearch.WordTrace tailWord_161 prefixEnd_161 24494929030845566449 := by
  unfold tailWord_161
  simp only [CollatzResearch.WordTrace]
  refine ⟨5872152424199341720337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3914768282799561146891 5872152424199341720337)
  ·
    refine ⟨4404114318149506290253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5872152424199341720337 4404114318149506290253)
    ·
      refine ⟨1651542869306064858845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4404114318149506290253 1651542869306064858845)
      ·
        refine ⟨619328575989774322067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1651542869306064858845 619328575989774322067)
        ·
          refine ⟨928992863984661483101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619328575989774322067 928992863984661483101)
          ·
            refine ⟨348372323994248056163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 928992863984661483101 348372323994248056163)
            ·
              refine ⟨522558485991372084245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348372323994248056163 522558485991372084245)
              ·
                refine ⟨24494929030845566449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 522558485991372084245 24494929030845566449)
                ·
                  rfl

theorem cell20_161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 6].length) (baseStart_161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161 prefixEnd_161 := by exact prefixLift 161
  have htrace : WordTrace (prefixWord ++ tailWord_161) baseStart_161 baseEnd_161 := by
    simpa [prefixWord, tailWord_161, baseEnd_161] using wordTrace_append hprefix tailTrace_161
  have hstable : (prefixWord ++ tailWord_161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161).length < 2 ^ (prefixWord ++ tailWord_161).sum := by decide
  have hdescent : baseEnd_161 < baseStart_161 := by decide
  rcases family_descends (prefixWord ++ tailWord_161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167 : List Nat := [1, 1, 6, 2, 2, 2, 1, 3, 2]
def baseStart_167 : Nat := 118140960795 + 167 * 2 ^ 59
def prefixEnd_167 : Nat := 4983230072969 + 3 ^ 40 * 167 * 2
def baseEnd_167 : Nat := 76223350583182499323

theorem tailTrace_167 : CollatzResearch.WordTrace tailWord_167 prefixEnd_167 76223350583182499323 := by
  unfold tailWord_167
  simp only [CollatzResearch.WordTrace]
  refine ⟨6090990402462366438755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4060660268308244292503 6090990402462366438755)
  ·
    refine ⟨9136485603693549658133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6090990402462366438755 9136485603693549658133)
    ·
      refine ⟨428272762673135140225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9136485603693549658133 428272762673135140225)
      ·
        refine ⟨321204572004851355169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428272762673135140225 321204572004851355169)
        ·
          refine ⟨240903429003638516377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321204572004851355169 240903429003638516377)
          ·
            refine ⟨180677571752728887283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240903429003638516377 180677571752728887283)
            ·
              refine ⟨271016357629093330925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180677571752728887283 271016357629093330925)
              ·
                refine ⟨101631134110909999097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 271016357629093330925 101631134110909999097)
                ·
                  refine ⟨76223350583182499323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101631134110909999097 76223350583182499323)
                  ·
                    rfl

theorem cell20_167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 2].length) (baseStart_167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167 prefixEnd_167 := by exact prefixLift 167
  have htrace : WordTrace (prefixWord ++ tailWord_167) baseStart_167 baseEnd_167 := by
    simpa [prefixWord, tailWord_167, baseEnd_167] using wordTrace_append hprefix tailTrace_167
  have hstable : (prefixWord ++ tailWord_167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167).length < 2 ^ (prefixWord ++ tailWord_167).sum := by decide
  have hdescent : baseEnd_167 < baseStart_167 := by decide
  rcases family_descends (prefixWord ++ tailWord_167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174 : List Nat := [4, 1, 4, 2, 2, 1, 6]
def baseStart_174 : Nat := 118140960795 + 174 * 2 ^ 59
def prefixEnd_174 : Nat := 4983230072969 + 3 ^ 40 * 174 * 2
def baseEnd_174 : Nat := 8824260146918807329

theorem tailTrace_174 : CollatzResearch.WordTrace tailWord_174 prefixEnd_174 8824260146918807329 := by
  unfold tailWord_174
  simp only [CollatzResearch.WordTrace]
  refine ⟨793287672137820242947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4230867584735041295717 793287672137820242947)
  ·
    refine ⟨1189931508206730364421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 793287672137820242947 1189931508206730364421)
    ·
      refine ⟨223112157788761943329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1189931508206730364421 223112157788761943329)
      ·
        refine ⟨167334118341571457497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223112157788761943329 167334118341571457497)
        ·
          refine ⟨125500588756178593123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167334118341571457497 125500588756178593123)
          ·
            refine ⟨188250883134267889685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125500588756178593123 188250883134267889685)
            ·
              refine ⟨8824260146918807329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 188250883134267889685 8824260146918807329)
              ·
                rfl

theorem cell20_174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 6].length) (baseStart_174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174 prefixEnd_174 := by exact prefixLift 174
  have htrace : WordTrace (prefixWord ++ tailWord_174) baseStart_174 baseEnd_174 := by
    simpa [prefixWord, tailWord_174, baseEnd_174] using wordTrace_append hprefix tailTrace_174
  have hstable : (prefixWord ++ tailWord_174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174).length < 2 ^ (prefixWord ++ tailWord_174).sum := by decide
  have hdescent : baseEnd_174 < baseStart_174 := by decide
  rcases family_descends (prefixWord ++ tailWord_174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188 : List Nat := [2, 2, 2, 3, 4, 1, 1, 1, 4]
def baseStart_188 : Nat := 118140960795 + 188 * 2 ^ 59
def prefixEnd_188 : Nat := 4983230072969 + 3 ^ 40 * 188 * 2
def baseEnd_188 : Nat := 85808322800442799237

theorem tailTrace_188 : CollatzResearch.WordTrace tailWord_188 prefixEnd_188 85808322800442799237 := by
  unfold tailWord_188
  simp only [CollatzResearch.WordTrace]
  refine ⟨3428461663191476476609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4571282217588635302145 3428461663191476476609)
  ·
    refine ⟨2571346247393607357457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3428461663191476476609 2571346247393607357457)
    ·
      refine ⟨1928509685545205518093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2571346247393607357457 1928509685545205518093)
      ·
        refine ⟨723191132079452069285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1928509685545205518093 723191132079452069285)
        ·
          refine ⟨135598337264897262991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 723191132079452069285 135598337264897262991)
          ·
            refine ⟨203397505897345894487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135598337264897262991 203397505897345894487)
            ·
              refine ⟨305096258846018841731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203397505897345894487 305096258846018841731)
              ·
                refine ⟨457644388269028262597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305096258846018841731 457644388269028262597)
                ·
                  refine ⟨85808322800442799237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 457644388269028262597 85808322800442799237)
                  ·
                    rfl

theorem cell20_188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 4].length) (baseStart_188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188 prefixEnd_188 := by exact prefixLift 188
  have htrace : WordTrace (prefixWord ++ tailWord_188) baseStart_188 baseEnd_188 := by
    simpa [prefixWord, tailWord_188, baseEnd_188] using wordTrace_append hprefix tailTrace_188
  have hstable : (prefixWord ++ tailWord_188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188).length < 2 ^ (prefixWord ++ tailWord_188).sum := by decide
  have hdescent : baseEnd_188 < baseStart_188 := by decide
  rcases family_descends (prefixWord ++ tailWord_188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192 : List Nat := [2, 1, 1, 2, 5, 1, 3, 1, 4]
def baseStart_192 : Nat := 118140960795 + 192 * 2 ^ 59
def prefixEnd_192 : Nat := 4983230072969 + 3 ^ 40 * 192 * 2
def baseEnd_192 : Nat := 87634031794206665887

theorem tailTrace_192 : CollatzResearch.WordTrace tailWord_192 prefixEnd_192 87634031794206665887 := by
  unfold tailWord_192
  simp only [CollatzResearch.WordTrace]
  refine ⟨3501407655945818049415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4668543541261090732553 3501407655945818049415)
  ·
    refine ⟨5252111483918727074123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3501407655945818049415 5252111483918727074123)
    ·
      refine ⟨7878167225878090611185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5252111483918727074123 7878167225878090611185)
      ·
        refine ⟨5908625419408567958389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7878167225878090611185 5908625419408567958389)
        ·
          refine ⟨553933633069553246099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5908625419408567958389 553933633069553246099)
          ·
            refine ⟨830900449604329869149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553933633069553246099 830900449604329869149)
            ·
              refine ⟨311587668601623700931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 830900449604329869149 311587668601623700931)
              ·
                refine ⟨467381502902435551397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311587668601623700931 467381502902435551397)
                ·
                  refine ⟨87634031794206665887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 467381502902435551397 87634031794206665887)
                  ·
                    rfl

theorem cell20_192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192 prefixEnd_192 := by exact prefixLift 192
  have htrace : WordTrace (prefixWord ++ tailWord_192) baseStart_192 baseEnd_192 := by
    simpa [prefixWord, tailWord_192, baseEnd_192] using wordTrace_append hprefix tailTrace_192
  have hstable : (prefixWord ++ tailWord_192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192).length < 2 ^ (prefixWord ++ tailWord_192).sum := by decide
  have hdescent : baseEnd_192 < baseStart_192 := by decide
  rcases family_descends (prefixWord ++ tailWord_192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237 : List Nat := [1, 5, 1, 2, 3, 8]
def baseStart_237 : Nat := 118140960795 + 237 * 2 ^ 59
def prefixEnd_237 : Nat := 4983230072969 + 3 ^ 40 * 237 * 2
def baseEnd_237 : Nat := 4006416962001857989

theorem tailTrace_237 : CollatzResearch.WordTrace tailWord_237 prefixEnd_237 4006416962001857989 := by
  unfold tailWord_237
  simp only [CollatzResearch.WordTrace]
  refine ⟨8644100148864321486965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5762733432576214324643 8644100148864321486965)
  ·
    refine ⟨810384388956030139403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8644100148864321486965 810384388956030139403)
    ·
      refine ⟨1215576583434045209105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 810384388956030139403 1215576583434045209105)
      ·
        refine ⟨911682437575533906829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1215576583434045209105 911682437575533906829)
        ·
          refine ⟨341880914090825215061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 911682437575533906829 341880914090825215061)
          ·
            refine ⟨4006416962001857989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 341880914090825215061 4006416962001857989)
            ·
              rfl

theorem cell20_237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 8].length) (baseStart_237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237 prefixEnd_237 := by exact prefixLift 237
  have htrace : WordTrace (prefixWord ++ tailWord_237) baseStart_237 baseEnd_237 := by
    simpa [prefixWord, tailWord_237, baseEnd_237] using wordTrace_append hprefix tailTrace_237
  have hstable : (prefixWord ++ tailWord_237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237).length < 2 ^ (prefixWord ++ tailWord_237).sum := by decide
  have hdescent : baseEnd_237 < baseStart_237 := by decide
  rcases family_descends (prefixWord ++ tailWord_237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 5]
def baseStart_295 : Nat := 118140960795 + 295 * 2 ^ 59
def prefixEnd_295 : Nat := 4983230072969 + 3 ^ 40 * 295 * 2
def baseEnd_295 : Nat := 134646038383626232133

theorem tailTrace_295 : CollatzResearch.WordTrace tailWord_295 prefixEnd_295 134646038383626232133 := by
  unfold tailWord_295
  simp only [CollatzResearch.WordTrace]
  refine ⟨10759533938740227098339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7173022625826818065559 10759533938740227098339)
  ·
    refine ⟨16139300908110340647509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10759533938740227098339 16139300908110340647509)
    ·
      refine ⟨189132432516918054463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 16139300908110340647509 189132432516918054463)
      ·
        refine ⟨283698648775377081695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189132432516918054463 283698648775377081695)
        ·
          refine ⟨425547973163065622543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283698648775377081695 425547973163065622543)
          ·
            refine ⟨638321959744598433815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425547973163065622543 638321959744598433815)
            ·
              refine ⟨957482939616897650723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 638321959744598433815 957482939616897650723)
              ·
                refine ⟨1436224409425346476085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 957482939616897650723 1436224409425346476085)
                ·
                  refine ⟨134646038383626232133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1436224409425346476085 134646038383626232133)
                  ·
                    rfl

theorem cell20_295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 5].length) (baseStart_295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295 prefixEnd_295 := by exact prefixLift 295
  have htrace : WordTrace (prefixWord ++ tailWord_295) baseStart_295 baseEnd_295 := by
    simpa [prefixWord, tailWord_295, baseEnd_295] using wordTrace_append hprefix tailTrace_295
  have hstable : (prefixWord ++ tailWord_295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295).length < 2 ^ (prefixWord ++ tailWord_295).sum := by decide
  have hdescent : baseEnd_295 < baseStart_295 := by decide
  rcases family_descends (prefixWord ++ tailWord_295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302 : List Nat := [4, 1, 3, 3, 1, 1, 2, 1, 4]
def baseStart_302 : Nat := 118140960795 + 302 * 2 ^ 59
def prefixEnd_302 : Nat := 4983230072969 + 3 ^ 40 * 302 * 2
def baseEnd_302 : Nat := 137841029122712998771

theorem tailTrace_302 : CollatzResearch.WordTrace tailWord_302 prefixEnd_302 137841029122712998771 := by
  unfold tailWord_302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1376855614172552825395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7343229942253615068773 1376855614172552825395)
  ·
    refine ⟨2065283421258829238093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1376855614172552825395 2065283421258829238093)
    ·
      refine ⟨774481282972060964285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2065283421258829238093 774481282972060964285)
      ·
        refine ⟨290430481114522861607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 774481282972060964285 290430481114522861607)
        ·
          refine ⟨435645721671784292411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290430481114522861607 435645721671784292411)
          ·
            refine ⟨653468582507676438617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435645721671784292411 653468582507676438617)
            ·
              refine ⟨490101436880757328963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 653468582507676438617 490101436880757328963)
              ·
                refine ⟨735152155321135993445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 490101436880757328963 735152155321135993445)
                ·
                  refine ⟨137841029122712998771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 735152155321135993445 137841029122712998771)
                  ·
                    rfl

theorem cell20_302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302 prefixEnd_302 := by exact prefixLift 302
  have htrace : WordTrace (prefixWord ++ tailWord_302) baseStart_302 baseEnd_302 := by
    simpa [prefixWord, tailWord_302, baseEnd_302] using wordTrace_append hprefix tailTrace_302
  have hstable : (prefixWord ++ tailWord_302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302).length < 2 ^ (prefixWord ++ tailWord_302).sum := by decide
  have hdescent : baseEnd_302 < baseStart_302 := by decide
  rcases family_descends (prefixWord ++ tailWord_302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327 : List Nat := [1, 1, 4, 1, 2, 2, 1, 4, 4]
def baseStart_327 : Nat := 118140960795 + 327 * 2 ^ 59
def prefixEnd_327 : Nat := 4983230072969 + 3 ^ 40 * 327 * 2
def baseEnd_327 : Nat := 149251710333737165335

theorem tailTrace_327 : CollatzResearch.WordTrace tailWord_327 prefixEnd_327 149251710333737165335 := by
  unfold tailWord_327
  simp only [CollatzResearch.WordTrace]
  refine ⟨11926669822809692263235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7951113215206461508823 11926669822809692263235)
  ·
    refine ⟨17890004734214538394853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11926669822809692263235 17890004734214538394853)
    ·
      refine ⟨3354375887665225949035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17890004734214538394853 3354375887665225949035)
      ·
        refine ⟨5031563831497838923553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3354375887665225949035 5031563831497838923553)
        ·
          refine ⟨3773672873623379192665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5031563831497838923553 3773672873623379192665)
          ·
            refine ⟨2830254655217534394499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3773672873623379192665 2830254655217534394499)
            ·
              refine ⟨4245381982826301591749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2830254655217534394499 4245381982826301591749)
              ·
                refine ⟨796009121779931548453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4245381982826301591749 796009121779931548453)
                ·
                  refine ⟨149251710333737165335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 796009121779931548453 149251710333737165335)
                  ·
                    rfl

theorem cell20_327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 4].length) (baseStart_327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327 prefixEnd_327 := by exact prefixLift 327
  have htrace : WordTrace (prefixWord ++ tailWord_327) baseStart_327 baseEnd_327 := by
    simpa [prefixWord, tailWord_327, baseEnd_327] using wordTrace_append hprefix tailTrace_327
  have hstable : (prefixWord ++ tailWord_327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327).length < 2 ^ (prefixWord ++ tailWord_327).sum := by decide
  have hdescent : baseEnd_327 < baseStart_327 := by decide
  rcases family_descends (prefixWord ++ tailWord_327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340 : List Nat := [2, 4, 1, 1, 2, 4, 1, 3, 2]
def baseStart_340 : Nat := 118140960795 + 340 * 2 ^ 59
def prefixEnd_340 : Nat := 4983230072969 + 3 ^ 40 * 340 * 2
def baseEnd_340 : Nat := 155185264563469731949

theorem tailTrace_340 : CollatzResearch.WordTrace tailWord_340 prefixEnd_340 155185264563469731949 := by
  unfold tailWord_340
  simp only [CollatzResearch.WordTrace]
  refine ⟨6200409387856456243237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8267212517141941657649 6200409387856456243237)
  ·
    refine ⟨1162576760223085545607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6200409387856456243237 1162576760223085545607)
    ·
      refine ⟨1743865140334628318411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1162576760223085545607 1743865140334628318411)
      ·
        refine ⟨2615797710501942477617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1743865140334628318411 2615797710501942477617)
        ·
          refine ⟨1961848282876456858213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2615797710501942477617 1961848282876456858213)
          ·
            refine ⟨367846553039335660915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1961848282876456858213 367846553039335660915)
            ·
              refine ⟨551769829559003491373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367846553039335660915 551769829559003491373)
              ·
                refine ⟨206913686084626309265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 551769829559003491373 206913686084626309265)
                ·
                  refine ⟨155185264563469731949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206913686084626309265 155185264563469731949)
                  ·
                    rfl

theorem cell20_340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_340 prefixEnd_340 := by exact prefixLift 340
  have htrace : WordTrace (prefixWord ++ tailWord_340) baseStart_340 baseEnd_340 := by
    simpa [prefixWord, tailWord_340, baseEnd_340] using wordTrace_append hprefix tailTrace_340
  have hstable : (prefixWord ++ tailWord_340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340).length < 2 ^ (prefixWord ++ tailWord_340).sum := by decide
  have hdescent : baseEnd_340 < baseStart_340 := by decide
  rcases family_descends (prefixWord ++ tailWord_340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344 : List Nat := [2, 1, 2, 2, 1, 1, 2, 7, 2]
def baseStart_344 : Nat := 118140960795 + 344 * 2 ^ 59
def prefixEnd_344 : Nat := 4983230072969 + 3 ^ 40 * 344 * 2
def baseEnd_344 : Nat := 157010973557233598599

theorem tailTrace_344 : CollatzResearch.WordTrace tailWord_344 prefixEnd_344 157010973557233598599 := by
  unfold tailWord_344
  simp only [CollatzResearch.WordTrace]
  refine ⟨6273355380610797816043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8364473840814397088057 6273355380610797816043)
  ·
    refine ⟨9410033070916196724065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6273355380610797816043 9410033070916196724065)
    ·
      refine ⟨7057524803187147543049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9410033070916196724065 7057524803187147543049)
      ·
        refine ⟨5293143602390360657287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7057524803187147543049 5293143602390360657287)
        ·
          refine ⟨7939715403585540985931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5293143602390360657287 7939715403585540985931)
          ·
            refine ⟨11909573105378311478897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7939715403585540985931 11909573105378311478897)
            ·
              refine ⟨8932179829033733609173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11909573105378311478897 8932179829033733609173)
              ·
                refine ⟨209347964742978131465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 8932179829033733609173 209347964742978131465)
                ·
                  refine ⟨157010973557233598599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209347964742978131465 157010973557233598599)
                  ·
                    rfl

theorem cell20_344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 2].length) (baseStart_344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_344 prefixEnd_344 := by exact prefixLift 344
  have htrace : WordTrace (prefixWord ++ tailWord_344) baseStart_344 baseEnd_344 := by
    simpa [prefixWord, tailWord_344, baseEnd_344] using wordTrace_append hprefix tailTrace_344
  have hstable : (prefixWord ++ tailWord_344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344).length < 2 ^ (prefixWord ++ tailWord_344).sum := by decide
  have hdescent : baseEnd_344 < baseStart_344 := by decide
  rcases family_descends (prefixWord ++ tailWord_344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361 : List Nat := [1, 2, 1, 1, 1, 3, 7, 2, 2]
def baseStart_361 : Nat := 118140960795 + 361 * 2 ^ 59
def prefixEnd_361 : Nat := 4983230072969 + 3 ^ 40 * 361 * 2
def baseEnd_361 : Nat := 164770236780730031863

theorem tailTrace_361 : CollatzResearch.WordTrace tailWord_361 prefixEnd_361 164770236780730031863 := by
  unfold tailWord_361
  simp only [CollatzResearch.WordTrace]
  refine ⟨13166751699633499000937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8777834466422332667291 13166751699633499000937)
  ·
    refine ⟨9875063774725124250703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13166751699633499000937 9875063774725124250703)
    ·
      refine ⟨14812595662087686376055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9875063774725124250703 14812595662087686376055)
      ·
        refine ⟨22218893493131529564083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14812595662087686376055 22218893493131529564083)
        ·
          refine ⟨33328340239697294346125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22218893493131529564083 33328340239697294346125)
          ·
            refine ⟨12498127589886485379797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33328340239697294346125 12498127589886485379797)
            ·
              refine ⟨292924865387964501089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12498127589886485379797 292924865387964501089)
              ·
                refine ⟨219693649040973375817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292924865387964501089 219693649040973375817)
                ·
                  refine ⟨164770236780730031863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219693649040973375817 164770236780730031863)
                  ·
                    rfl

theorem cell20_361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 2].length) (baseStart_361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361 prefixEnd_361 := by exact prefixLift 361
  have htrace : WordTrace (prefixWord ++ tailWord_361) baseStart_361 baseEnd_361 := by
    simpa [prefixWord, tailWord_361, baseEnd_361] using wordTrace_append hprefix tailTrace_361
  have hstable : (prefixWord ++ tailWord_361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361).length < 2 ^ (prefixWord ++ tailWord_361).sum := by decide
  have hdescent : baseEnd_361 < baseStart_361 := by decide
  rcases family_descends (prefixWord ++ tailWord_361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410 : List Nat := [3, 1, 1, 4, 1, 10]
def baseStart_410 : Nat := 118140960795 + 410 * 2 ^ 59
def prefixEnd_410 : Nat := 4983230072969 + 3 ^ 40 * 410 * 2
def baseEnd_410 : Nat := 6930932294605088827

theorem tailTrace_410 : CollatzResearch.WordTrace tailWord_410 prefixEnd_410 6930932294605088827 := by
  unfold tailWord_410
  simp only [CollatzResearch.WordTrace]
  refine ⟨3738482130528716883671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9969285681409911689789 3738482130528716883671)
  ·
    refine ⟨5607723195793075325507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3738482130528716883671 5607723195793075325507)
    ·
      refine ⟨8411584793689612988261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5607723195793075325507 8411584793689612988261)
      ·
        refine ⟨1577172148816802435299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8411584793689612988261 1577172148816802435299)
        ·
          refine ⟨2365758223225203652949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1577172148816802435299 2365758223225203652949)
          ·
            refine ⟨6930932294605088827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2365758223225203652949 6930932294605088827)
            ·
              rfl

theorem cell20_410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 10].length) (baseStart_410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410 prefixEnd_410 := by exact prefixLift 410
  have htrace : WordTrace (prefixWord ++ tailWord_410) baseStart_410 baseEnd_410 := by
    simpa [prefixWord, tailWord_410, baseEnd_410] using wordTrace_append hprefix tailTrace_410
  have hstable : (prefixWord ++ tailWord_410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410).length < 2 ^ (prefixWord ++ tailWord_410).sum := by decide
  have hdescent : baseEnd_410 < baseStart_410 := by decide
  rcases family_descends (prefixWord ++ tailWord_410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416 : List Nat := [2, 1, 1, 4, 1, 5, 2, 2, 2]
def baseStart_416 : Nat := 118140960795 + 416 * 2 ^ 59
def prefixEnd_416 : Nat := 4983230072969 + 3 ^ 40 * 416 * 2
def baseEnd_416 : Nat := 189873735444983198305

theorem tailTrace_416 : CollatzResearch.WordTrace tailWord_416 prefixEnd_416 189873735444983198305 := by
  unfold tailWord_416
  simp only [CollatzResearch.WordTrace]
  refine ⟨7586383250188946126551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10115177666918594835401 7586383250188946126551)
  ·
    refine ⟨11379574875283419189827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7586383250188946126551 11379574875283419189827)
    ·
      refine ⟨17069362312925128784741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11379574875283419189827 17069362312925128784741)
      ·
        refine ⟨3200505433673461647139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17069362312925128784741 3200505433673461647139)
        ·
          refine ⟨4800758150510192470709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3200505433673461647139 4800758150510192470709)
          ·
            refine ⟨450071076610330544129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4800758150510192470709 450071076610330544129)
            ·
              refine ⟨337553307457747908097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450071076610330544129 337553307457747908097)
              ·
                refine ⟨253164980593310931073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337553307457747908097 253164980593310931073)
                ·
                  refine ⟨189873735444983198305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253164980593310931073 189873735444983198305)
                  ·
                    rfl

theorem cell20_416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 2].length) (baseStart_416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416 prefixEnd_416 := by exact prefixLift 416
  have htrace : WordTrace (prefixWord ++ tailWord_416) baseStart_416 baseEnd_416 := by
    simpa [prefixWord, tailWord_416, baseEnd_416] using wordTrace_append hprefix tailTrace_416
  have hstable : (prefixWord ++ tailWord_416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416).length < 2 ^ (prefixWord ++ tailWord_416).sum := by decide
  have hdescent : baseEnd_416 < baseStart_416 := by decide
  rcases family_descends (prefixWord ++ tailWord_416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434 : List Nat := [3, 2, 1, 1, 1, 1, 3, 5, 3]
def baseStart_434 : Nat := 118140960795 + 434 * 2 ^ 59
def prefixEnd_434 : Nat := 4983230072969 + 3 ^ 40 * 434 * 2
def baseEnd_434 : Nat := 198089425916920598231

theorem tailTrace_434 : CollatzResearch.WordTrace tailWord_434 prefixEnd_434 198089425916920598231 := by
  unfold tailWord_434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3957320108791741602089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10552853623444644272237 3957320108791741602089)
  ·
    refine ⟨2967990081593806201567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3957320108791741602089 2967990081593806201567)
    ·
      refine ⟨4451985122390709302351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2967990081593806201567 4451985122390709302351)
      ·
        refine ⟨6677977683586063953527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4451985122390709302351 6677977683586063953527)
        ·
          refine ⟨10016966525379095930291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6677977683586063953527 10016966525379095930291)
          ·
            refine ⟨15025449788068643895437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10016966525379095930291 15025449788068643895437)
            ·
              refine ⟨5634543670525741460789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15025449788068643895437 5634543670525741460789)
              ·
                refine ⟨528238469111788261949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5634543670525741460789 528238469111788261949)
                ·
                  refine ⟨198089425916920598231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 528238469111788261949 198089425916920598231)
                  ·
                    rfl

theorem cell20_434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434 prefixEnd_434 := by exact prefixLift 434
  have htrace : WordTrace (prefixWord ++ tailWord_434) baseStart_434 baseEnd_434 := by
    simpa [prefixWord, tailWord_434, baseEnd_434] using wordTrace_append hprefix tailTrace_434
  have hstable : (prefixWord ++ tailWord_434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434).length < 2 ^ (prefixWord ++ tailWord_434).sum := by decide
  have hdescent : baseEnd_434 < baseStart_434 := by decide
  rcases family_descends (prefixWord ++ tailWord_434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 6]
def baseStart_441 : Nat := 118140960795 + 441 * 2 ^ 59
def prefixEnd_441 : Nat := 4983230072969 + 3 ^ 40 * 441 * 2
def baseEnd_441 : Nat := 201284416656007364869

theorem tailTrace_441 : CollatzResearch.WordTrace tailWord_441 prefixEnd_441 201284416656007364869 := by
  unfold tailWord_441
  simp only [CollatzResearch.WordTrace]
  refine ⟨16084591409807161913177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10723060939871441275451 16084591409807161913177)
  ·
    refine ⟨12063443557355371434883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16084591409807161913177 12063443557355371434883)
    ·
      refine ⟨18095165336033057152325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12063443557355371434883 18095165336033057152325)
      ·
        refine ⟨3392843500506198216061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18095165336033057152325 3392843500506198216061)
        ·
          refine ⟨1272316312689824331023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3392843500506198216061 1272316312689824331023)
          ·
            refine ⟨1908474469034736496535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1272316312689824331023 1908474469034736496535)
            ·
              refine ⟨2862711703552104744803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1908474469034736496535 2862711703552104744803)
              ·
                refine ⟨4294067555328157117205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2862711703552104744803 4294067555328157117205)
                ·
                  refine ⟨201284416656007364869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4294067555328157117205 201284416656007364869)
                  ·
                    rfl

theorem cell20_441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441 prefixEnd_441 := by exact prefixLift 441
  have htrace : WordTrace (prefixWord ++ tailWord_441) baseStart_441 baseEnd_441 := by
    simpa [prefixWord, tailWord_441, baseEnd_441] using wordTrace_append hprefix tailTrace_441
  have hstable : (prefixWord ++ tailWord_441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441).length < 2 ^ (prefixWord ++ tailWord_441).sum := by decide
  have hdescent : baseEnd_441 < baseStart_441 := by decide
  rcases family_descends (prefixWord ++ tailWord_441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444 : List Nat := [2, 2, 2, 4, 1, 2, 3, 4]
def baseStart_444 : Nat := 118140960795 + 444 * 2 ^ 59
def prefixEnd_444 : Nat := 4983230072969 + 3 ^ 40 * 444 * 2
def baseEnd_444 : Nat := 67551232800443421619

theorem tailTrace_444 : CollatzResearch.WordTrace tailWord_444 prefixEnd_444 67551232800443421619 := by
  unfold tailWord_444
  simp only [CollatzResearch.WordTrace]
  refine ⟨8097005199469337136193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10796006932625782848257 8097005199469337136193)
  ·
    refine ⟨6072753899602002852145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8097005199469337136193 6072753899602002852145)
    ·
      refine ⟨4554565424701502139109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6072753899602002852145 4554565424701502139109)
      ·
        refine ⟨853981017131531651083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4554565424701502139109 853981017131531651083)
        ·
          refine ⟨1280971525697297476625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 853981017131531651083 1280971525697297476625)
          ·
            refine ⟨960728644272973107469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1280971525697297476625 960728644272973107469)
            ·
              refine ⟨360273241602364915301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 960728644272973107469 360273241602364915301)
              ·
                refine ⟨67551232800443421619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 360273241602364915301 67551232800443421619)
                ·
                  rfl

theorem cell20_444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 4].length) (baseStart_444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444 prefixEnd_444 := by exact prefixLift 444
  have htrace : WordTrace (prefixWord ++ tailWord_444) baseStart_444 baseEnd_444 := by
    simpa [prefixWord, tailWord_444, baseEnd_444] using wordTrace_append hprefix tailTrace_444
  have hstable : (prefixWord ++ tailWord_444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444).length < 2 ^ (prefixWord ++ tailWord_444).sum := by decide
  have hdescent : baseEnd_444 < baseStart_444 := by decide
  rcases family_descends (prefixWord ++ tailWord_444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468 : List Nat := [2, 4, 1, 2, 2, 3, 1, 2, 3]
def baseStart_468 : Nat := 118140960795 + 468 * 2 ^ 59
def prefixEnd_468 : Nat := 4983230072969 + 3 ^ 40 * 468 * 2
def baseEnd_468 : Nat := 213607952363913464759

theorem tailTrace_468 : CollatzResearch.WordTrace tailWord_468 prefixEnd_468 213607952363913464759 := by
  unfold tailWord_468
  simp only [CollatzResearch.WordTrace]
  refine ⟨8534681155995386573029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11379574874660515430705 8534681155995386573029)
  ·
    refine ⟨1600252716749134982443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8534681155995386573029 1600252716749134982443)
    ·
      refine ⟨2400379075123702473665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1600252716749134982443 2400379075123702473665)
      ·
        refine ⟨1800284306342776855249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2400379075123702473665 1800284306342776855249)
        ·
          refine ⟨1350213229757082641437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1800284306342776855249 1350213229757082641437)
          ·
            refine ⟨506329961158905990539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1350213229757082641437 506329961158905990539)
            ·
              refine ⟨759494941738358985809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506329961158905990539 759494941738358985809)
              ·
                refine ⟨569621206303769239357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759494941738358985809 569621206303769239357)
                ·
                  refine ⟨213607952363913464759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 569621206303769239357 213607952363913464759)
                  ·
                    rfl

theorem cell20_468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468 prefixEnd_468 := by exact prefixLift 468
  have htrace : WordTrace (prefixWord ++ tailWord_468) baseStart_468 baseEnd_468 := by
    simpa [prefixWord, tailWord_468, baseEnd_468] using wordTrace_append hprefix tailTrace_468
  have hstable : (prefixWord ++ tailWord_468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468).length < 2 ^ (prefixWord ++ tailWord_468).sum := by decide
  have hdescent : baseEnd_468 < baseStart_468 := by decide
  rcases family_descends (prefixWord ++ tailWord_468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479 : List Nat := [1, 1, 2, 3, 3, 2, 1, 3, 4]
def baseStart_479 : Nat := 118140960795 + 479 * 2 ^ 59
def prefixEnd_479 : Nat := 4983230072969 + 3 ^ 40 * 479 * 2
def baseEnd_479 : Nat := 218628652096764098047

theorem tailTrace_479 : CollatzResearch.WordTrace tailWord_479 prefixEnd_479 218628652096764098047 := by
  unfold tailWord_479
  simp only [CollatzResearch.WordTrace]
  refine ⟨17470565272139651796491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11647043514759767864327 17470565272139651796491)
  ·
    refine ⟨26205847908209477694737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17470565272139651796491 26205847908209477694737)
    ·
      refine ⟨19654385931157108271053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26205847908209477694737 19654385931157108271053)
      ·
        refine ⟨7370394724183915601645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19654385931157108271053 7370394724183915601645)
        ·
          refine ⟨2763898021568968350617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7370394724183915601645 2763898021568968350617)
          ·
            refine ⟨2072923516176726262963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2763898021568968350617 2072923516176726262963)
            ·
              refine ⟨3109385274265089394445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2072923516176726262963 3109385274265089394445)
              ·
                refine ⟨1166019477849408522917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3109385274265089394445 1166019477849408522917)
                ·
                  refine ⟨218628652096764098047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1166019477849408522917 218628652096764098047)
                  ·
                    rfl

theorem cell20_479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 4].length) (baseStart_479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479 prefixEnd_479 := by exact prefixLift 479
  have htrace : WordTrace (prefixWord ++ tailWord_479) baseStart_479 baseEnd_479 := by
    simpa [prefixWord, tailWord_479, baseEnd_479] using wordTrace_append hprefix tailTrace_479
  have hstable : (prefixWord ++ tailWord_479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479).length < 2 ^ (prefixWord ++ tailWord_479).sum := by decide
  have hdescent : baseEnd_479 < baseStart_479 := by decide
  rcases family_descends (prefixWord ++ tailWord_479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513 : List Nat := [1, 2, 4, 1, 3, 1, 3, 3, 2]
def baseStart_513 : Nat := 118140960795 + 513 * 2 ^ 59
def prefixEnd_513 : Nat := 4983230072969 + 3 ^ 40 * 513 * 2
def baseEnd_513 : Nat := 234147178543756964575

theorem tailTrace_513 : CollatzResearch.WordTrace tailWord_513 prefixEnd_513 234147178543756964575 := by
  unfold tailWord_513
  simp only [CollatzResearch.WordTrace]
  refine ⟨18710647148963458534193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12473764765975639022795 18710647148963458534193)
  ·
    refine ⟨14032985361722593900645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18710647148963458534193 14032985361722593900645)
    ·
      refine ⟨2631184755322986356371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14032985361722593900645 2631184755322986356371)
      ·
        refine ⟨3946777132984479534557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2631184755322986356371 3946777132984479534557)
        ·
          refine ⟨1480041424869179825459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3946777132984479534557 1480041424869179825459)
          ·
            refine ⟨2220062137303769738189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480041424869179825459 2220062137303769738189)
            ·
              refine ⟨832523301488913651821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2220062137303769738189 832523301488913651821)
              ·
                refine ⟨312196238058342619433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 832523301488913651821 312196238058342619433)
                ·
                  refine ⟨234147178543756964575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312196238058342619433 234147178543756964575)
                  ·
                    rfl

theorem cell20_513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 2].length) (baseStart_513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_513 prefixEnd_513 := by exact prefixLift 513
  have htrace : WordTrace (prefixWord ++ tailWord_513) baseStart_513 baseEnd_513 := by
    simpa [prefixWord, tailWord_513, baseEnd_513] using wordTrace_append hprefix tailTrace_513
  have hstable : (prefixWord ++ tailWord_513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513).length < 2 ^ (prefixWord ++ tailWord_513).sum := by decide
  have hdescent : baseEnd_513 < baseStart_513 := by decide
  rcases family_descends (prefixWord ++ tailWord_513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524 : List Nat := [2, 2, 1, 2, 4, 1, 8]
def baseStart_524 : Nat := 118140960795 + 524 * 2 ^ 59
def prefixEnd_524 : Nat := 4983230072969 + 3 ^ 40 * 524 * 2
def baseEnd_524 : Nat := 26574208697400844207

theorem tailTrace_524 : CollatzResearch.WordTrace tailWord_524 prefixEnd_524 26574208697400844207 := by
  unfold tailWord_524
  simp only [CollatzResearch.WordTrace]
  refine ⟨9555925054556168592313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12741233406074891456417 9555925054556168592313)
  ·
    refine ⟨7166943790917126444235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9555925054556168592313 7166943790917126444235)
    ·
      refine ⟨10750415686375689666353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7166943790917126444235 10750415686375689666353)
      ·
        refine ⟨8062811764781767249765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10750415686375689666353 8062811764781767249765)
        ·
          refine ⟨1511777205896581359331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8062811764781767249765 1511777205896581359331)
          ·
            refine ⟨2267665808844872038997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1511777205896581359331 2267665808844872038997)
            ·
              refine ⟨26574208697400844207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2267665808844872038997 26574208697400844207)
              ·
                rfl

theorem cell20_524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 8].length) (baseStart_524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524 prefixEnd_524 := by exact prefixLift 524
  have htrace : WordTrace (prefixWord ++ tailWord_524) baseStart_524 baseEnd_524 := by
    simpa [prefixWord, tailWord_524, baseEnd_524] using wordTrace_append hprefix tailTrace_524
  have hstable : (prefixWord ++ tailWord_524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524).length < 2 ^ (prefixWord ++ tailWord_524).sum := by decide
  have hdescent : baseEnd_524 < baseStart_524 := by decide
  rcases family_descends (prefixWord ++ tailWord_524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 5]
def baseStart_531 : Nat := 118140960795 + 531 * 2 ^ 59
def prefixEnd_531 : Nat := 4983230072969 + 3 ^ 40 * 531 * 2
def baseEnd_531 : Nat := 242362869015694364501

theorem tailTrace_531 : CollatzResearch.WordTrace tailWord_531 prefixEnd_531 242362869015694364501 := by
  unfold tailWord_531
  simp only [CollatzResearch.WordTrace]
  refine ⟨19367161083752532689447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12911440722501688459631 19367161083752532689447)
  ·
    refine ⟨29050741625628799034171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19367161083752532689447 29050741625628799034171)
    ·
      refine ⟨43576112438443198551257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29050741625628799034171 43576112438443198551257)
      ·
        refine ⟨32682084328832398913443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43576112438443198551257 32682084328832398913443)
        ·
          refine ⟨49023126493248598370165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32682084328832398913443 49023126493248598370165)
          ·
            refine ⟨4595918108742056097203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49023126493248598370165 4595918108742056097203)
            ·
              refine ⟨6893877163113084145805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4595918108742056097203 6893877163113084145805)
              ·
                refine ⟨2585203936167406554677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6893877163113084145805 2585203936167406554677)
                ·
                  refine ⟨242362869015694364501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2585203936167406554677 242362869015694364501)
                  ·
                    rfl

theorem cell20_531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531 prefixEnd_531 := by exact prefixLift 531
  have htrace : WordTrace (prefixWord ++ tailWord_531) baseStart_531 baseEnd_531 := by
    simpa [prefixWord, tailWord_531, baseEnd_531] using wordTrace_append hprefix tailTrace_531
  have hstable : (prefixWord ++ tailWord_531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531).length < 2 ^ (prefixWord ++ tailWord_531).sum := by decide
  have hdescent : baseEnd_531 < baseStart_531 := by decide
  rcases family_descends (prefixWord ++ tailWord_531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541 : List Nat := [1, 4, 2, 2, 1, 3, 2, 5]
def baseStart_541 : Nat := 118140960795 + 541 * 2 ^ 59
def prefixEnd_541 : Nat := 4983230072969 + 3 ^ 40 * 541 * 2
def baseEnd_541 : Nat := 82309047166701343709

theorem tailTrace_541 : CollatzResearch.WordTrace tailWord_541 prefixEnd_541 82309047166701343709 := by
  unfold tailWord_541
  simp only [CollatzResearch.WordTrace]
  refine ⟨19731891047524240553477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13154594031682827035651 19731891047524240553477)
  ·
    refine ⟨3699729571410795103777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19731891047524240553477 3699729571410795103777)
    ·
      refine ⟨2774797178558096327833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3699729571410795103777 2774797178558096327833)
      ·
        refine ⟨2081097883918572245875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2774797178558096327833 2081097883918572245875)
        ·
          refine ⟨3121646825877858368813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2081097883918572245875 3121646825877858368813)
          ·
            refine ⟨1170617559704196888305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3121646825877858368813 1170617559704196888305)
            ·
              refine ⟨877963169778147666229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1170617559704196888305 877963169778147666229)
              ·
                refine ⟨82309047166701343709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 877963169778147666229 82309047166701343709)
                ·
                  rfl

theorem cell20_541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 5].length) (baseStart_541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541 prefixEnd_541 := by exact prefixLift 541
  have htrace : WordTrace (prefixWord ++ tailWord_541) baseStart_541 baseEnd_541 := by
    simpa [prefixWord, tailWord_541, baseEnd_541] using wordTrace_append hprefix tailTrace_541
  have hstable : (prefixWord ++ tailWord_541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541).length < 2 ^ (prefixWord ++ tailWord_541).sum := by decide
  have hdescent : baseEnd_541 < baseStart_541 := by decide
  rcases family_descends (prefixWord ++ tailWord_541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562 : List Nat := [3, 2, 1, 1, 2, 1, 4, 6]
def baseStart_562 : Nat := 118140960795 + 562 * 2 ^ 59
def prefixEnd_562 : Nat := 4983230072969 + 3 ^ 40 * 562 * 2
def baseEnd_562 : Nat := 85504037905788110347

theorem tailTrace_562 : CollatzResearch.WordTrace tailWord_562 prefixEnd_562 85504037905788110347 := by
  unfold tailWord_562
  simp only [CollatzResearch.WordTrace]
  refine ⟨5124455992861206766985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13665215980963218045293 5124455992861206766985)
  ·
    refine ⟨3843341994645905075239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5124455992861206766985 3843341994645905075239)
    ·
      refine ⟨5765012991968857612859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3843341994645905075239 5765012991968857612859)
      ·
        refine ⟨8647519487953286419289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5765012991968857612859 8647519487953286419289)
        ·
          refine ⟨6485639615964964814467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8647519487953286419289 6485639615964964814467)
          ·
            refine ⟨9728459423947447221701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6485639615964964814467 9728459423947447221701)
            ·
              refine ⟨1824086141990146354069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9728459423947447221701 1824086141990146354069)
              ·
                refine ⟨85504037905788110347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1824086141990146354069 85504037905788110347)
                ·
                  rfl

theorem cell20_562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562 prefixEnd_562 := by exact prefixLift 562
  have htrace : WordTrace (prefixWord ++ tailWord_562) baseStart_562 baseEnd_562 := by
    simpa [prefixWord, tailWord_562, baseEnd_562] using wordTrace_append hprefix tailTrace_562
  have hstable : (prefixWord ++ tailWord_562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562).length < 2 ^ (prefixWord ++ tailWord_562).sum := by decide
  have hdescent : baseEnd_562 < baseStart_562 := by decide
  rcases family_descends (prefixWord ++ tailWord_562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582 : List Nat := [6, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_582 : Nat := 118140960795 + 582 * 2 ^ 59
def prefixEnd_582 : Nat := 4983230072969 + 3 ^ 40 * 582 * 2
def baseEnd_582 : Nat := 265640658686183664293

theorem tailTrace_582 : CollatzResearch.WordTrace tailWord_582 prefixEnd_582 265640658686183664293 := by
  unfold tailWord_582
  simp only [CollatzResearch.WordTrace]
  refine ⟨663352621843382587375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14151522599325495197333 663352621843382587375)
  ·
    refine ⟨995028932765073881063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 663352621843382587375 995028932765073881063)
    ·
      refine ⟨1492543399147610821595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 995028932765073881063 1492543399147610821595)
      ·
        refine ⟨2238815098721416232393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1492543399147610821595 2238815098721416232393)
        ·
          refine ⟨1679111324041062174295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2238815098721416232393 1679111324041062174295)
          ·
            refine ⟨2518666986061593261443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1679111324041062174295 2518666986061593261443)
            ·
              refine ⟨3778000479092389892165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2518666986061593261443 3778000479092389892165)
              ·
                refine ⟨708375089829823104781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3778000479092389892165 708375089829823104781)
                ·
                  refine ⟨265640658686183664293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 708375089829823104781 265640658686183664293)
                  ·
                    rfl

theorem cell20_582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582 prefixEnd_582 := by exact prefixLift 582
  have htrace : WordTrace (prefixWord ++ tailWord_582) baseStart_582 baseEnd_582 := by
    simpa [prefixWord, tailWord_582, baseEnd_582] using wordTrace_append hprefix tailTrace_582
  have hstable : (prefixWord ++ tailWord_582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582).length < 2 ^ (prefixWord ++ tailWord_582).sum := by decide
  have hdescent : baseEnd_582 < baseStart_582 := by decide
  rcases family_descends (prefixWord ++ tailWord_582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586 : List Nat := [3, 1, 2, 1, 1, 4, 1, 4, 3]
def baseStart_586 : Nat := 118140960795 + 586 * 2 ^ 59
def prefixEnd_586 : Nat := 4983230072969 + 3 ^ 40 * 586 * 2
def baseEnd_586 : Nat := 267466367679947530943

theorem tailTrace_586 : CollatzResearch.WordTrace tailWord_586 prefixEnd_586 267466367679947530943 := by
  unfold tailWord_586
  simp only [CollatzResearch.WordTrace]
  refine ⟨5343293971124231485403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14248783922997950627741 5343293971124231485403)
  ·
    refine ⟨8014940956686347228105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5343293971124231485403 8014940956686347228105)
    ·
      refine ⟨6011205717514760421079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8014940956686347228105 6011205717514760421079)
      ·
        refine ⟨9016808576272140631619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6011205717514760421079 9016808576272140631619)
        ·
          refine ⟨13525212864408210947429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9016808576272140631619 13525212864408210947429)
          ·
            refine ⟨2535977412076539552643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13525212864408210947429 2535977412076539552643)
            ·
              refine ⟨3803966118114809328965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2535977412076539552643 3803966118114809328965)
              ·
                refine ⟨713243647146526749181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3803966118114809328965 713243647146526749181)
                ·
                  refine ⟨267466367679947530943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 713243647146526749181 267466367679947530943)
                  ·
                    rfl

theorem cell20_586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586 prefixEnd_586 := by exact prefixLift 586
  have htrace : WordTrace (prefixWord ++ tailWord_586) baseStart_586 baseEnd_586 := by
    simpa [prefixWord, tailWord_586, baseEnd_586] using wordTrace_append hprefix tailTrace_586
  have hstable : (prefixWord ++ tailWord_586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586).length < 2 ^ (prefixWord ++ tailWord_586).sum := by decide
  have hdescent : baseEnd_586 < baseStart_586 := by decide
  rcases family_descends (prefixWord ++ tailWord_586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600 : List Nat := [2, 1, 2, 2, 1, 2, 5, 5]
def baseStart_600 : Nat := 118140960795 + 600 * 2 ^ 59
def prefixEnd_600 : Nat := 4983230072969 + 3 ^ 40 * 600 * 2
def baseEnd_600 : Nat := 91285449719373688073

theorem tailTrace_600 : CollatzResearch.WordTrace tailWord_600 prefixEnd_600 91285449719373688073 := by
  unfold tailWord_600
  simp only [CollatzResearch.WordTrace]
  refine ⟨10941898916888658475627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14589198555851544634169 10941898916888658475627)
  ·
    refine ⟨16412848375332987713441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10941898916888658475627 16412848375332987713441)
    ·
      refine ⟨12309636281499740785081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16412848375332987713441 12309636281499740785081)
      ·
        refine ⟨9232227211124805588811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12309636281499740785081 9232227211124805588811)
        ·
          refine ⟨13848340816687208383217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9232227211124805588811 13848340816687208383217)
          ·
            refine ⟨10386255612515406287413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13848340816687208383217 10386255612515406287413)
            ·
              refine ⟨973711463673319339445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10386255612515406287413 973711463673319339445)
              ·
                refine ⟨91285449719373688073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 973711463673319339445 91285449719373688073)
                ·
                  rfl

theorem cell20_600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600 prefixEnd_600 := by exact prefixLift 600
  have htrace : WordTrace (prefixWord ++ tailWord_600) baseStart_600 baseEnd_600 := by
    simpa [prefixWord, tailWord_600, baseEnd_600] using wordTrace_append hprefix tailTrace_600
  have hstable : (prefixWord ++ tailWord_600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600).length < 2 ^ (prefixWord ++ tailWord_600).sum := by decide
  have hdescent : baseEnd_600 < baseStart_600 := by decide
  rcases family_descends (prefixWord ++ tailWord_600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658 : List Nat := [3, 2, 3, 1, 2, 2, 3, 1, 3]
def baseStart_658 : Nat := 118140960795 + 658 * 2 ^ 59
def prefixEnd_658 : Nat := 4983230072969 + 3 ^ 40 * 658 * 2
def baseEnd_658 : Nat := 300329129567697130649

theorem tailTrace_658 : CollatzResearch.WordTrace tailWord_658 prefixEnd_658 300329129567697130649 := by
  unfold tailWord_658
  simp only [CollatzResearch.WordTrace]
  refine ⟨5999807905913305640657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15999487749102148375085 5999807905913305640657)
  ·
    refine ⟨4499855929434979230493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5999807905913305640657 4499855929434979230493)
    ·
      refine ⟨1687445973538117211435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4499855929434979230493 1687445973538117211435)
      ·
        refine ⟨2531168960307175817153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1687445973538117211435 2531168960307175817153)
        ·
          refine ⟨1898376720230381862865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2531168960307175817153 1898376720230381862865)
          ·
            refine ⟨1423782540172786397149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1898376720230381862865 1423782540172786397149)
            ·
              refine ⟨533918452564794898931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1423782540172786397149 533918452564794898931)
              ·
                refine ⟨800877678847192348397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 533918452564794898931 800877678847192348397)
                ·
                  refine ⟨300329129567697130649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 800877678847192348397 300329129567697130649)
                  ·
                    rfl

theorem cell20_658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658 prefixEnd_658 := by exact prefixLift 658
  have htrace : WordTrace (prefixWord ++ tailWord_658) baseStart_658 baseEnd_658 := by
    simpa [prefixWord, tailWord_658, baseEnd_658] using wordTrace_append hprefix tailTrace_658
  have hstable : (prefixWord ++ tailWord_658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658).length < 2 ^ (prefixWord ++ tailWord_658).sum := by decide
  have hdescent : baseEnd_658 < baseStart_658 := by decide
  rcases family_descends (prefixWord ++ tailWord_658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669 : List Nat := [1, 4, 2, 1, 1, 1, 4, 2, 4]
def baseStart_669 : Nat := 118140960795 + 669 * 2 ^ 59
def prefixEnd_669 : Nat := 4983230072969 + 3 ^ 40 * 669 * 2
def baseEnd_669 : Nat := 305349829300547763937

theorem tailTrace_669 : CollatzResearch.WordTrace tailWord_669 prefixEnd_669 305349829300547763937 := by
  unfold tailWord_669
  simp only [CollatzResearch.WordTrace]
  refine ⟨24400434583802101213061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16266956389201400808707 24400434583802101213061)
  ·
    refine ⟨4575081484462893977449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24400434583802101213061 4575081484462893977449)
    ·
      refine ⟨3431311113347170483087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4575081484462893977449 3431311113347170483087)
      ·
        refine ⟨5146966670020755724631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3431311113347170483087 5146966670020755724631)
        ·
          refine ⟨7720450005031133586947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5146966670020755724631 7720450005031133586947)
          ·
            refine ⟨11580675007546700380421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7720450005031133586947 11580675007546700380421)
            ·
              refine ⟨2171376563915006321329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11580675007546700380421 2171376563915006321329)
              ·
                refine ⟨1628532422936254740997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2171376563915006321329 1628532422936254740997)
                ·
                  refine ⟨305349829300547763937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1628532422936254740997 305349829300547763937)
                  ·
                    rfl

theorem cell20_669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669 prefixEnd_669 := by exact prefixLift 669
  have htrace : WordTrace (prefixWord ++ tailWord_669) baseStart_669 baseEnd_669 := by
    simpa [prefixWord, tailWord_669, baseEnd_669] using wordTrace_append hprefix tailTrace_669
  have hstable : (prefixWord ++ tailWord_669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669).length < 2 ^ (prefixWord ++ tailWord_669).sum := by decide
  have hdescent : baseEnd_669 < baseStart_669 := by decide
  rcases family_descends (prefixWord ++ tailWord_669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672 : List Nat := [2, 1, 1, 4, 4, 2, 2, 4]
def baseStart_672 : Nat := 118140960795 + 672 * 2 ^ 59
def prefixEnd_672 : Nat := 4983230072969 + 3 ^ 40 * 672 * 2
def baseEnd_672 : Nat := 102239703681956887975

theorem tailTrace_672 : CollatzResearch.WordTrace tailWord_672 prefixEnd_672 102239703681956887975 := by
  unfold tailWord_672
  simp only [CollatzResearch.WordTrace]
  refine ⟨12254926786466806786135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16339902381955742381513 12254926786466806786135)
  ·
    refine ⟨18382390179700210179203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12254926786466806786135 18382390179700210179203)
    ·
      refine ⟨27573585269550315268805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18382390179700210179203 27573585269550315268805)
      ·
        refine ⟨5170047238040684112901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27573585269550315268805 5170047238040684112901)
        ·
          refine ⟨969383857132628271169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5170047238040684112901 969383857132628271169)
          ·
            refine ⟨727037892849471203377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 969383857132628271169 727037892849471203377)
            ·
              refine ⟨545278419637103402533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 727037892849471203377 545278419637103402533)
              ·
                refine ⟨102239703681956887975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 545278419637103402533 102239703681956887975)
                ·
                  rfl

theorem cell20_672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 4].length) (baseStart_672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672 prefixEnd_672 := by exact prefixLift 672
  have htrace : WordTrace (prefixWord ++ tailWord_672) baseStart_672 baseEnd_672 := by
    simpa [prefixWord, tailWord_672, baseEnd_672] using wordTrace_append hprefix tailTrace_672
  have hstable : (prefixWord ++ tailWord_672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672).length < 2 ^ (prefixWord ++ tailWord_672).sum := by decide
  have hdescent : baseEnd_672 < baseStart_672 := by decide
  rcases family_descends (prefixWord ++ tailWord_672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676 : List Nat := [2, 3, 1, 2, 2, 1, 3, 6]
def baseStart_676 : Nat := 118140960795 + 676 * 2 ^ 59
def prefixEnd_676 : Nat := 4983230072969 + 3 ^ 40 * 676 * 2
def baseEnd_676 : Nat := 102848273346544843525

theorem tailTrace_676 : CollatzResearch.WordTrace tailWord_676 prefixEnd_676 102848273346544843525 := by
  unfold tailWord_676
  simp only [CollatzResearch.WordTrace]
  refine ⟨12327872779221148358941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16437163705628197811921 12327872779221148358941)
  ·
    refine ⟨4622952292207930634603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12327872779221148358941 4622952292207930634603)
    ·
      refine ⟨6934428438311895951905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4622952292207930634603 6934428438311895951905)
      ·
        refine ⟨5200821328733921963929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6934428438311895951905 5200821328733921963929)
        ·
          refine ⟨3900615996550441472947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5200821328733921963929 3900615996550441472947)
          ·
            refine ⟨5850923994825662209421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3900615996550441472947 5850923994825662209421)
            ·
              refine ⟨2194096498059623328533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5850923994825662209421 2194096498059623328533)
              ·
                refine ⟨102848273346544843525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2194096498059623328533 102848273346544843525)
                ·
                  rfl

theorem cell20_676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676 prefixEnd_676 := by exact prefixLift 676
  have htrace : WordTrace (prefixWord ++ tailWord_676) baseStart_676 baseEnd_676 := by
    simpa [prefixWord, tailWord_676, baseEnd_676] using wordTrace_append hprefix tailTrace_676
  have hstable : (prefixWord ++ tailWord_676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676).length < 2 ^ (prefixWord ++ tailWord_676).sum := by decide
  have hdescent : baseEnd_676 < baseStart_676 := by decide
  rcases family_descends (prefixWord ++ tailWord_676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693 : List Nat := [1, 3, 3, 3, 1, 3, 6]
def baseStart_693 : Nat := 118140960795 + 693 * 2 ^ 59
def prefixEnd_693 : Nat := 4983230072969 + 3 ^ 40 * 693 * 2
def baseEnd_693 : Nat := 35144898140347884871

theorem tailTrace_693 : CollatzResearch.WordTrace tailWord_693 prefixEnd_693 35144898140347884871 := by
  unfold tailWord_693
  simp only [CollatzResearch.WordTrace]
  refine ⟨25275786496854200086733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16850524331236133391155 25275786496854200086733)
  ·
    refine ⟨9478419936320325032525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25275786496854200086733 9478419936320325032525)
    ·
      refine ⟨3554407476120121887197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9478419936320325032525 3554407476120121887197)
      ·
        refine ⟨1332902803545045707699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3554407476120121887197 1332902803545045707699)
        ·
          refine ⟨1999354205317568561549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1332902803545045707699 1999354205317568561549)
          ·
            refine ⟨749757826994088210581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1999354205317568561549 749757826994088210581)
            ·
              refine ⟨35144898140347884871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 749757826994088210581 35144898140347884871)
              ·
                rfl

theorem cell20_693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 6].length) (baseStart_693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693 prefixEnd_693 := by exact prefixLift 693
  have htrace : WordTrace (prefixWord ++ tailWord_693) baseStart_693 baseEnd_693 := by
    simpa [prefixWord, tailWord_693, baseEnd_693] using wordTrace_append hprefix tailTrace_693
  have hstable : (prefixWord ++ tailWord_693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693).length < 2 ^ (prefixWord ++ tailWord_693).sum := by decide
  have hdescent : baseEnd_693 < baseStart_693 := by decide
  rcases family_descends (prefixWord ++ tailWord_693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700 : List Nat := [2, 2, 2, 3, 1, 1, 2, 4, 3]
def baseStart_700 : Nat := 118140960795 + 700 * 2 ^ 59
def prefixEnd_700 : Nat := 4983230072969 + 3 ^ 40 * 700 * 2
def baseEnd_700 : Nat := 319499074002217730477

theorem tailTrace_700 : CollatzResearch.WordTrace tailWord_700 prefixEnd_700 319499074002217730477 := by
  unfold tailWord_700
  simp only [CollatzResearch.WordTrace]
  refine ⟨12765548735747197795777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17020731647662930394369 12765548735747197795777)
  ·
    refine ⟨9574161551810398346833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12765548735747197795777 9574161551810398346833)
    ·
      refine ⟨7180621163857798760125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9574161551810398346833 7180621163857798760125)
      ·
        refine ⟨2692732936446674535047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7180621163857798760125 2692732936446674535047)
        ·
          refine ⟨4039099404670011802571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2692732936446674535047 4039099404670011802571)
          ·
            refine ⟨6058649107005017703857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4039099404670011802571 6058649107005017703857)
            ·
              refine ⟨4543986830253763277893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6058649107005017703857 4543986830253763277893)
              ·
                refine ⟨851997530672580614605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4543986830253763277893 851997530672580614605)
                ·
                  refine ⟨319499074002217730477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 851997530672580614605 319499074002217730477)
                  ·
                    rfl

theorem cell20_700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700 prefixEnd_700 := by exact prefixLift 700
  have htrace : WordTrace (prefixWord ++ tailWord_700) baseStart_700 baseEnd_700 := by
    simpa [prefixWord, tailWord_700, baseEnd_700] using wordTrace_append hprefix tailTrace_700
  have hstable : (prefixWord ++ tailWord_700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700).length < 2 ^ (prefixWord ++ tailWord_700).sum := by decide
  have hdescent : baseEnd_700 < baseStart_700 := by decide
  rcases family_descends (prefixWord ++ tailWord_700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703 : List Nat := [1, 1, 2, 2, 2, 5, 3, 2, 2]
def baseStart_703 : Nat := 118140960795 + 703 * 2 ^ 59
def prefixEnd_703 : Nat := 4983230072969 + 3 ^ 40 * 703 * 2
def baseEnd_703 : Nat := 320868355747540630465

theorem tailTrace_703 : CollatzResearch.WordTrace tailWord_703 prefixEnd_703 320868355747540630465 := by
  unfold tailWord_703
  simp only [CollatzResearch.WordTrace]
  refine ⟨25640516460625907950763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17093677640417271967175 25640516460625907950763)
  ·
    refine ⟨38460774690938861926145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25640516460625907950763 38460774690938861926145)
    ·
      refine ⟨28845581018204146444609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38460774690938861926145 28845581018204146444609)
      ·
        refine ⟨21634185763653109833457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28845581018204146444609 21634185763653109833457)
        ·
          refine ⟨16225639322739832375093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21634185763653109833457 16225639322739832375093)
          ·
            refine ⟨1521153686506859285165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16225639322739832375093 1521153686506859285165)
            ·
              refine ⟨570432632440072231937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1521153686506859285165 570432632440072231937)
              ·
                refine ⟨427824474330054173953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 570432632440072231937 427824474330054173953)
                ·
                  refine ⟨320868355747540630465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427824474330054173953 320868355747540630465)
                  ·
                    rfl

theorem cell20_703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 2].length) (baseStart_703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703 prefixEnd_703 := by exact prefixLift 703
  have htrace : WordTrace (prefixWord ++ tailWord_703) baseStart_703 baseEnd_703 := by
    simpa [prefixWord, tailWord_703, baseEnd_703] using wordTrace_append hprefix tailTrace_703
  have hstable : (prefixWord ++ tailWord_703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703).length < 2 ^ (prefixWord ++ tailWord_703).sum := by decide
  have hdescent : baseEnd_703 < baseStart_703 := by decide
  rcases family_descends (prefixWord ++ tailWord_703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714 : List Nat := [3, 1, 2, 1, 4, 1, 1, 7]
def baseStart_714 : Nat := 118140960795 + 714 * 2 ^ 59
def prefixEnd_714 : Nat := 4983230072969 + 3 ^ 40 * 714 * 2
def baseEnd_714 : Nat := 108629685160130421251

theorem tailTrace_714 : CollatzResearch.WordTrace tailWord_714 prefixEnd_714 108629685160130421251 := by
  unfold tailWord_714
  simp only [CollatzResearch.WordTrace]
  refine ⟨6510429855193696650299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17361146280516524400797 6510429855193696650299)
  ·
    refine ⟨9765644782790544975449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6510429855193696650299 9765644782790544975449)
    ·
      refine ⟨7324233587092908731587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9765644782790544975449 7324233587092908731587)
      ·
        refine ⟨10986350380639363097381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7324233587092908731587 10986350380639363097381)
        ·
          refine ⟨2059940696369880580759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10986350380639363097381 2059940696369880580759)
          ·
            refine ⟨3089911044554820871139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2059940696369880580759 3089911044554820871139)
            ·
              refine ⟨4634866566832231306709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3089911044554820871139 4634866566832231306709)
              ·
                refine ⟨108629685160130421251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4634866566832231306709 108629685160130421251)
                ·
                  rfl

theorem cell20_714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714 prefixEnd_714 := by exact prefixLift 714
  have htrace : WordTrace (prefixWord ++ tailWord_714) baseStart_714 baseEnd_714 := by
    simpa [prefixWord, tailWord_714, baseEnd_714] using wordTrace_append hprefix tailTrace_714
  have hstable : (prefixWord ++ tailWord_714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714).length < 2 ^ (prefixWord ++ tailWord_714).sum := by decide
  have hdescent : baseEnd_714 < baseStart_714 := by decide
  rcases family_descends (prefixWord ++ tailWord_714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776 : List Nat := [2, 1, 3, 2, 2, 2, 2, 3, 3]
def baseStart_776 : Nat := 118140960795 + 776 * 2 ^ 59
def prefixEnd_776 : Nat := 4983230072969 + 3 ^ 40 * 776 * 2
def baseEnd_776 : Nat := 354187544883731196833

theorem tailTrace_776 : CollatzResearch.WordTrace tailWord_776 prefixEnd_776 354187544883731196833 := by
  unfold tailWord_776
  simp only [CollatzResearch.WordTrace]
  refine ⟨14151522598079687679091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18868696797439583572121 14151522598079687679091)
  ·
    refine ⟨21227283897119531518637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14151522598079687679091 21227283897119531518637)
    ·
      refine ⟨7960231461419824319489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21227283897119531518637 7960231461419824319489)
      ·
        refine ⟨5970173596064868239617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7960231461419824319489 5970173596064868239617)
        ·
          refine ⟨4477630197048651179713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5970173596064868239617 4477630197048651179713)
          ·
            refine ⟨3358222647786488384785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4477630197048651179713 3358222647786488384785)
            ·
              refine ⟨2518666985839866288589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3358222647786488384785 2518666985839866288589)
              ·
                refine ⟨944500119689949858221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2518666985839866288589 944500119689949858221)
                ·
                  refine ⟨354187544883731196833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 944500119689949858221 354187544883731196833)
                  ·
                    rfl

theorem cell20_776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 3].length) (baseStart_776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776 prefixEnd_776 := by exact prefixLift 776
  have htrace : WordTrace (prefixWord ++ tailWord_776) baseStart_776 baseEnd_776 := by
    simpa [prefixWord, tailWord_776, baseEnd_776] using wordTrace_append hprefix tailTrace_776
  have hstable : (prefixWord ++ tailWord_776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776).length < 2 ^ (prefixWord ++ tailWord_776).sum := by decide
  have hdescent : baseEnd_776 < baseStart_776 := by decide
  rcases family_descends (prefixWord ++ tailWord_776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800 : List Nat := [2, 1, 1, 5, 1, 2, 1, 5, 2]
def baseStart_800 : Nat := 118140960795 + 800 * 2 ^ 59
def prefixEnd_800 : Nat := 4983230072969 + 3 ^ 40 * 800 * 2
def baseEnd_800 : Nat := 365141798846314396735

theorem tailTrace_800 : CollatzResearch.WordTrace tailWord_800 prefixEnd_800 365141798846314396735 := by
  unfold tailWord_800
  simp only [CollatzResearch.WordTrace]
  refine ⟨14589198554605737115927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19452264739474316154569 14589198554605737115927)
  ·
    refine ⟨21883797831908605673891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14589198554605737115927 21883797831908605673891)
    ·
      refine ⟨32825696747862908510837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21883797831908605673891 32825696747862908510837)
      ·
        refine ⟨3077409070112147672891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32825696747862908510837 3077409070112147672891)
        ·
          refine ⟨4616113605168221509337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3077409070112147672891 4616113605168221509337)
          ·
            refine ⟨3462085203876166132003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4616113605168221509337 3462085203876166132003)
            ·
              refine ⟨5193127805814249198005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3462085203876166132003 5193127805814249198005)
              ·
                refine ⟨486855731795085862313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5193127805814249198005 486855731795085862313)
                ·
                  refine ⟨365141798846314396735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486855731795085862313 365141798846314396735)
                  ·
                    rfl

theorem cell20_800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 2].length) (baseStart_800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800 prefixEnd_800 := by exact prefixLift 800
  have htrace : WordTrace (prefixWord ++ tailWord_800) baseStart_800 baseEnd_800 := by
    simpa [prefixWord, tailWord_800, baseEnd_800] using wordTrace_append hprefix tailTrace_800
  have hstable : (prefixWord ++ tailWord_800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800).length < 2 ^ (prefixWord ++ tailWord_800).sum := by decide
  have hdescent : baseEnd_800 < baseStart_800 := by decide
  rcases family_descends (prefixWord ++ tailWord_800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821 : List Nat := [1, 3, 3, 1, 3, 1, 1, 3, 4]
def baseStart_821 : Nat := 118140960795 + 821 * 2 ^ 59
def prefixEnd_821 : Nat := 4983230072969 + 3 ^ 40 * 821 * 2
def baseEnd_821 : Nat := 374726771063574696649

theorem tailTrace_821 : CollatzResearch.WordTrace tailWord_821 prefixEnd_821 374726771063574696649 := by
  unfold tailWord_821
  simp only [CollatzResearch.WordTrace]
  refine ⟨29944330033132060746317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19962886688754707164211 29944330033132060746317)
  ·
    refine ⟨11229123762424522779869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29944330033132060746317 11229123762424522779869)
    ·
      refine ⟨4210921410909196042451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11229123762424522779869 4210921410909196042451)
      ·
        refine ⟨6316382116363794063677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4210921410909196042451 6316382116363794063677)
        ·
          refine ⟨2368643293636422773879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6316382116363794063677 2368643293636422773879)
          ·
            refine ⟨3552964940454634160819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2368643293636422773879 3552964940454634160819)
            ·
              refine ⟨5329447410681951241229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3552964940454634160819 5329447410681951241229)
              ·
                refine ⟨1998542779005731715461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5329447410681951241229 1998542779005731715461)
                ·
                  refine ⟨374726771063574696649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1998542779005731715461 374726771063574696649)
                  ·
                    rfl

theorem cell20_821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821 prefixEnd_821 := by exact prefixLift 821
  have htrace : WordTrace (prefixWord ++ tailWord_821) baseStart_821 baseEnd_821 := by
    simpa [prefixWord, tailWord_821, baseEnd_821] using wordTrace_append hprefix tailTrace_821
  have hstable : (prefixWord ++ tailWord_821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821).length < 2 ^ (prefixWord ++ tailWord_821).sum := by decide
  have hdescent : baseEnd_821 < baseStart_821 := by decide
  rcases family_descends (prefixWord ++ tailWord_821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831 : List Nat := [1, 1, 2, 2, 5, 2, 3, 1, 3]
def baseStart_831 : Nat := 118140960795 + 831 * 2 ^ 59
def prefixEnd_831 : Nat := 4983230072969 + 3 ^ 40 * 831 * 2
def baseEnd_831 : Nat := 379291043547984363275

theorem tailTrace_831 : CollatzResearch.WordTrace tailWord_831 prefixEnd_831 379291043547984363275 := by
  unfold tailWord_831
  simp only [CollatzResearch.WordTrace]
  refine ⟨30309059996903768610347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20206039997935845740231 30309059996903768610347)
  ·
    refine ⟨45463589995355652915521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30309059996903768610347 45463589995355652915521)
    ·
      refine ⟨34097692496516739686641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45463589995355652915521 34097692496516739686641)
      ·
        refine ⟨25573269372387554764981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34097692496516739686641 25573269372387554764981)
        ·
          refine ⟨2397494003661333259217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25573269372387554764981 2397494003661333259217)
          ·
            refine ⟨1798120502745999944413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2397494003661333259217 1798120502745999944413)
            ·
              refine ⟨674295188529749979155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1798120502745999944413 674295188529749979155)
              ·
                refine ⟨1011442782794624968733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674295188529749979155 1011442782794624968733)
                ·
                  refine ⟨379291043547984363275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1011442782794624968733 379291043547984363275)
                  ·
                    rfl

theorem cell20_831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 3].length) (baseStart_831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831 prefixEnd_831 := by exact prefixLift 831
  have htrace : WordTrace (prefixWord ++ tailWord_831) baseStart_831 baseEnd_831 := by
    simpa [prefixWord, tailWord_831, baseEnd_831] using wordTrace_append hprefix tailTrace_831
  have hstable : (prefixWord ++ tailWord_831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831).length < 2 ^ (prefixWord ++ tailWord_831).sum := by decide
  have hdescent : baseEnd_831 < baseStart_831 := by decide
  rcases family_descends (prefixWord ++ tailWord_831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 6]
def baseStart_842 : Nat := 118140960795 + 842 * 2 ^ 59
def prefixEnd_842 : Nat := 4983230072969 + 3 ^ 40 * 842 * 2
def baseEnd_842 : Nat := 384311743280834996563

theorem tailTrace_842 : CollatzResearch.WordTrace tailWord_842 prefixEnd_842 384311743280834996563 := by
  unfold tailWord_842
  simp only [CollatzResearch.WordTrace]
  refine ⟨7677565739263161815195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20473508638035098173853 7677565739263161815195)
  ·
    refine ⟨11516348608894742722793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7677565739263161815195 11516348608894742722793)
    ·
      refine ⟨8637261456671057042095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11516348608894742722793 8637261456671057042095)
      ·
        refine ⟨12955892185006585563143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8637261456671057042095 12955892185006585563143)
        ·
          refine ⟨19433838277509878344715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12955892185006585563143 19433838277509878344715)
          ·
            refine ⟨29150757416264817517073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19433838277509878344715 29150757416264817517073)
            ·
              refine ⟨21863068062198613137805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29150757416264817517073 21863068062198613137805)
              ·
                refine ⟨8198650523324479926677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21863068062198613137805 8198650523324479926677)
                ·
                  refine ⟨384311743280834996563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8198650523324479926677 384311743280834996563)
                  ·
                    rfl

theorem cell20_842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842 prefixEnd_842 := by exact prefixLift 842
  have htrace : WordTrace (prefixWord ++ tailWord_842) baseStart_842 baseEnd_842 := by
    simpa [prefixWord, tailWord_842, baseEnd_842] using wordTrace_append hprefix tailTrace_842
  have hstable : (prefixWord ++ tailWord_842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842).length < 2 ^ (prefixWord ++ tailWord_842).sum := by decide
  have hdescent : baseEnd_842 < baseStart_842 := by decide
  rcases family_descends (prefixWord ++ tailWord_842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855 : List Nat := [1, 1, 3, 2, 4, 3, 1, 3, 2]
def baseStart_855 : Nat := 118140960795 + 855 * 2 ^ 59
def prefixEnd_855 : Nat := 4983230072969 + 3 ^ 40 * 855 * 2
def baseEnd_855 : Nat := 390245297510567563177

theorem tailTrace_855 : CollatzResearch.WordTrace tailWord_855 prefixEnd_855 390245297510567563177 := by
  unfold tailWord_855
  simp only [CollatzResearch.WordTrace]
  refine ⟨31184411909955867484019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20789607939970578322679 31184411909955867484019)
  ·
    refine ⟨46776617864933801226029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31184411909955867484019 46776617864933801226029)
    ·
      refine ⟨17541231699350175459761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46776617864933801226029 17541231699350175459761)
      ·
        refine ⟨13155923774512631594821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17541231699350175459761 13155923774512631594821)
        ·
          refine ⟨2466735707721118424029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13155923774512631594821 2466735707721118424029)
          ·
            refine ⟨925025890395419409011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2466735707721118424029 925025890395419409011)
            ·
              refine ⟨1387538835593129113517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925025890395419409011 1387538835593129113517)
              ·
                refine ⟨520327063347423417569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1387538835593129113517 520327063347423417569)
                ·
                  refine ⟨390245297510567563177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 520327063347423417569 390245297510567563177)
                  ·
                    rfl

theorem cell20_855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 2].length) (baseStart_855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855 prefixEnd_855 := by exact prefixLift 855
  have htrace : WordTrace (prefixWord ++ tailWord_855) baseStart_855 baseEnd_855 := by
    simpa [prefixWord, tailWord_855, baseEnd_855] using wordTrace_append hprefix tailTrace_855
  have hstable : (prefixWord ++ tailWord_855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855).length < 2 ^ (prefixWord ++ tailWord_855).sum := by decide
  have hdescent : baseEnd_855 < baseStart_855 := by decide
  rcases family_descends (prefixWord ++ tailWord_855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886 : List Nat := [5, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_886 : Nat := 118140960795 + 886 * 2 ^ 59
def prefixEnd_886 : Nat := 4983230072969 + 3 ^ 40 * 886 * 2
def baseEnd_886 : Nat := 404394542212237529717

theorem tailTrace_886 : CollatzResearch.WordTrace tailWord_886 prefixEnd_886 404394542212237529717 := by
  unfold tailWord_886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2019692174853010116407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21543383198432107908341 2019692174853010116407)
  ·
    refine ⟨3029538262279515174611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2019692174853010116407 3029538262279515174611)
    ·
      refine ⟨4544307393419272761917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3029538262279515174611 4544307393419272761917)
      ·
        refine ⟨1704115272532227285719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4544307393419272761917 1704115272532227285719)
        ·
          refine ⟨2556172908798340928579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1704115272532227285719 2556172908798340928579)
          ·
            refine ⟨3834259363197511392869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2556172908798340928579 3834259363197511392869)
            ·
              refine ⟨718923630599533386163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3834259363197511392869 718923630599533386163)
              ·
                refine ⟨1078385445899300079245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 718923630599533386163 1078385445899300079245)
                ·
                  refine ⟨404394542212237529717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1078385445899300079245 404394542212237529717)
                  ·
                    rfl

theorem cell20_886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886 prefixEnd_886 := by exact prefixLift 886
  have htrace : WordTrace (prefixWord ++ tailWord_886) baseStart_886 baseEnd_886 := by
    simpa [prefixWord, tailWord_886, baseEnd_886] using wordTrace_append hprefix tailTrace_886
  have hstable : (prefixWord ++ tailWord_886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886).length < 2 ^ (prefixWord ++ tailWord_886).sum := by decide
  have hdescent : baseEnd_886 < baseStart_886 := by decide
  rcases family_descends (prefixWord ++ tailWord_886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904 : List Nat := [2, 1, 3, 3, 2, 1, 2, 6]
def baseStart_904 : Nat := 118140960795 + 904 * 2 ^ 59
def prefixEnd_904 : Nat := 4983230072969 + 3 ^ 40 * 904 * 2
def baseEnd_904 : Nat := 137536744228058309881

theorem tailTrace_904 : CollatzResearch.WordTrace tailWord_904 prefixEnd_904 137536744228058309881 := by
  unfold tailWord_904
  simp only [CollatzResearch.WordTrace]
  refine ⟨16485794366218618008883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21981059154958157345177 16485794366218618008883)
  ·
    refine ⟨24728691549327927013325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16485794366218618008883 24728691549327927013325)
    ·
      refine ⟨9273259330997972629997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24728691549327927013325 9273259330997972629997)
      ·
        refine ⟨3477472249124239736249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9273259330997972629997 3477472249124239736249)
        ·
          refine ⟨2608104186843179802187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3477472249124239736249 2608104186843179802187)
          ·
            refine ⟨3912156280264769703281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2608104186843179802187 3912156280264769703281)
            ·
              refine ⟨2934117210198577277461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3912156280264769703281 2934117210198577277461)
              ·
                refine ⟨137536744228058309881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2934117210198577277461 137536744228058309881)
                ·
                  rfl

theorem cell20_904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904 prefixEnd_904 := by exact prefixLift 904
  have htrace : WordTrace (prefixWord ++ tailWord_904) baseStart_904 baseEnd_904 := by
    simpa [prefixWord, tailWord_904, baseEnd_904] using wordTrace_append hprefix tailTrace_904
  have hstable : (prefixWord ++ tailWord_904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904).length < 2 ^ (prefixWord ++ tailWord_904).sum := by decide
  have hdescent : baseEnd_904 < baseStart_904 := by decide
  rcases family_descends (prefixWord ++ tailWord_904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980 : List Nat := [2, 4, 1, 2, 1, 3, 7]
def baseStart_980 : Nat := 118140960795 + 980 * 2 ^ 59
def prefixEnd_980 : Nat := 4983230072969 + 3 ^ 40 * 980 * 2
def baseEnd_980 : Nat := 49699855951743155111

theorem tailTrace_980 : CollatzResearch.WordTrace tailWord_980 prefixEnd_980 49699855951743155111 := by
  unfold tailWord_980
  simp only [CollatzResearch.WordTrace]
  refine ⟨17871768228551107892197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23829024304734810522929 17871768228551107892197)
  ·
    refine ⟨3350956542853332729787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17871768228551107892197 3350956542853332729787)
    ·
      refine ⟨5026434814279999094681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3350956542853332729787 5026434814279999094681)
      ·
        refine ⟨3769826110709999321011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5026434814279999094681 3769826110709999321011)
        ·
          refine ⟨5654739166064998981517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3769826110709999321011 5654739166064998981517)
          ·
            refine ⟨2120527187274374618069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5654739166064998981517 2120527187274374618069)
            ·
              refine ⟨49699855951743155111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2120527187274374618069 49699855951743155111)
              ·
                rfl

theorem cell20_980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 7].length) (baseStart_980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_980 prefixEnd_980 := by exact prefixLift 980
  have htrace : WordTrace (prefixWord ++ tailWord_980) baseStart_980 baseEnd_980 := by
    simpa [prefixWord, tailWord_980, baseEnd_980] using wordTrace_append hprefix tailTrace_980
  have hstable : (prefixWord ++ tailWord_980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980).length < 2 ^ (prefixWord ++ tailWord_980).sum := by decide
  have hdescent : baseEnd_980 < baseStart_980 := by decide
  rcases family_descends (prefixWord ++ tailWord_980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014 : List Nat := [5, 1, 1, 1, 3, 3, 2, 4]
def baseStart_1014 : Nat := 118140960795 + 1014 * 2 ^ 59
def prefixEnd_1014 : Nat := 4983230072969 + 3 ^ 40 * 1014 * 2
def baseEnd_1014 : Nat := 154272410004227087509

theorem tailTrace_1014 : CollatzResearch.WordTrace tailWord_1014 prefixEnd_1014 154272410004227087509 := by
  unfold tailWord_1014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2311476145870376407631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24655745555950681681397 2311476145870376407631)
  ·
    refine ⟨3467214218805564611447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2311476145870376407631 3467214218805564611447)
    ·
      refine ⟨5200821328208346917171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3467214218805564611447 5200821328208346917171)
      ·
        refine ⟨7801231992312520375757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5200821328208346917171 7801231992312520375757)
        ·
          refine ⟨2925461997117195140909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7801231992312520375757 2925461997117195140909)
          ·
            refine ⟨1097048248918948177841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2925461997117195140909 1097048248918948177841)
            ·
              refine ⟨822786186689211133381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1097048248918948177841 822786186689211133381)
              ·
                refine ⟨154272410004227087509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 822786186689211133381 154272410004227087509)
                ·
                  rfl

theorem cell20_1014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_1014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1014 prefixEnd_1014 := by exact prefixLift 1014
  have htrace : WordTrace (prefixWord ++ tailWord_1014) baseStart_1014 baseEnd_1014 := by
    simpa [prefixWord, tailWord_1014, baseEnd_1014] using wordTrace_append hprefix tailTrace_1014
  have hstable : (prefixWord ++ tailWord_1014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014).length < 2 ^ (prefixWord ++ tailWord_1014).sum := by decide
  have hdescent : baseEnd_1014 < baseStart_1014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 5]
def baseStart_1025 : Nat := 118140960795 + 1025 * 2 ^ 59
def prefixEnd_1025 : Nat := 4983230072969 + 3 ^ 40 * 1025 * 2
def baseEnd_1025 : Nat := 467837929745531895815

theorem tailTrace_1025 : CollatzResearch.WordTrace tailWord_1025 prefixEnd_1025 467837929745531895815 := by
  unfold tailWord_1025
  simp only [CollatzResearch.WordTrace]
  refine ⟨37384821294074901172529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24923214196049934115019 37384821294074901172529)
  ·
    refine ⟨28038615970556175879397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37384821294074901172529 28038615970556175879397)
    ·
      refine ⟨5257240494479282977387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28038615970556175879397 5257240494479282977387)
      ·
        refine ⟨7885860741718924466081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5257240494479282977387 7885860741718924466081)
        ·
          refine ⟨5914395556289193349561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7885860741718924466081 5914395556289193349561)
          ·
            refine ⟨4435796667216895012171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5914395556289193349561 4435796667216895012171)
            ·
              refine ⟨6653695000825342518257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4435796667216895012171 6653695000825342518257)
              ·
                refine ⟨4990271250619006888693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6653695000825342518257 4990271250619006888693)
                ·
                  refine ⟨467837929745531895815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4990271250619006888693 467837929745531895815)
                  ·
                    rfl

theorem cell20_1025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_1025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025 prefixEnd_1025 := by exact prefixLift 1025
  have htrace : WordTrace (prefixWord ++ tailWord_1025) baseStart_1025 baseEnd_1025 := by
    simpa [prefixWord, tailWord_1025, baseEnd_1025] using wordTrace_append hprefix tailTrace_1025
  have hstable : (prefixWord ++ tailWord_1025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025).length < 2 ^ (prefixWord ++ tailWord_1025).sum := by decide
  have hdescent : baseEnd_1025 < baseStart_1025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045 : List Nat := [1, 3, 2, 1, 4, 2, 3, 2, 2]
def baseStart_1045 : Nat := 118140960795 + 1045 * 2 ^ 59
def prefixEnd_1045 : Nat := 4983230072969 + 3 ^ 40 * 1045 * 2
def baseEnd_1045 : Nat := 476966474714351229067

theorem tailTrace_1045 : CollatzResearch.WordTrace tailWord_1045 prefixEnd_1045 476966474714351229067 := by
  unfold tailWord_1045
  simp only [CollatzResearch.WordTrace]
  refine ⟨38114281221618316900589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25409520814412211267059 38114281221618316900589)
  ·
    refine ⟨14292855458106868837721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38114281221618316900589 14292855458106868837721)
    ·
      refine ⟨10719641593580151628291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14292855458106868837721 10719641593580151628291)
      ·
        refine ⟨16079462390370227442437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10719641593580151628291 16079462390370227442437)
        ·
          refine ⟨3014899198194417645457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16079462390370227442437 3014899198194417645457)
          ·
            refine ⟨2261174398645813234093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3014899198194417645457 2261174398645813234093)
            ·
              refine ⟨847940399492179962785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2261174398645813234093 847940399492179962785)
              ·
                refine ⟨635955299619134972089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 847940399492179962785 635955299619134972089)
                ·
                  refine ⟨476966474714351229067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 635955299619134972089 476966474714351229067)
                  ·
                    rfl

theorem cell20_1045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 2].length) (baseStart_1045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045 prefixEnd_1045 := by exact prefixLift 1045
  have htrace : WordTrace (prefixWord ++ tailWord_1045) baseStart_1045 baseEnd_1045 := by
    simpa [prefixWord, tailWord_1045, baseEnd_1045] using wordTrace_append hprefix tailTrace_1045
  have hstable : (prefixWord ++ tailWord_1045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045).length < 2 ^ (prefixWord ++ tailWord_1045).sum := by decide
  have hdescent : baseEnd_1045 < baseStart_1045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049 : List Nat := [1, 2, 1, 2, 1, 1, 4, 6, 2]
def baseStart_1049 : Nat := 118140960795 + 1049 * 2 ^ 59
def prefixEnd_1049 : Nat := 4983230072969 + 3 ^ 40 * 1049 * 2
def baseEnd_1049 : Nat := 478792183708115095717

theorem tailTrace_1049 : CollatzResearch.WordTrace tailWord_1049 prefixEnd_1049 478792183708115095717 := by
  unfold tailWord_1049
  simp only [CollatzResearch.WordTrace]
  refine ⟨38260173207127000046201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25506782138084666697467 38260173207127000046201)
  ·
    refine ⟨28695129905345250034651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38260173207127000046201 28695129905345250034651)
    ·
      refine ⟨43042694858017875051977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28695129905345250034651 43042694858017875051977)
      ·
        refine ⟨32282021143513406288983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43042694858017875051977 32282021143513406288983)
        ·
          refine ⟨48423031715270109433475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32282021143513406288983 48423031715270109433475)
          ·
            refine ⟨72634547572905164150213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48423031715270109433475 72634547572905164150213)
            ·
              refine ⟨13618977669919718278165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72634547572905164150213 13618977669919718278165)
              ·
                refine ⟨638389578277486794289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13618977669919718278165 638389578277486794289)
                ·
                  refine ⟨478792183708115095717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 638389578277486794289 478792183708115095717)
                  ·
                    rfl

theorem cell20_1049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 2].length) (baseStart_1049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1049 prefixEnd_1049 := by exact prefixLift 1049
  have htrace : WordTrace (prefixWord ++ tailWord_1049) baseStart_1049 baseEnd_1049 := by
    simpa [prefixWord, tailWord_1049, baseEnd_1049] using wordTrace_append hprefix tailTrace_1049
  have hstable : (prefixWord ++ tailWord_1049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049).length < 2 ^ (prefixWord ++ tailWord_1049).sum := by decide
  have hdescent : baseEnd_1049 < baseStart_1049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059 : List Nat := [1, 1, 1, 4, 3, 4, 2, 1, 3]
def baseStart_1059 : Nat := 118140960795 + 1059 * 2 ^ 59
def prefixEnd_1059 : Nat := 4983230072969 + 3 ^ 40 * 1059 * 2
def baseEnd_1059 : Nat := 483356456192524762343

theorem tailTrace_1059 : CollatzResearch.WordTrace tailWord_1059 prefixEnd_1059 483356456192524762343 := by
  unfold tailWord_1059
  simp only [CollatzResearch.WordTrace]
  refine ⟨38624903170898707910231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25749935447265805273487 38624903170898707910231)
  ·
    refine ⟨57937354756348061865347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38624903170898707910231 57937354756348061865347)
    ·
      refine ⟨86906032134522092798021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57937354756348061865347 86906032134522092798021)
      ·
        refine ⟨16294881025222892399629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86906032134522092798021 16294881025222892399629)
        ·
          refine ⟨6110580384458584649861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16294881025222892399629 6110580384458584649861)
          ·
            refine ⟨1145733822085984621849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6110580384458584649861 1145733822085984621849)
            ·
              refine ⟨859300366564488466387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1145733822085984621849 859300366564488466387)
              ·
                refine ⟨1288950549846732699581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 859300366564488466387 1288950549846732699581)
                ·
                  refine ⟨483356456192524762343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1288950549846732699581 483356456192524762343)
                  ·
                    rfl

theorem cell20_1059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 3].length) (baseStart_1059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1059 prefixEnd_1059 := by exact prefixLift 1059
  have htrace : WordTrace (prefixWord ++ tailWord_1059) baseStart_1059 baseEnd_1059 := by
    simpa [prefixWord, tailWord_1059, baseEnd_1059] using wordTrace_append hprefix tailTrace_1059
  have hstable : (prefixWord ++ tailWord_1059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059).length < 2 ^ (prefixWord ++ tailWord_1059).sum := by decide
  have hdescent : baseEnd_1059 < baseStart_1059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087 : List Nat := [1, 1, 2, 2, 3, 1, 1, 7, 2]
def baseStart_1087 : Nat := 118140960795 + 1087 * 2 ^ 59
def prefixEnd_1087 : Nat := 4983230072969 + 3 ^ 40 * 1087 * 2
def baseEnd_1087 : Nat := 496136419148871828895

theorem tailTrace_1087 : CollatzResearch.WordTrace tailWord_1087 prefixEnd_1087 496136419148871828895 := by
  unfold tailWord_1087
  simp only [CollatzResearch.WordTrace]
  refine ⟨39646147069459489929515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26430764712972993286343 39646147069459489929515)
  ·
    refine ⟨59469220604189234894273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39646147069459489929515 59469220604189234894273)
    ·
      refine ⟨44601915453141926170705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59469220604189234894273 44601915453141926170705)
      ·
        refine ⟨33451436589856444628029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44601915453141926170705 33451436589856444628029)
        ·
          refine ⟨12544288721196166735511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33451436589856444628029 12544288721196166735511)
          ·
            refine ⟨18816433081794250103267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12544288721196166735511 18816433081794250103267)
            ·
              refine ⟨28224649622691375154901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18816433081794250103267 28224649622691375154901)
              ·
                refine ⟨661515225531829105193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 28224649622691375154901 661515225531829105193)
                ·
                  refine ⟨496136419148871828895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 661515225531829105193 496136419148871828895)
                  ·
                    rfl

theorem cell20_1087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 2].length) (baseStart_1087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1087 prefixEnd_1087 := by exact prefixLift 1087
  have htrace : WordTrace (prefixWord ++ tailWord_1087) baseStart_1087 baseEnd_1087 := by
    simpa [prefixWord, tailWord_1087, baseEnd_1087] using wordTrace_append hprefix tailTrace_1087
  have hstable : (prefixWord ++ tailWord_1087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087).length < 2 ^ (prefixWord ++ tailWord_1087).sum := by decide
  have hdescent : baseEnd_1087 < baseStart_1087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128 : List Nat := [2, 1, 4, 4, 1, 1, 3, 4]
def baseStart_1128 : Nat := 118140960795 + 1128 * 2 ^ 59
def prefixEnd_1128 : Nat := 4983230072969 + 3 ^ 40 * 1128 * 2
def baseEnd_1128 : Nat := 171616645444983820687

theorem tailTrace_1128 : CollatzResearch.WordTrace tailWord_1128 prefixEnd_1128 171616645444983820687 := by
  unfold tailWord_1128
  simp only [CollatzResearch.WordTrace]
  refine ⟨20570769960461746086019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27427693280615661448025 20570769960461746086019)
  ·
    refine ⟨30856154940692619129029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20570769960461746086019 30856154940692619129029)
    ·
      refine ⟨5785529051379866086693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30856154940692619129029 5785529051379866086693)
      ·
        refine ⟨1084786697133724891255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5785529051379866086693 1084786697133724891255)
        ·
          refine ⟨1627180045700587336883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1084786697133724891255 1627180045700587336883)
          ·
            refine ⟨2440770068550881005325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1627180045700587336883 2440770068550881005325)
            ·
              refine ⟨915288775706580376997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2440770068550881005325 915288775706580376997)
              ·
                refine ⟨171616645444983820687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 915288775706580376997 171616645444983820687)
                ·
                  rfl

theorem cell20_1128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 4].length) (baseStart_1128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1128 prefixEnd_1128 := by exact prefixLift 1128
  have htrace : WordTrace (prefixWord ++ tailWord_1128) baseStart_1128 baseEnd_1128 := by
    simpa [prefixWord, tailWord_1128, baseEnd_1128] using wordTrace_append hprefix tailTrace_1128
  have hstable : (prefixWord ++ tailWord_1128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128).length < 2 ^ (prefixWord ++ tailWord_1128).sum := by decide
  have hdescent : baseEnd_1128 < baseStart_1128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132 : List Nat := [2, 2, 1, 1, 3, 2, 5, 4]
def baseStart_1132 : Nat := 118140960795 + 1132 * 2 ^ 59
def prefixEnd_1132 : Nat := 4983230072969 + 3 ^ 40 * 1132 * 2
def baseEnd_1132 : Nat := 172225215109571776237

theorem tailTrace_1132 : CollatzResearch.WordTrace tailWord_1132 prefixEnd_1132 172225215109571776237 := by
  unfold tailWord_1132
  simp only [CollatzResearch.WordTrace]
  refine ⟨20643715953216087658825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27524954604288116878433 20643715953216087658825)
  ·
    refine ⟨15482786964912065744119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20643715953216087658825 15482786964912065744119)
    ·
      refine ⟨23224180447368098616179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15482786964912065744119 23224180447368098616179)
      ·
        refine ⟨34836270671052147924269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23224180447368098616179 34836270671052147924269)
        ·
          refine ⟨13063601501644555471601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34836270671052147924269 13063601501644555471601)
          ·
            refine ⟨9797701126233416603701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13063601501644555471601 9797701126233416603701)
            ·
              refine ⟨918534480584382806597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9797701126233416603701 918534480584382806597)
              ·
                refine ⟨172225215109571776237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 918534480584382806597 172225215109571776237)
                ·
                  rfl

theorem cell20_1132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 4].length) (baseStart_1132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1132 prefixEnd_1132 := by exact prefixLift 1132
  have htrace : WordTrace (prefixWord ++ tailWord_1132) baseStart_1132 baseEnd_1132 := by
    simpa [prefixWord, tailWord_1132, baseEnd_1132] using wordTrace_append hprefix tailTrace_1132
  have hstable : (prefixWord ++ tailWord_1132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132).length < 2 ^ (prefixWord ++ tailWord_1132).sum := by decide
  have hdescent : baseEnd_1132 < baseStart_1132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156 : List Nat := [2, 3, 2, 1, 2, 2, 3, 2, 3]
def baseStart_1156 : Nat := 118140960795 + 1156 * 2 ^ 59
def prefixEnd_1156 : Nat := 4983230072969 + 3 ^ 40 * 1156 * 2
def baseEnd_1156 : Nat := 527629899291298528613

theorem tailTrace_1156 : CollatzResearch.WordTrace tailWord_1156 prefixEnd_1156 527629899291298528613 := by
  unfold tailWord_1156
  simp only [CollatzResearch.WordTrace]
  refine ⟨21081391909742137095661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28108522546322849460881 21081391909742137095661)
  ·
    refine ⟨7905521966153301410873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21081391909742137095661 7905521966153301410873)
    ·
      refine ⟨5929141474614976058155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7905521966153301410873 5929141474614976058155)
      ·
        refine ⟨8893712211922464087233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5929141474614976058155 8893712211922464087233)
        ·
          refine ⟨6670284158941848065425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8893712211922464087233 6670284158941848065425)
          ·
            refine ⟨5002713119206386049069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6670284158941848065425 5002713119206386049069)
            ·
              refine ⟨1876017419702394768401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5002713119206386049069 1876017419702394768401)
              ·
                refine ⟨1407013064776796076301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1876017419702394768401 1407013064776796076301)
                ·
                  refine ⟨527629899291298528613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1407013064776796076301 527629899291298528613)
                  ·
                    rfl

theorem cell20_1156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_1156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1156 prefixEnd_1156 := by exact prefixLift 1156
  have htrace : WordTrace (prefixWord ++ tailWord_1156) baseStart_1156 baseEnd_1156 := by
    simpa [prefixWord, tailWord_1156, baseEnd_1156] using wordTrace_append hprefix tailTrace_1156
  have hstable : (prefixWord ++ tailWord_1156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156).length < 2 ^ (prefixWord ++ tailWord_1156).sum := by decide
  have hdescent : baseEnd_1156 < baseStart_1156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184 : List Nat := [2, 1, 1, 4, 2, 1, 1, 4, 4]
def baseStart_1184 : Nat := 118140960795 + 1184 * 2 ^ 59
def prefixEnd_1184 : Nat := 4983230072969 + 3 ^ 40 * 1184 * 2
def baseEnd_1184 : Nat := 540409862247645595165

theorem tailTrace_1184 : CollatzResearch.WordTrace tailWord_1184 prefixEnd_1184 540409862247645595165 := by
  unfold tailWord_1184
  simp only [CollatzResearch.WordTrace]
  refine ⟨21592013859022528105303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28789351812030037473737 21592013859022528105303)
  ·
    refine ⟨32388020788533792157955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21592013859022528105303 32388020788533792157955)
    ·
      refine ⟨48582031182800688236933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32388020788533792157955 48582031182800688236933)
      ·
        refine ⟨9109130846775129044425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48582031182800688236933 9109130846775129044425)
        ·
          refine ⟨6831848135081346783319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9109130846775129044425 6831848135081346783319)
          ·
            refine ⟨10247772202622020174979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6831848135081346783319 10247772202622020174979)
            ·
              refine ⟨15371658303933030262469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10247772202622020174979 15371658303933030262469)
              ·
                refine ⟨2882185931987443174213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15371658303933030262469 2882185931987443174213)
                ·
                  refine ⟨540409862247645595165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2882185931987443174213 540409862247645595165)
                  ·
                    rfl

theorem cell20_1184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_1184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1184 prefixEnd_1184 := by exact prefixLift 1184
  have htrace : WordTrace (prefixWord ++ tailWord_1184) baseStart_1184 baseEnd_1184 := by
    simpa [prefixWord, tailWord_1184, baseEnd_1184] using wordTrace_append hprefix tailTrace_1184
  have hstable : (prefixWord ++ tailWord_1184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184).length < 2 ^ (prefixWord ++ tailWord_1184).sum := by decide
  have hdescent : baseEnd_1184 < baseStart_1184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 5]
def baseStart_1194 : Nat := 118140960795 + 1194 * 2 ^ 59
def prefixEnd_1194 : Nat := 4983230072969 + 3 ^ 40 * 1194 * 2
def baseEnd_1194 : Nat := 544974134732055261791

theorem tailTrace_1194 : CollatzResearch.WordTrace tailWord_1194 prefixEnd_1194 544974134732055261791 := by
  unfold tailWord_1194
  simp only [CollatzResearch.WordTrace]
  refine ⟨10887189420454191018659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29032505121211176049757 10887189420454191018659)
  ·
    refine ⟨16330784130681286527989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10887189420454191018659 16330784130681286527989)
    ·
      refine ⟨1531011012251370611999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16330784130681286527989 1531011012251370611999)
      ·
        refine ⟨2296516518377055917999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1531011012251370611999 2296516518377055917999)
        ·
          refine ⟨3444774777565583876999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2296516518377055917999 3444774777565583876999)
          ·
            refine ⟨5167162166348375815499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3444774777565583876999 5167162166348375815499)
            ·
              refine ⟨7750743249522563723249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5167162166348375815499 7750743249522563723249)
              ·
                refine ⟨5813057437141922792437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7750743249522563723249 5813057437141922792437)
                ·
                  refine ⟨544974134732055261791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5813057437141922792437 544974134732055261791)
                  ·
                    rfl

theorem cell20_1194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_1194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1194 prefixEnd_1194 := by exact prefixLift 1194
  have htrace : WordTrace (prefixWord ++ tailWord_1194) baseStart_1194 baseEnd_1194 := by
    simpa [prefixWord, tailWord_1194, baseEnd_1194] using wordTrace_append hprefix tailTrace_1194
  have hstable : (prefixWord ++ tailWord_1194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194).length < 2 ^ (prefixWord ++ tailWord_1194).sum := by decide
  have hdescent : baseEnd_1194 < baseStart_1194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284 : List Nat := [2, 3, 2, 2, 2, 1, 3, 5]
def baseStart_1284 : Nat := 118140960795 + 1284 * 2 ^ 59
def prefixEnd_1284 : Nat := 4983230072969 + 3 ^ 40 * 1284 * 2
def baseEnd_1284 : Nat := 195350862363914087141

theorem tailTrace_1284 : CollatzResearch.WordTrace tailWord_1284 prefixEnd_1284 195350862363914087141 := by
  unfold tailWord_1284
  simp only [CollatzResearch.WordTrace]
  refine ⟨23415663677881067425453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31220884903841423233937 23415663677881067425453)
  ·
    refine ⟨8780873879205400284545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23415663677881067425453 8780873879205400284545)
    ·
      refine ⟨6585655409404050213409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8780873879205400284545 6585655409404050213409)
      ·
        refine ⟨4939241557053037660057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6585655409404050213409 4939241557053037660057)
        ·
          refine ⟨3704431167789778245043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4939241557053037660057 3704431167789778245043)
          ·
            refine ⟨5556646751684667367565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3704431167789778245043 5556646751684667367565)
            ·
              refine ⟨2083742531881750262837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5556646751684667367565 2083742531881750262837)
              ·
                refine ⟨195350862363914087141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2083742531881750262837 195350862363914087141)
                ·
                  rfl

theorem cell20_1284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_1284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1284 prefixEnd_1284 := by exact prefixLift 1284
  have htrace : WordTrace (prefixWord ++ tailWord_1284) baseStart_1284 baseEnd_1284 := by
    simpa [prefixWord, tailWord_1284, baseEnd_1284] using wordTrace_append hprefix tailTrace_1284
  have hstable : (prefixWord ++ tailWord_1284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284).length < 2 ^ (prefixWord ++ tailWord_1284).sum := by decide
  have hdescent : baseEnd_1284 < baseStart_1284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291 : List Nat := [1, 1, 1, 1, 5, 3, 2, 3, 3]
def baseStart_1291 : Nat := 118140960795 + 1291 * 2 ^ 59
def prefixEnd_1291 : Nat := 4983230072969 + 3 ^ 40 * 1291 * 2
def baseEnd_1291 : Nat := 589247577830829028061

theorem tailTrace_1291 : CollatzResearch.WordTrace tailWord_1291 prefixEnd_1291 589247577830829028061 := by
  unfold tailWord_1291
  simp only [CollatzResearch.WordTrace]
  refine ⟨47086638330402330355727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31391092220268220237151 47086638330402330355727)
  ·
    refine ⟨70629957495603495533591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47086638330402330355727 70629957495603495533591)
    ·
      refine ⟨105944936243405243300387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70629957495603495533591 105944936243405243300387)
      ·
        refine ⟨158917404365107864950581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105944936243405243300387 158917404365107864950581)
        ·
          refine ⟨14898506659228862339117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158917404365107864950581 14898506659228862339117)
          ·
            refine ⟨5586939997210823377169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14898506659228862339117 5586939997210823377169)
            ·
              refine ⟨4190204997908117532877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5586939997210823377169 4190204997908117532877)
              ·
                refine ⟨1571326874215544074829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4190204997908117532877 1571326874215544074829)
                ·
                  refine ⟨589247577830829028061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1571326874215544074829 589247577830829028061)
                  ·
                    rfl

theorem cell20_1291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 3].length) (baseStart_1291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1291 prefixEnd_1291 := by exact prefixLift 1291
  have htrace : WordTrace (prefixWord ++ tailWord_1291) baseStart_1291 baseEnd_1291 := by
    simpa [prefixWord, tailWord_1291, baseEnd_1291] using wordTrace_append hprefix tailTrace_1291
  have hstable : (prefixWord ++ tailWord_1291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291).length < 2 ^ (prefixWord ++ tailWord_1291).sum := by decide
  have hdescent : baseEnd_1291 < baseStart_1291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315 : List Nat := [1, 1, 1, 4, 2, 3, 1, 5, 2]
def baseStart_1315 : Nat := 118140960795 + 1315 * 2 ^ 59
def prefixEnd_1315 : Nat := 4983230072969 + 3 ^ 40 * 1315 * 2
def baseEnd_1315 : Nat := 600201831793412227963

theorem tailTrace_1315 : CollatzResearch.WordTrace tailWord_1315 prefixEnd_1315 600201831793412227963 := by
  unfold tailWord_1315
  simp only [CollatzResearch.WordTrace]
  refine ⟨47961990243454429229399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31974660162302952819599 47961990243454429229399)
  ·
    refine ⟨71942985365181643844099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47961990243454429229399 71942985365181643844099)
    ·
      refine ⟨107914478047772465766149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71942985365181643844099 107914478047772465766149)
      ·
        refine ⟨20233964633957337331153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107914478047772465766149 20233964633957337331153)
        ·
          refine ⟨15175473475468002998365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20233964633957337331153 15175473475468002998365)
          ·
            refine ⟨5690802553300501124387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15175473475468002998365 5690802553300501124387)
            ·
              refine ⟨8536203829950751686581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5690802553300501124387 8536203829950751686581)
              ·
                refine ⟨800269109057882970617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8536203829950751686581 800269109057882970617)
                ·
                  refine ⟨600201831793412227963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 800269109057882970617 600201831793412227963)
                  ·
                    rfl

theorem cell20_1315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 2].length) (baseStart_1315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1315 prefixEnd_1315 := by exact prefixLift 1315
  have htrace : WordTrace (prefixWord ++ tailWord_1315) baseStart_1315 baseEnd_1315 := by
    simpa [prefixWord, tailWord_1315, baseEnd_1315] using wordTrace_append hprefix tailTrace_1315
  have hstable : (prefixWord ++ tailWord_1315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315).length < 2 ^ (prefixWord ++ tailWord_1315).sum := by decide
  have hdescent : baseEnd_1315 < baseStart_1315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322 : List Nat := [3, 1, 4, 2, 1, 2, 7]
def baseStart_1322 : Nat := 118140960795 + 1322 * 2 ^ 59
def prefixEnd_1322 : Nat := 4983230072969 + 3 ^ 40 * 1322 * 2
def baseEnd_1322 : Nat := 67044091392499888289

theorem tailTrace_1322 : CollatzResearch.WordTrace tailWord_1322 prefixEnd_1322 67044091392499888289 := by
  unfold tailWord_1322
  simp only [CollatzResearch.WordTrace]
  refine ⟨12054325304523656183555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32144867478729749822813 12054325304523656183555)
  ·
    refine ⟨18081487956785484275333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12054325304523656183555 18081487956785484275333)
    ·
      refine ⟨3390278991897278301625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18081487956785484275333 3390278991897278301625)
      ·
        refine ⟨2542709243922958726219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3390278991897278301625 2542709243922958726219)
        ·
          refine ⟨3814063865884438089329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2542709243922958726219 3814063865884438089329)
          ·
            refine ⟨2860547899413328566997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3814063865884438089329 2860547899413328566997)
            ·
              refine ⟨67044091392499888289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2860547899413328566997 67044091392499888289)
              ·
                rfl

theorem cell20_1322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 7].length) (baseStart_1322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1322 prefixEnd_1322 := by exact prefixLift 1322
  have htrace : WordTrace (prefixWord ++ tailWord_1322) baseStart_1322 baseEnd_1322 := by
    simpa [prefixWord, tailWord_1322, baseEnd_1322] using wordTrace_append hprefix tailTrace_1322
  have hstable : (prefixWord ++ tailWord_1322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322).length < 2 ^ (prefixWord ++ tailWord_1322).sum := by decide
  have hdescent : baseEnd_1322 < baseStart_1322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325 : List Nat := [1, 5, 3, 1, 1, 1, 3, 2, 3]
def baseStart_1325 : Nat := 118140960795 + 1325 * 2 ^ 59
def prefixEnd_1325 : Nat := 4983230072969 + 3 ^ 40 * 1325 * 2
def baseEnd_1325 : Nat := 604766104277821894589

theorem tailTrace_1325 : CollatzResearch.WordTrace tailWord_1325 prefixEnd_1325 604766104277821894589 := by
  unfold tailWord_1325
  simp only [CollatzResearch.WordTrace]
  refine ⟨48326720207226137093429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32217813471484091395619 48326720207226137093429)
  ·
    refine ⟨4530630019427450352509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48326720207226137093429 4530630019427450352509)
    ·
      refine ⟨1698986257285293882191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4530630019427450352509 1698986257285293882191)
      ·
        refine ⟨2548479385927940823287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1698986257285293882191 2548479385927940823287)
        ·
          refine ⟨3822719078891911234931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2548479385927940823287 3822719078891911234931)
          ·
            refine ⟨5734078618337866852397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3822719078891911234931 5734078618337866852397)
            ·
              refine ⟨2150279481876700069649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5734078618337866852397 2150279481876700069649)
              ·
                refine ⟨1612709611407525052237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2150279481876700069649 1612709611407525052237)
                ·
                  refine ⟨604766104277821894589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1612709611407525052237 604766104277821894589)
                  ·
                    rfl

theorem cell20_1325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_1325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1325 prefixEnd_1325 := by exact prefixLift 1325
  have htrace : WordTrace (prefixWord ++ tailWord_1325) baseStart_1325 baseEnd_1325 := by
    simpa [prefixWord, tailWord_1325, baseEnd_1325] using wordTrace_append hprefix tailTrace_1325
  have hstable : (prefixWord ++ tailWord_1325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325).length < 2 ^ (prefixWord ++ tailWord_1325).sum := by decide
  have hdescent : baseEnd_1325 < baseStart_1325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 5]
def baseStart_1329 : Nat := 118140960795 + 1329 * 2 ^ 59
def prefixEnd_1329 : Nat := 4983230072969 + 3 ^ 40 * 1329 * 2
def baseEnd_1329 : Nat := 606591813271585761239

theorem tailTrace_1329 : CollatzResearch.WordTrace tailWord_1329 prefixEnd_1329 606591813271585761239 := by
  unfold tailWord_1329
  simp only [CollatzResearch.WordTrace]
  refine ⟨48472612192734820239041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32315074795156546826027 48472612192734820239041)
  ·
    refine ⟨36354459144551115179281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48472612192734820239041 36354459144551115179281)
    ·
      refine ⟨27265844358413336384461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36354459144551115179281 27265844358413336384461)
      ·
        refine ⟨10224691634405001144173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27265844358413336384461 10224691634405001144173)
        ·
          refine ⟨3834259362901875429065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10224691634405001144173 3834259362901875429065)
          ·
            refine ⟨2875694522176406571799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3834259362901875429065 2875694522176406571799)
            ·
              refine ⟨4313541783264609857699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2875694522176406571799 4313541783264609857699)
              ·
                refine ⟨6470312674896914786549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4313541783264609857699 6470312674896914786549)
                ·
                  refine ⟨606591813271585761239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6470312674896914786549 606591813271585761239)
                  ·
                    rfl

theorem cell20_1329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_1329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1329 prefixEnd_1329 := by exact prefixLift 1329
  have htrace : WordTrace (prefixWord ++ tailWord_1329) baseStart_1329 baseEnd_1329 := by
    simpa [prefixWord, tailWord_1329, baseEnd_1329] using wordTrace_append hprefix tailTrace_1329
  have hstable : (prefixWord ++ tailWord_1329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329).length < 2 ^ (prefixWord ++ tailWord_1329).sum := by decide
  have hdescent : baseEnd_1329 < baseStart_1329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332 : List Nat := [2, 5, 1, 1, 1, 1, 1, 6, 2]
def baseStart_1332 : Nat := 118140960795 + 1332 * 2 ^ 59
def prefixEnd_1332 : Nat := 4983230072969 + 3 ^ 40 * 1332 * 2
def baseEnd_1332 : Nat := 607961095016908661227

theorem tailTrace_1332 : CollatzResearch.WordTrace tailWord_1332 prefixEnd_1332 607961095016908661227 := by
  unfold tailWord_1332
  simp only [CollatzResearch.WordTrace]
  refine ⟨24291015590933166299125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32388020787910888398833 24291015590933166299125)
  ·
    refine ⟨2277282711649984340543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24291015590933166299125 2277282711649984340543)
    ·
      refine ⟨3415924067474976510815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2277282711649984340543 3415924067474976510815)
      ·
        refine ⟨5123886101212464766223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3415924067474976510815 5123886101212464766223)
        ·
          refine ⟨7685829151818697149335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5123886101212464766223 7685829151818697149335)
          ·
            refine ⟨11528743727728045724003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7685829151818697149335 11528743727728045724003)
            ·
              refine ⟨17293115591592068586005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11528743727728045724003 17293115591592068586005)
              ·
                refine ⟨810614793355878214969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17293115591592068586005 810614793355878214969)
                ·
                  refine ⟨607961095016908661227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 810614793355878214969 607961095016908661227)
                  ·
                    rfl

theorem cell20_1332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_1332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1332 prefixEnd_1332 := by exact prefixLift 1332
  have htrace : WordTrace (prefixWord ++ tailWord_1332) baseStart_1332 baseEnd_1332 := by
    simpa [prefixWord, tailWord_1332, baseEnd_1332] using wordTrace_append hprefix tailTrace_1332
  have hstable : (prefixWord ++ tailWord_1332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332).length < 2 ^ (prefixWord ++ tailWord_1332).sum := by decide
  have hdescent : baseEnd_1332 < baseStart_1332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373 : List Nat := [1, 4, 5, 1, 2, 1, 6]
def baseStart_1373 : Nat := 118140960795 + 1373 * 2 ^ 59
def prefixEnd_1373 : Nat := 4983230072969 + 3 ^ 40 * 1373 * 2
def baseEnd_1373 : Nat := 69630512466998699377

theorem tailTrace_1373 : CollatzResearch.WordTrace tailWord_1373 prefixEnd_1373 69630512466998699377 := by
  unfold tailWord_1373
  simp only [CollatzResearch.WordTrace]
  refine ⟨50077424033330334840773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33384949355553556560515 50077424033330334840773)
  ·
    refine ⟨9389517006249437782645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50077424033330334840773 9389517006249437782645)
    ·
      refine ⟨880267219335884792123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9389517006249437782645 880267219335884792123)
      ·
        refine ⟨1320400829003827188185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 880267219335884792123 1320400829003827188185)
        ·
          refine ⟨990300621752870391139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1320400829003827188185 990300621752870391139)
          ·
            refine ⟨1485450932629305586709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990300621752870391139 1485450932629305586709)
            ·
              refine ⟨69630512466998699377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1485450932629305586709 69630512466998699377)
              ·
                rfl

theorem cell20_1373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 6].length) (baseStart_1373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1373 prefixEnd_1373 := by exact prefixLift 1373
  have htrace : WordTrace (prefixWord ++ tailWord_1373) baseStart_1373 baseEnd_1373 := by
    simpa [prefixWord, tailWord_1373, baseEnd_1373] using wordTrace_append hprefix tailTrace_1373
  have hstable : (prefixWord ++ tailWord_1373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373).length < 2 ^ (prefixWord ++ tailWord_1373).sum := by decide
  have hdescent : baseEnd_1373 < baseStart_1373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405 : List Nat := [1, 4, 1, 1, 2, 2, 3, 3, 3]
def baseStart_1405 : Nat := 118140960795 + 1405 * 2 ^ 59
def prefixEnd_1405 : Nat := 4983230072969 + 3 ^ 40 * 1405 * 2
def baseEnd_1405 : Nat := 641280284153099227595

theorem tailTrace_1405 : CollatzResearch.WordTrace tailWord_1405 prefixEnd_1405 641280284153099227595 := by
  unfold tailWord_1405
  simp only [CollatzResearch.WordTrace]
  refine ⟨51244559917399800005669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34163039944933200003779 51244559917399800005669)
  ·
    refine ⟨9608354984512462501063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51244559917399800005669 9608354984512462501063)
    ·
      refine ⟨14412532476768693751595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9608354984512462501063 14412532476768693751595)
      ·
        refine ⟨21618798715153040627393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14412532476768693751595 21618798715153040627393)
        ·
          refine ⟨16214099036364780470545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21618798715153040627393 16214099036364780470545)
          ·
            refine ⟨12160574277273585352909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16214099036364780470545 12160574277273585352909)
            ·
              refine ⟨4560215353977594507341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12160574277273585352909 4560215353977594507341)
              ·
                refine ⟨1710080757741597940253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4560215353977594507341 1710080757741597940253)
                ·
                  refine ⟨641280284153099227595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1710080757741597940253 641280284153099227595)
                  ·
                    rfl

theorem cell20_1405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_1405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1405 prefixEnd_1405 := by exact prefixLift 1405
  have htrace : WordTrace (prefixWord ++ tailWord_1405) baseStart_1405 baseEnd_1405 := by
    simpa [prefixWord, tailWord_1405, baseEnd_1405] using wordTrace_append hprefix tailTrace_1405
  have hstable : (prefixWord ++ tailWord_1405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405).length < 2 ^ (prefixWord ++ tailWord_1405).sum := by decide
  have hdescent : baseEnd_1405 < baseStart_1405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436 : List Nat := [2, 2, 3, 4, 1, 8]
def baseStart_1436 : Nat := 118140960795 + 1436 * 2 ^ 59
def prefixEnd_1436 : Nat := 4983230072969 + 3 ^ 40 * 1436 * 2
def baseEnd_1436 : Nat := 24275167735361822005

theorem tailTrace_1436 : CollatzResearch.WordTrace tailWord_1436 prefixEnd_1436 24275167735361822005 := by
  unfold tailWord_1436
  simp only [CollatzResearch.WordTrace]
  refine ⟨26187611402546047192081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34916815203394729589441 26187611402546047192081)
  ·
    refine ⟨19640708551909535394061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26187611402546047192081 19640708551909535394061)
    ·
      refine ⟨7365265706966075772773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19640708551909535394061 7365265706966075772773)
      ·
        refine ⟨1380987320056139207395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7365265706966075772773 1380987320056139207395)
        ·
          refine ⟨2071480980084208811093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1380987320056139207395 2071480980084208811093)
          ·
            refine ⟨24275167735361822005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 2071480980084208811093 24275167735361822005)
            ·
              rfl

theorem cell20_1436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 8].length) (baseStart_1436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1436 prefixEnd_1436 := by exact prefixLift 1436
  have htrace : WordTrace (prefixWord ++ tailWord_1436) baseStart_1436 baseEnd_1436 := by
    simpa [prefixWord, tailWord_1436, baseEnd_1436] using wordTrace_append hprefix tailTrace_1436
  have hstable : (prefixWord ++ tailWord_1436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436).length < 2 ^ (prefixWord ++ tailWord_1436).sum := by decide
  have hdescent : baseEnd_1436 < baseStart_1436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443 : List Nat := [1, 1, 1, 4, 1, 3, 4, 2, 3]
def baseStart_1443 : Nat := 118140960795 + 1443 * 2 ^ 59
def prefixEnd_1443 : Nat := 4983230072969 + 3 ^ 40 * 1443 * 2
def baseEnd_1443 : Nat := 658624519593855960773

theorem tailTrace_1443 : CollatzResearch.WordTrace tailWord_1443 prefixEnd_1443 658624519593855960773 := by
  unfold tailWord_1443
  simp only [CollatzResearch.WordTrace]
  refine ⟨52630533779732289888983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35087022519821526592655 52630533779732289888983)
  ·
    refine ⟨78945800669598434833475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52630533779732289888983 78945800669598434833475)
    ·
      refine ⟨118418701004397652250213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78945800669598434833475 118418701004397652250213)
      ·
        refine ⟨22203506438324559796915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118418701004397652250213 22203506438324559796915)
        ·
          refine ⟨33305259657486839695373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22203506438324559796915 33305259657486839695373)
          ·
            refine ⟨12489472371557564885765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33305259657486839695373 12489472371557564885765)
            ·
              refine ⟨2341776069667043416081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12489472371557564885765 2341776069667043416081)
              ·
                refine ⟨1756332052250282562061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2341776069667043416081 1756332052250282562061)
                ·
                  refine ⟨658624519593855960773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1756332052250282562061 658624519593855960773)
                  ·
                    rfl

theorem cell20_1443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 3].length) (baseStart_1443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1443 prefixEnd_1443 := by exact prefixLift 1443
  have htrace : WordTrace (prefixWord ++ tailWord_1443) baseStart_1443 baseEnd_1443 := by
    simpa [prefixWord, tailWord_1443, baseEnd_1443] using wordTrace_append hprefix tailTrace_1443
  have hstable : (prefixWord ++ tailWord_1443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443).length < 2 ^ (prefixWord ++ tailWord_1443).sum := by decide
  have hdescent : baseEnd_1443 < baseStart_1443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453 : List Nat := [1, 5, 2, 2, 1, 3, 1, 5]
def baseStart_1453 : Nat := 118140960795 + 1453 * 2 ^ 59
def prefixEnd_1453 : Nat := 4983230072969 + 3 ^ 40 * 1453 * 2
def baseEnd_1453 : Nat := 221062930692755209133

theorem tailTrace_1453 : CollatzResearch.WordTrace tailWord_1453 prefixEnd_1453 221062930692755209133 := by
  unfold tailWord_1453
  simp only [CollatzResearch.WordTrace]
  refine ⟨52995263743503997753013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35330175829002665168675 52995263743503997753013)
  ·
    refine ⟨4968305975953499789345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52995263743503997753013 4968305975953499789345)
    ·
      refine ⟨3726229481965124842009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4968305975953499789345 3726229481965124842009)
      ·
        refine ⟨2794672111473843631507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3726229481965124842009 2794672111473843631507)
        ·
          refine ⟨4192008167210765447261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2794672111473843631507 4192008167210765447261)
          ·
            refine ⟨1572003062704037042723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4192008167210765447261 1572003062704037042723)
            ·
              refine ⟨2358004594056055564085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1572003062704037042723 2358004594056055564085)
              ·
                refine ⟨221062930692755209133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2358004594056055564085 221062930692755209133)
                ·
                  rfl

theorem cell20_1453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 5].length) (baseStart_1453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1453 prefixEnd_1453 := by exact prefixLift 1453
  have htrace : WordTrace (prefixWord ++ tailWord_1453) baseStart_1453 baseEnd_1453 := by
    simpa [prefixWord, tailWord_1453, baseEnd_1453] using wordTrace_append hprefix tailTrace_1453
  have hstable : (prefixWord ++ tailWord_1453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453).length < 2 ^ (prefixWord ++ tailWord_1453).sum := by decide
  have hdescent : baseEnd_1453 < baseStart_1453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484 : List Nat := [2, 2, 1, 4, 2, 2, 2, 3, 2]
def baseStart_1484 : Nat := 118140960795 + 1484 * 2 ^ 59
def prefixEnd_1484 : Nat := 4983230072969 + 3 ^ 40 * 1484 * 2
def baseEnd_1484 : Nat := 677338036779935593939

theorem tailTrace_1484 : CollatzResearch.WordTrace tailWord_1484 prefixEnd_1484 677338036779935593939 := by
  unfold tailWord_1484
  simp only [CollatzResearch.WordTrace]
  refine ⟨27062963315598146065753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36083951087464194754337 27062963315598146065753)
  ·
    refine ⟨20297222486698609549315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27062963315598146065753 20297222486698609549315)
    ·
      refine ⟨30445833730047914323973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20297222486698609549315 30445833730047914323973)
      ·
        refine ⟨5708593824383983935745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30445833730047914323973 5708593824383983935745)
        ·
          refine ⟨4281445368287987951809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5708593824383983935745 4281445368287987951809)
          ·
            refine ⟨3211084026215990963857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4281445368287987951809 3211084026215990963857)
            ·
              refine ⟨2408313019661993222893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3211084026215990963857 2408313019661993222893)
              ·
                refine ⟨903117382373247458585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2408313019661993222893 903117382373247458585)
                ·
                  refine ⟨677338036779935593939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 903117382373247458585 677338036779935593939)
                  ·
                    rfl

theorem cell20_1484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 2].length) (baseStart_1484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1484 prefixEnd_1484 := by exact prefixLift 1484
  have htrace : WordTrace (prefixWord ++ tailWord_1484) baseStart_1484 baseEnd_1484 := by
    simpa [prefixWord, tailWord_1484, baseEnd_1484] using wordTrace_append hprefix tailTrace_1484
  have hstable : (prefixWord ++ tailWord_1484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484).length < 2 ^ (prefixWord ++ tailWord_1484).sum := by decide
  have hdescent : baseEnd_1484 < baseStart_1484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498 : List Nat := [3, 1, 1, 2, 3, 4, 1, 2, 3]
def baseStart_1498 : Nat := 118140960795 + 1498 * 2 ^ 59
def prefixEnd_1498 : Nat := 4983230072969 + 3 ^ 40 * 1498 * 2
def baseEnd_1498 : Nat := 683728018258109127215

theorem tailTrace_1498 : CollatzResearch.WordTrace tailWord_1498 prefixEnd_1498 683728018258109127215 := by
  unfold tailWord_1498
  simp only [CollatzResearch.WordTrace]
  refine ⟨13659137145119170785287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36424365720317788760765 13659137145119170785287)
  ·
    refine ⟨20488705717678756177931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13659137145119170785287 20488705717678756177931)
    ·
      refine ⟨30733058576518134266897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20488705717678756177931 30733058576518134266897)
      ·
        refine ⟨23049793932388600700173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30733058576518134266897 23049793932388600700173)
        ·
          refine ⟨8643672724645725262565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23049793932388600700173 8643672724645725262565)
          ·
            refine ⟨1620688635871073486731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8643672724645725262565 1620688635871073486731)
            ·
              refine ⟨2431032953806610230097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1620688635871073486731 2431032953806610230097)
              ·
                refine ⟨1823274715354957672573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2431032953806610230097 1823274715354957672573)
                ·
                  refine ⟨683728018258109127215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1823274715354957672573 683728018258109127215)
                  ·
                    rfl

theorem cell20_1498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_1498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1498 prefixEnd_1498 := by exact prefixLift 1498
  have htrace : WordTrace (prefixWord ++ tailWord_1498) baseStart_1498 baseEnd_1498 := by
    simpa [prefixWord, tailWord_1498, baseEnd_1498] using wordTrace_append hprefix tailTrace_1498
  have hstable : (prefixWord ++ tailWord_1498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498).length < 2 ^ (prefixWord ++ tailWord_1498).sum := by decide
  have hdescent : baseEnd_1498 < baseStart_1498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505 : List Nat := [1, 2, 3, 1, 2, 3, 2, 4, 2]
def baseStart_1505 : Nat := 118140960795 + 1505 * 2 ^ 59
def prefixEnd_1505 : Nat := 4983230072969 + 3 ^ 40 * 1505 * 2
def baseEnd_1505 : Nat := 686923008997195893853

theorem tailTrace_1505 : CollatzResearch.WordTrace tailWord_1505 prefixEnd_1505 686923008997195893853 := by
  unfold tailWord_1505
  simp only [CollatzResearch.WordTrace]
  refine ⟨54891859555116878645969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36594573036744585763979 54891859555116878645969)
  ·
    refine ⟨41168894666337658984477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54891859555116878645969 41168894666337658984477)
    ·
      refine ⟨15438335499876622119179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41168894666337658984477 15438335499876622119179)
      ·
        refine ⟨23157503249814933178769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15438335499876622119179 23157503249814933178769)
        ·
          refine ⟨17368127437361199884077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23157503249814933178769 17368127437361199884077)
          ·
            refine ⟨6513047789010449956529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17368127437361199884077 6513047789010449956529)
            ·
              refine ⟨4884785841757837467397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6513047789010449956529 4884785841757837467397)
              ·
                refine ⟨915897345329594525137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4884785841757837467397 915897345329594525137)
                ·
                  refine ⟨686923008997195893853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 915897345329594525137 686923008997195893853)
                  ·
                    rfl

theorem cell20_1505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 2].length) (baseStart_1505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1505 prefixEnd_1505 := by exact prefixLift 1505
  have htrace : WordTrace (prefixWord ++ tailWord_1505) baseStart_1505 baseEnd_1505 := by
    simpa [prefixWord, tailWord_1505, baseEnd_1505] using wordTrace_append hprefix tailTrace_1505
  have hstable : (prefixWord ++ tailWord_1505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505).length < 2 ^ (prefixWord ++ tailWord_1505).sum := by decide
  have hdescent : baseEnd_1505 < baseStart_1505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533 : List Nat := [1, 4, 1, 1, 1, 5, 1, 6]
def baseStart_1533 : Nat := 118140960795 + 1533 * 2 ^ 59
def prefixEnd_1533 : Nat := 4983230072969 + 3 ^ 40 * 1533 * 2
def baseEnd_1533 : Nat := 233234323984514320135

theorem tailTrace_1533 : CollatzResearch.WordTrace tailWord_1533 prefixEnd_1533 233234323984514320135 := by
  unfold tailWord_1533
  simp only [CollatzResearch.WordTrace]
  refine ⟨55913103453677660665253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37275402302451773776835 55913103453677660665253)
  ·
    refine ⟨10483706897564561374735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55913103453677660665253 10483706897564561374735)
    ·
      refine ⟨15725560346346842062103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10483706897564561374735 15725560346346842062103)
      ·
        refine ⟨23588340519520263093155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15725560346346842062103 23588340519520263093155)
        ·
          refine ⟨35382510779280394639733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23588340519520263093155 35382510779280394639733)
          ·
            refine ⟨3317110385557536997475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35382510779280394639733 3317110385557536997475)
            ·
              refine ⟨4975665578336305496213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3317110385557536997475 4975665578336305496213)
              ·
                refine ⟨233234323984514320135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4975665578336305496213 233234323984514320135)
                ·
                  rfl

theorem cell20_1533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 6].length) (baseStart_1533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1533 prefixEnd_1533 := by exact prefixLift 1533
  have htrace : WordTrace (prefixWord ++ tailWord_1533) baseStart_1533 baseEnd_1533 := by
    simpa [prefixWord, tailWord_1533, baseEnd_1533] using wordTrace_append hprefix tailTrace_1533
  have hstable : (prefixWord ++ tailWord_1533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533).length < 2 ^ (prefixWord ++ tailWord_1533).sum := by decide
  have hdescent : baseEnd_1533 < baseStart_1533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550 : List Nat := [4, 1, 1, 2, 4, 2, 6]
def baseStart_1550 : Nat := 118140960795 + 1550 * 2 ^ 59
def prefixEnd_1550 : Nat := 4983230072969 + 3 ^ 40 * 1550 * 2
def baseEnd_1550 : Nat := 78606915019671043741

theorem tailTrace_1550 : CollatzResearch.WordTrace tailWord_1550 prefixEnd_1550 78606915019671043741 := by
  unfold tailWord_1550
  simp only [CollatzResearch.WordTrace]
  refine ⟨7066643049011195504263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37688762928059709356069 7066643049011195504263)
  ·
    refine ⟨10599964573516793256395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7066643049011195504263 10599964573516793256395)
    ·
      refine ⟨15899946860275189884593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10599964573516793256395 15899946860275189884593)
      ·
        refine ⟨11924960145206392413445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15899946860275189884593 11924960145206392413445)
        ·
          refine ⟨2235930027226198577521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11924960145206392413445 2235930027226198577521)
          ·
            refine ⟨1676947520419648933141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2235930027226198577521 1676947520419648933141)
            ·
              refine ⟨78606915019671043741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1676947520419648933141 78606915019671043741)
              ·
                rfl

theorem cell20_1550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 6].length) (baseStart_1550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1550 prefixEnd_1550 := by exact prefixLift 1550
  have htrace : WordTrace (prefixWord ++ tailWord_1550) baseStart_1550 baseEnd_1550 := by
    simpa [prefixWord, tailWord_1550, baseEnd_1550] using wordTrace_append hprefix tailTrace_1550
  have hstable : (prefixWord ++ tailWord_1550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550).length < 2 ^ (prefixWord ++ tailWord_1550).sum := by decide
  have hdescent : baseEnd_1550 < baseStart_1550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556 : List Nat := [2, 4, 3, 1, 2, 1, 3, 2, 2]
def baseStart_1556 : Nat := 118140960795 + 1556 * 2 ^ 59
def prefixEnd_1556 : Nat := 4983230072969 + 3 ^ 40 * 1556 * 2
def baseEnd_1556 : Nat := 710200798667685193645

theorem tailTrace_1556 : CollatzResearch.WordTrace tailWord_1556 prefixEnd_1556 710200798667685193645 := by
  unfold tailWord_1556
  simp only [CollatzResearch.WordTrace]
  refine ⟨28375991185176294376261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37834654913568392501681 28375991185176294376261)
  ·
    refine ⟨5320498347220555195549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28375991185176294376261 5320498347220555195549)
    ·
      refine ⟨1995186880207708198331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5320498347220555195549 1995186880207708198331)
      ·
        refine ⟨2992780320311562297497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1995186880207708198331 2992780320311562297497)
        ·
          refine ⟨2244585240233671723123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2992780320311562297497 2244585240233671723123)
          ·
            refine ⟨3366877860350507584685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2244585240233671723123 3366877860350507584685)
            ·
              refine ⟨1262579197631440344257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3366877860350507584685 1262579197631440344257)
              ·
                refine ⟨946934398223580258193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1262579197631440344257 946934398223580258193)
                ·
                  refine ⟨710200798667685193645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 946934398223580258193 710200798667685193645)
                  ·
                    rfl

theorem cell20_1556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_1556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1556 prefixEnd_1556 := by exact prefixLift 1556
  have htrace : WordTrace (prefixWord ++ tailWord_1556) baseStart_1556 baseEnd_1556 := by
    simpa [prefixWord, tailWord_1556, baseEnd_1556] using wordTrace_append hprefix tailTrace_1556
  have hstable : (prefixWord ++ tailWord_1556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556).length < 2 ^ (prefixWord ++ tailWord_1556).sum := by decide
  have hdescent : baseEnd_1556 < baseStart_1556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560 : List Nat := [2, 1, 2, 3, 5, 1, 1, 1, 4]
def baseStart_1560 : Nat := 118140960795 + 1560 * 2 ^ 59
def prefixEnd_1560 : Nat := 4983230072969 + 3 ^ 40 * 1560 * 2
def baseEnd_1560 : Nat := 712026507661449060295

theorem tailTrace_1560 : CollatzResearch.WordTrace tailWord_1560 prefixEnd_1560 712026507661449060295 := by
  unfold tailWord_1560
  simp only [CollatzResearch.WordTrace]
  refine ⟨28448937177930635949067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37931916237240847932089 28448937177930635949067)
  ·
    refine ⟨42673405766895953923601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28448937177930635949067 42673405766895953923601)
    ·
      refine ⟨32005054325171965442701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42673405766895953923601 32005054325171965442701)
      ·
        refine ⟨12001895371939487041013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32005054325171965442701 12001895371939487041013)
        ·
          refine ⟨1125177691119326910095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12001895371939487041013 1125177691119326910095)
          ·
            refine ⟨1687766536678990365143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125177691119326910095 1687766536678990365143)
            ·
              refine ⟨2531649805018485547715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1687766536678990365143 2531649805018485547715)
              ·
                refine ⟨3797474707527728321573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2531649805018485547715 3797474707527728321573)
                ·
                  refine ⟨712026507661449060295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3797474707527728321573 712026507661449060295)
                  ·
                    rfl

theorem cell20_1560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 4].length) (baseStart_1560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1560 prefixEnd_1560 := by exact prefixLift 1560
  have htrace : WordTrace (prefixWord ++ tailWord_1560) baseStart_1560 baseEnd_1560 := by
    simpa [prefixWord, tailWord_1560, baseEnd_1560] using wordTrace_append hprefix tailTrace_1560
  have hstable : (prefixWord ++ tailWord_1560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560).length < 2 ^ (prefixWord ++ tailWord_1560).sum := by decide
  have hdescent : baseEnd_1560 < baseStart_1560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566 : List Nat := [4, 3, 3, 1, 1, 2, 2, 1, 3]
def baseStart_1566 : Nat := 118140960795 + 1566 * 2 ^ 59
def prefixEnd_1566 : Nat := 4983230072969 + 3 ^ 40 * 1566 * 2
def baseEnd_1566 : Nat := 714765071152094860271

theorem tailTrace_1566 : CollatzResearch.WordTrace tailWord_1566 prefixEnd_1566 714765071152094860271 := by
  unfold tailWord_1566
  simp only [CollatzResearch.WordTrace]
  refine ⟨7139589041765537077069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38077808222749531077701 7139589041765537077069)
  ·
    refine ⟨2677345890662076403901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7139589041765537077069 2677345890662076403901)
    ·
      refine ⟨1004004708998278651463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2677345890662076403901 1004004708998278651463)
      ·
        refine ⟨1506007063497417977195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1004004708998278651463 1506007063497417977195)
        ·
          refine ⟨2259010595246126965793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1506007063497417977195 2259010595246126965793)
          ·
            refine ⟨1694257946434595224345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2259010595246126965793 1694257946434595224345)
            ·
              refine ⟨1270693459825946418259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1694257946434595224345 1270693459825946418259)
              ·
                refine ⟨1906040189738919627389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1270693459825946418259 1906040189738919627389)
                ·
                  refine ⟨714765071152094860271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1906040189738919627389 714765071152094860271)
                  ·
                    rfl

theorem cell20_1566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_1566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1566 prefixEnd_1566 := by exact prefixLift 1566
  have htrace : WordTrace (prefixWord ++ tailWord_1566) baseStart_1566 baseEnd_1566 := by
    simpa [prefixWord, tailWord_1566, baseEnd_1566] using wordTrace_append hprefix tailTrace_1566
  have hstable : (prefixWord ++ tailWord_1566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566).length < 2 ^ (prefixWord ++ tailWord_1566).sum := by decide
  have hdescent : baseEnd_1566 < baseStart_1566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 6]
def baseStart_1585 : Nat := 118140960795 + 1585 * 2 ^ 59
def prefixEnd_1585 : Nat := 4983230072969 + 3 ^ 40 * 1585 * 2
def baseEnd_1585 : Nat := 723437188872473226859

theorem tailTrace_1585 : CollatzResearch.WordTrace tailWord_1585 prefixEnd_1585 723437188872473226859 := by
  unfold tailWord_1585
  simp only [CollatzResearch.WordTrace]
  refine ⟨57809699265290541558209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38539799510193694372139 57809699265290541558209)
  ·
    refine ⟨43357274448967906168657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57809699265290541558209 43357274448967906168657)
    ·
      refine ⟨32517955836725929626493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43357274448967906168657 32517955836725929626493)
      ·
        refine ⟨12194233438772223609935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32517955836725929626493 12194233438772223609935)
        ·
          refine ⟨18291350158158335414903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12194233438772223609935 18291350158158335414903)
          ·
            refine ⟨27437025237237503122355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18291350158158335414903 27437025237237503122355)
            ·
              refine ⟨41155537855856254683533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27437025237237503122355 41155537855856254683533)
              ·
                refine ⟨15433326695946095506325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41155537855856254683533 15433326695946095506325)
                ·
                  refine ⟨723437188872473226859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15433326695946095506325 723437188872473226859)
                  ·
                    rfl

theorem cell20_1585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_1585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1585 prefixEnd_1585 := by exact prefixLift 1585
  have htrace : WordTrace (prefixWord ++ tailWord_1585) baseStart_1585 baseEnd_1585 := by
    simpa [prefixWord, tailWord_1585, baseEnd_1585] using wordTrace_append hprefix tailTrace_1585
  have hstable : (prefixWord ++ tailWord_1585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585).length < 2 ^ (prefixWord ++ tailWord_1585).sum := by decide
  have hdescent : baseEnd_1585 < baseStart_1585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 6]
def baseStart_1640 : Nat := 118140960795 + 1640 * 2 ^ 59
def prefixEnd_1640 : Nat := 4983230072969 + 3 ^ 40 * 1640 * 2
def baseEnd_1640 : Nat := 748540687536726393301

theorem tailTrace_1640 : CollatzResearch.WordTrace tailWord_1640 prefixEnd_1640 748540687536726393301 := by
  unfold tailWord_1640
  simp only [CollatzResearch.WordTrace]
  refine ⟨29907857033017467405187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39877142710689956540249 29907857033017467405187)
  ·
    refine ⟨44861785549526201107781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29907857033017467405187 44861785549526201107781)
    ·
      refine ⟨8411584790536162707709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44861785549526201107781 8411584790536162707709)
      ·
        refine ⟨3154344296451061015391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8411584790536162707709 3154344296451061015391)
        ·
          refine ⟨4731516444676591523087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3154344296451061015391 4731516444676591523087)
          ·
            refine ⟨7097274667014887284631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4731516444676591523087 7097274667014887284631)
            ·
              refine ⟨10645912000522330926947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7097274667014887284631 10645912000522330926947)
              ·
                refine ⟨15968868000783496390421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10645912000522330926947 15968868000783496390421)
                ·
                  refine ⟨748540687536726393301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15968868000783496390421 748540687536726393301)
                  ·
                    rfl

theorem cell20_1640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_1640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1640 prefixEnd_1640 := by exact prefixLift 1640
  have htrace : WordTrace (prefixWord ++ tailWord_1640) baseStart_1640 baseEnd_1640 := by
    simpa [prefixWord, tailWord_1640, baseEnd_1640] using wordTrace_append hprefix tailTrace_1640
  have hstable : (prefixWord ++ tailWord_1640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640).length < 2 ^ (prefixWord ++ tailWord_1640).sum := by decide
  have hdescent : baseEnd_1640 < baseStart_1640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657 : List Nat := [1, 2, 1, 3, 3, 1, 4, 3, 2]
def baseStart_1657 : Nat := 118140960795 + 1657 * 2 ^ 59
def prefixEnd_1657 : Nat := 4983230072969 + 3 ^ 40 * 1657 * 2
def baseEnd_1657 : Nat := 756299950760222826565

theorem tailTrace_1657 : CollatzResearch.WordTrace tailWord_1657 prefixEnd_1657 756299950760222826565 := by
  unfold tailWord_1657
  simp only [CollatzResearch.WordTrace]
  refine ⟨60435755004446838179225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40290503336297892119483 60435755004446838179225)
  ·
    refine ⟨45326816253335128634419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60435755004446838179225 45326816253335128634419)
    ·
      refine ⟨67990224380002692951629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45326816253335128634419 67990224380002692951629)
      ·
        refine ⟨25496334142501009856861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67990224380002692951629 25496334142501009856861)
        ·
          refine ⟨9561125303437878696323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25496334142501009856861 9561125303437878696323)
          ·
            refine ⟨14341687955156818044485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9561125303437878696323 14341687955156818044485)
            ·
              refine ⟨2689066491591903383341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14341687955156818044485 2689066491591903383341)
              ·
                refine ⟨1008399934346963768753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2689066491591903383341 1008399934346963768753)
                ·
                  refine ⟨756299950760222826565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1008399934346963768753 756299950760222826565)
                  ·
                    rfl

theorem cell20_1657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 2].length) (baseStart_1657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1657 prefixEnd_1657 := by exact prefixLift 1657
  have htrace : WordTrace (prefixWord ++ tailWord_1657) baseStart_1657 baseEnd_1657 := by
    simpa [prefixWord, tailWord_1657, baseEnd_1657] using wordTrace_append hprefix tailTrace_1657
  have hstable : (prefixWord ++ tailWord_1657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657).length < 2 ^ (prefixWord ++ tailWord_1657).sum := by decide
  have hdescent : baseEnd_1657 < baseStart_1657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671 : List Nat := [1, 1, 4, 2, 1, 3, 3, 2, 3]
def baseStart_1671 : Nat := 118140960795 + 1671 * 2 ^ 59
def prefixEnd_1671 : Nat := 4983230072969 + 3 ^ 40 * 1671 * 2
def baseEnd_1671 : Nat := 762689932238396359841

theorem tailTrace_1671 : CollatzResearch.WordTrace tailWord_1671 prefixEnd_1671 762689932238396359841 := by
  unfold tailWord_1671
  simp only [CollatzResearch.WordTrace]
  refine ⟨60946376953727229188867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40630917969151486125911 60946376953727229188867)
  ·
    refine ⟨91419565430590843783301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60946376953727229188867 91419565430590843783301)
    ·
      refine ⟨17141168518235783209369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91419565430590843783301 17141168518235783209369)
      ·
        refine ⟨12855876388676837407027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17141168518235783209369 12855876388676837407027)
        ·
          refine ⟨19283814583015256110541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12855876388676837407027 19283814583015256110541)
          ·
            refine ⟨7231430468630721041453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19283814583015256110541 7231430468630721041453)
            ·
              refine ⟨2711786425736520390545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7231430468630721041453 2711786425736520390545)
              ·
                refine ⟨2033839819302390292909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2711786425736520390545 2033839819302390292909)
                ·
                  refine ⟨762689932238396359841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2033839819302390292909 762689932238396359841)
                  ·
                    rfl

theorem cell20_1671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 3].length) (baseStart_1671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1671 prefixEnd_1671 := by exact prefixLift 1671
  have htrace : WordTrace (prefixWord ++ tailWord_1671) baseStart_1671 baseEnd_1671 := by
    simpa [prefixWord, tailWord_1671, baseEnd_1671] using wordTrace_append hprefix tailTrace_1671
  have hstable : (prefixWord ++ tailWord_1671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671).length < 2 ^ (prefixWord ++ tailWord_1671).sum := by decide
  have hdescent : baseEnd_1671 < baseStart_1671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678 : List Nat := [4, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_1678 : Nat := 118140960795 + 1678 * 2 ^ 59
def prefixEnd_1678 : Nat := 4983230072969 + 3 ^ 40 * 1678 * 2
def baseEnd_1678 : Nat := 765884922977483126479

theorem tailTrace_1678 : CollatzResearch.WordTrace tailWord_1678 prefixEnd_1678 765884922977483126479 := by
  unfold tailWord_1678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7650210991045928086711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40801125285578283129125 7650210991045928086711)
  ·
    refine ⟨11475316486568892130067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7650210991045928086711 11475316486568892130067)
    ·
      refine ⟨17212974729853338195101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11475316486568892130067 17212974729853338195101)
      ·
        refine ⟨6454865523695001823163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17212974729853338195101 6454865523695001823163)
        ·
          refine ⟨9682298285542502734745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6454865523695001823163 9682298285542502734745)
          ·
            refine ⟨7261723714156877051059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9682298285542502734745 7261723714156877051059)
            ·
              refine ⟨10892585571235315576589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7261723714156877051059 10892585571235315576589)
              ·
                refine ⟨4084719589213243341221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10892585571235315576589 4084719589213243341221)
                ·
                  refine ⟨765884922977483126479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4084719589213243341221 765884922977483126479)
                  ·
                    rfl

theorem cell20_1678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_1678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1678 prefixEnd_1678 := by exact prefixLift 1678
  have htrace : WordTrace (prefixWord ++ tailWord_1678) baseStart_1678 baseEnd_1678 := by
    simpa [prefixWord, tailWord_1678, baseEnd_1678] using wordTrace_append hprefix tailTrace_1678
  have hstable : (prefixWord ++ tailWord_1678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678).length < 2 ^ (prefixWord ++ tailWord_1678).sum := by decide
  have hdescent : baseEnd_1678 < baseStart_1678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688 : List Nat := [2, 1, 2, 4, 1, 3, 3, 1, 3]
def baseStart_1688 : Nat := 118140960795 + 1688 * 2 ^ 59
def prefixEnd_1688 : Nat := 4983230072969 + 3 ^ 40 * 1688 * 2
def baseEnd_1688 : Nat := 770449195461892793105

theorem tailTrace_1688 : CollatzResearch.WordTrace tailWord_1688 prefixEnd_1688 770449195461892793105 := by
  unfold tailWord_1688
  simp only [CollatzResearch.WordTrace]
  refine ⟨30783208946069566278859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41044278594759421705145 30783208946069566278859)
  ·
    refine ⟨46174813419104349418289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30783208946069566278859 46174813419104349418289)
    ·
      refine ⟨34631110064328262063717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46174813419104349418289 34631110064328262063717)
      ·
        refine ⟨6493333137061549136947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34631110064328262063717 6493333137061549136947)
        ·
          refine ⟨9739999705592323705421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6493333137061549136947 9739999705592323705421)
          ·
            refine ⟨3652499889597121389533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9739999705592323705421 3652499889597121389533)
            ·
              refine ⟨1369687458598920521075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3652499889597121389533 1369687458598920521075)
              ·
                refine ⟨2054531187898380781613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1369687458598920521075 2054531187898380781613)
                ·
                  refine ⟨770449195461892793105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2054531187898380781613 770449195461892793105)
                  ·
                    rfl

theorem cell20_1688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 3].length) (baseStart_1688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1688 prefixEnd_1688 := by exact prefixLift 1688
  have htrace : WordTrace (prefixWord ++ tailWord_1688) baseStart_1688 baseEnd_1688 := by
    simpa [prefixWord, tailWord_1688, baseEnd_1688] using wordTrace_append hprefix tailTrace_1688
  have hstable : (prefixWord ++ tailWord_1688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688).length < 2 ^ (prefixWord ++ tailWord_1688).sum := by decide
  have hdescent : baseEnd_1688 < baseStart_1688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698 : List Nat := [3, 3, 1, 4, 1, 2, 2, 4]
def baseStart_1698 : Nat := 118140960795 + 1698 * 2 ^ 59
def prefixEnd_1698 : Nat := 4983230072969 + 3 ^ 40 * 1698 * 2
def baseEnd_1698 : Nat := 258337822648767486577

theorem tailTrace_1698 : CollatzResearch.WordTrace tailWord_1698 prefixEnd_1698 258337822648767486577 := by
  unfold tailWord_1698
  simp only [CollatzResearch.WordTrace]
  refine ⟨15482786963977710105437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41287431903940560281165 15482786963977710105437)
  ·
    refine ⟨5806045111491641289539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15482786963977710105437 5806045111491641289539)
    ·
      refine ⟨8709067667237461934309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5806045111491641289539 8709067667237461934309)
      ·
        refine ⟨1632950187607024112683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8709067667237461934309 1632950187607024112683)
        ·
          refine ⟨2449425281410536169025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1632950187607024112683 2449425281410536169025)
          ·
            refine ⟨1837068961057902126769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2449425281410536169025 1837068961057902126769)
            ·
              refine ⟨1377801720793426595077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1837068961057902126769 1377801720793426595077)
              ·
                refine ⟨258337822648767486577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1377801720793426595077 258337822648767486577)
                ·
                  rfl

theorem cell20_1698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_1698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1698 prefixEnd_1698 := by exact prefixLift 1698
  have htrace : WordTrace (prefixWord ++ tailWord_1698) baseStart_1698 baseEnd_1698 := by
    simpa [prefixWord, tailWord_1698, baseEnd_1698] using wordTrace_append hprefix tailTrace_1698
  have hstable : (prefixWord ++ tailWord_1698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698).length < 2 ^ (prefixWord ++ tailWord_1698).sum := by decide
  have hdescent : baseEnd_1698 < baseStart_1698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699 : List Nat := [1, 1, 1, 4, 1, 1, 3, 4, 4]
def baseStart_1699 : Nat := 118140960795 + 1699 * 2 ^ 59
def prefixEnd_1699 : Nat := 4983230072969 + 3 ^ 40 * 1699 * 2
def baseEnd_1699 : Nat := 775469895194743426393

theorem tailTrace_1699 : CollatzResearch.WordTrace tailWord_1699 prefixEnd_1699 775469895194743426393 := by
  unfold tailWord_1699
  simp only [CollatzResearch.WordTrace]
  refine ⟨61967620852288011208151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41311747234858674138767 61967620852288011208151)
  ·
    refine ⟨92951431278432016812227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61967620852288011208151 92951431278432016812227)
    ·
      refine ⟨139427146917648025218341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92951431278432016812227 139427146917648025218341)
      ·
        refine ⟨26142590047059004728439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139427146917648025218341 26142590047059004728439)
        ·
          refine ⟨39213885070588507092659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26142590047059004728439 39213885070588507092659)
          ·
            refine ⟨58820827605882760638989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39213885070588507092659 58820827605882760638989)
            ·
              refine ⟨22057810352206035239621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58820827605882760638989 22057810352206035239621)
              ·
                refine ⟨4135839441038631607429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22057810352206035239621 4135839441038631607429)
                ·
                  refine ⟨775469895194743426393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4135839441038631607429 775469895194743426393)
                  ·
                    rfl

theorem cell20_1699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 4].length) (baseStart_1699 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1699 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1699 prefixEnd_1699 := by exact prefixLift 1699
  have htrace : WordTrace (prefixWord ++ tailWord_1699) baseStart_1699 baseEnd_1699 := by
    simpa [prefixWord, tailWord_1699, baseEnd_1699] using wordTrace_append hprefix tailTrace_1699
  have hstable : (prefixWord ++ tailWord_1699).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699).length < 2 ^ (prefixWord ++ tailWord_1699).sum := by decide
  have hdescent : baseEnd_1699 < baseStart_1699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740 : List Nat := [2, 2, 1, 5, 2, 1, 2, 5]
def baseStart_1740 : Nat := 118140960795 + 1740 * 2 ^ 59
def prefixEnd_1740 : Nat := 4983230072969 + 3 ^ 40 * 1740 * 2
def baseEnd_1740 : Nat := 264727804126941019853

theorem tailTrace_1740 : CollatzResearch.WordTrace tailWord_1740 prefixEnd_1740 264727804126941019853 := by
  unfold tailWord_1740
  simp only [CollatzResearch.WordTrace]
  refine ⟨31731506851876006725337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42308675802501342300449 31731506851876006725337)
  ·
    refine ⟨23798630138907005044003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31731506851876006725337 23798630138907005044003)
    ·
      refine ⟨35697945208360507566005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23798630138907005044003 35697945208360507566005)
      ·
        refine ⟨3346682363283797584313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35697945208360507566005 3346682363283797584313)
        ·
          refine ⟨2510011772462848188235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3346682363283797584313 2510011772462848188235)
          ·
            refine ⟨3765017658694272282353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2510011772462848188235 3765017658694272282353)
            ·
              refine ⟨2823763244020704211765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3765017658694272282353 2823763244020704211765)
              ·
                refine ⟨264727804126941019853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2823763244020704211765 264727804126941019853)
                ·
                  rfl

theorem cell20_1740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 5].length) (baseStart_1740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1740 prefixEnd_1740 := by exact prefixLift 1740
  have htrace : WordTrace (prefixWord ++ tailWord_1740) baseStart_1740 baseEnd_1740 := by
    simpa [prefixWord, tailWord_1740, baseEnd_1740] using wordTrace_append hprefix tailTrace_1740
  have hstable : (prefixWord ++ tailWord_1740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740).length < 2 ^ (prefixWord ++ tailWord_1740).sum := by decide
  have hdescent : baseEnd_1740 < baseStart_1740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792 : List Nat := [2, 1, 1, 2, 1, 1, 2, 8, 2]
def baseStart_1792 : Nat := 118140960795 + 1792 * 2 ^ 59
def prefixEnd_1792 : Nat := 4983230072969 + 3 ^ 40 * 1792 * 2
def baseEnd_1792 : Nat := 817917629299753326013

theorem tailTrace_1792 : CollatzResearch.WordTrace tailWord_1792 prefixEnd_1792 817917629299753326013 := by
  unfold tailWord_1792
  simp only [CollatzResearch.WordTrace]
  refine ⟨32679804757682447171815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43573073010243262895753 32679804757682447171815)
  ·
    refine ⟨49019707136523670757723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32679804757682447171815 49019707136523670757723)
    ·
      refine ⟨73529560704785506136585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49019707136523670757723 73529560704785506136585)
      ·
        refine ⟨55147170528589129602439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73529560704785506136585 55147170528589129602439)
        ·
          refine ⟨82720755792883694403659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55147170528589129602439 82720755792883694403659)
          ·
            refine ⟨124081133689325541605489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82720755792883694403659 124081133689325541605489)
            ·
              refine ⟨93060850266994156204117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124081133689325541605489 93060850266994156204117)
              ·
                refine ⟨1090556839066337768017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 93060850266994156204117 1090556839066337768017)
                ·
                  refine ⟨817917629299753326013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1090556839066337768017 817917629299753326013)
                  ·
                    rfl

theorem cell20_1792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 2].length) (baseStart_1792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1792 prefixEnd_1792 := by exact prefixLift 1792
  have htrace : WordTrace (prefixWord ++ tailWord_1792) baseStart_1792 baseEnd_1792 := by
    simpa [prefixWord, tailWord_1792, baseEnd_1792] using wordTrace_append hprefix tailTrace_1792
  have hstable : (prefixWord ++ tailWord_1792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792).length < 2 ^ (prefixWord ++ tailWord_1792).sum := by decide
  have hdescent : baseEnd_1792 < baseStart_1792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 6]
def baseStart_1813 : Nat := 118140960795 + 1813 * 2 ^ 59
def prefixEnd_1813 : Nat := 4983230072969 + 3 ^ 40 * 1813 * 2
def baseEnd_1813 : Nat := 827502601517013625927

theorem tailTrace_1813 : CollatzResearch.WordTrace tailWord_1813 prefixEnd_1813 827502601517013625927 := by
  unfold tailWord_1813
  simp only [CollatzResearch.WordTrace]
  refine ⟨66125542439285480858093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44083694959523653905395 66125542439285480858093)
  ·
    refine ⟨24797078414732055321785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66125542439285480858093 24797078414732055321785)
    ·
      refine ⟨18597808811049041491339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24797078414732055321785 18597808811049041491339)
      ·
        refine ⟨27896713216573562237009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18597808811049041491339 27896713216573562237009)
        ·
          refine ⟨20922534912430171677757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27896713216573562237009 20922534912430171677757)
          ·
            refine ⟨7845950592161314379159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20922534912430171677757 7845950592161314379159)
            ·
              refine ⟨11768925888241971568739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7845950592161314379159 11768925888241971568739)
              ·
                refine ⟨17653388832362957353109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11768925888241971568739 17653388832362957353109)
                ·
                  refine ⟨827502601517013625927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17653388832362957353109 827502601517013625927)
                  ·
                    rfl

theorem cell20_1813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_1813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1813 prefixEnd_1813 := by exact prefixLift 1813
  have htrace : WordTrace (prefixWord ++ tailWord_1813) baseStart_1813 baseEnd_1813 := by
    simpa [prefixWord, tailWord_1813, baseEnd_1813] using wordTrace_append hprefix tailTrace_1813
  have hstable : (prefixWord ++ tailWord_1813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813).length < 2 ^ (prefixWord ++ tailWord_1813).sum := by decide
  have hdescent : baseEnd_1813 < baseStart_1813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822 : List Nat := [4, 3, 2, 2, 1, 1, 2, 3, 2]
def baseStart_1822 : Nat := 118140960795 + 1822 * 2 ^ 59
def prefixEnd_1822 : Nat := 4983230072969 + 3 ^ 40 * 1822 * 2
def baseEnd_1822 : Nat := 831610446752982325891

theorem tailTrace_1822 : CollatzResearch.WordTrace tailWord_1822 prefixEnd_1822 831610446752982325891 := by
  unfold tailWord_1822
  simp only [CollatzResearch.WordTrace]
  refine ⟨8306724925835002241965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44302532937786678623813 8306724925835002241965)
  ·
    refine ⟨3115021847188125840737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8306724925835002241965 3115021847188125840737)
    ·
      refine ⟨2336266385391094380553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3115021847188125840737 2336266385391094380553)
      ·
        refine ⟨1752199789043320785415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2336266385391094380553 1752199789043320785415)
        ·
          refine ⟨2628299683564981178123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1752199789043320785415 2628299683564981178123)
          ·
            refine ⟨3942449525347471767185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2628299683564981178123 3942449525347471767185)
            ·
              refine ⟨2956837144010603825389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3942449525347471767185 2956837144010603825389)
              ·
                refine ⟨1108813929003976434521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2956837144010603825389 1108813929003976434521)
                ·
                  refine ⟨831610446752982325891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1108813929003976434521 831610446752982325891)
                  ·
                    rfl

theorem cell20_1822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_1822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1822 prefixEnd_1822 := by exact prefixLift 1822
  have htrace : WordTrace (prefixWord ++ tailWord_1822) baseStart_1822 baseEnd_1822 := by
    simpa [prefixWord, tailWord_1822, baseEnd_1822] using wordTrace_append hprefix tailTrace_1822
  have hstable : (prefixWord ++ tailWord_1822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822).length < 2 ^ (prefixWord ++ tailWord_1822).sum := by decide
  have hdescent : baseEnd_1822 < baseStart_1822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861 : List Nat := [1, 3, 1, 1, 1, 2, 7, 1, 3]
def baseStart_1861 : Nat := 118140960795 + 1861 * 2 ^ 59
def prefixEnd_1861 : Nat := 4983230072969 + 3 ^ 40 * 1861 * 2
def baseEnd_1861 : Nat := 849411109442180025731

theorem tailTrace_1861 : CollatzResearch.WordTrace tailWord_1861 prefixEnd_1861 849411109442180025731 := by
  unfold tailWord_1861
  simp only [CollatzResearch.WordTrace]
  refine ⟨67876246265389678605437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45250830843593119070291 67876246265389678605437)
  ·
    refine ⟨25453592349521129477039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67876246265389678605437 25453592349521129477039)
    ·
      refine ⟨38180388524281694215559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25453592349521129477039 38180388524281694215559)
      ·
        refine ⟨57270582786422541323339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38180388524281694215559 57270582786422541323339)
        ·
          refine ⟨85905874179633811985009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57270582786422541323339 85905874179633811985009)
          ·
            refine ⟨64429405634725358988757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85905874179633811985009 64429405634725358988757)
            ·
              refine ⟨1510064194563875601299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 64429405634725358988757 1510064194563875601299)
              ·
                refine ⟨2265096291845813401949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1510064194563875601299 2265096291845813401949)
                ·
                  refine ⟨849411109442180025731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2265096291845813401949 849411109442180025731)
                  ·
                    rfl

theorem cell20_1861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_1861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1861 prefixEnd_1861 := by exact prefixLift 1861
  have htrace : WordTrace (prefixWord ++ tailWord_1861) baseStart_1861 baseEnd_1861 := by
    simpa [prefixWord, tailWord_1861, baseEnd_1861] using wordTrace_append hprefix tailTrace_1861
  have hstable : (prefixWord ++ tailWord_1861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861).length < 2 ^ (prefixWord ++ tailWord_1861).sum := by decide
  have hdescent : baseEnd_1861 < baseStart_1861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892 : List Nat := [2, 3, 1, 1, 6, 1, 6]
def baseStart_1892 : Nat := 118140960795 + 1892 * 2 ^ 59
def prefixEnd_1892 : Nat := 4983230072969 + 3 ^ 40 * 1892 * 2
def baseEnd_1892 : Nat := 95951150460427776919

theorem tailTrace_1892 : CollatzResearch.WordTrace tailWord_1892 prefixEnd_1892 95951150460427776919 := by
  unfold tailWord_1892
  simp only [CollatzResearch.WordTrace]
  refine ⟨34503454576540986491965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46004606102054648655953 34503454576540986491965)
  ·
    refine ⟨12938795466202869934487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34503454576540986491965 12938795466202869934487)
    ·
      refine ⟨19408193199304304901731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12938795466202869934487 19408193199304304901731)
      ·
        refine ⟨29112289798956457352597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19408193199304304901731 29112289798956457352597)
        ·
          refine ⟨1364638584326083938403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29112289798956457352597 1364638584326083938403)
          ·
            refine ⟨2046957876489125907605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1364638584326083938403 2046957876489125907605)
            ·
              refine ⟨95951150460427776919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2046957876489125907605 95951150460427776919)
              ·
                rfl

theorem cell20_1892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 6].length) (baseStart_1892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1892 prefixEnd_1892 := by exact prefixLift 1892
  have htrace : WordTrace (prefixWord ++ tailWord_1892) baseStart_1892 baseEnd_1892 := by
    simpa [prefixWord, tailWord_1892, baseEnd_1892] using wordTrace_append hprefix tailTrace_1892
  have hstable : (prefixWord ++ tailWord_1892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892).length < 2 ^ (prefixWord ++ tailWord_1892).sum := by decide
  have hdescent : baseEnd_1892 < baseStart_1892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920 : List Nat := [2, 1, 1, 2, 1, 2, 5, 3, 3]
def baseStart_1920 : Nat := 118140960795 + 1920 * 2 ^ 59
def prefixEnd_1920 : Nat := 4983230072969 + 3 ^ 40 * 1920 * 2
def baseEnd_1920 : Nat := 876340317100197058823

theorem tailTrace_1920 : CollatzResearch.WordTrace tailWord_1920 prefixEnd_1920 876340317100197058823 := by
  unfold tailWord_1920
  simp only [CollatzResearch.WordTrace]
  refine ⟨35014076525821377501607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46685435367761836668809 35014076525821377501607)
  ·
    refine ⟨52521114788732066252411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35014076525821377501607 52521114788732066252411)
    ·
      refine ⟨78781672183098099378617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52521114788732066252411 78781672183098099378617)
      ·
        refine ⟨59086254137323574533963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78781672183098099378617 59086254137323574533963)
        ·
          refine ⟨88629381205985361800945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59086254137323574533963 88629381205985361800945)
          ·
            refine ⟨66472035904489021350709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88629381205985361800945 66472035904489021350709)
            ·
              refine ⟨6231753366045845751629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66472035904489021350709 6231753366045845751629)
              ·
                refine ⟨2336907512267192156861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6231753366045845751629 2336907512267192156861)
                ·
                  refine ⟨876340317100197058823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2336907512267192156861 876340317100197058823)
                  ·
                    rfl

theorem cell20_1920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 3].length) (baseStart_1920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1920 prefixEnd_1920 := by exact prefixLift 1920
  have htrace : WordTrace (prefixWord ++ tailWord_1920) baseStart_1920 baseEnd_1920 := by
    simpa [prefixWord, tailWord_1920, baseEnd_1920] using wordTrace_append hprefix tailTrace_1920
  have hstable : (prefixWord ++ tailWord_1920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920).length < 2 ^ (prefixWord ++ tailWord_1920).sum := by decide
  have hdescent : baseEnd_1920 < baseStart_1920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951 : List Nat := [1, 1, 2, 5, 4, 7]
def baseStart_1951 : Nat := 118140960795 + 1951 * 2 ^ 59
def prefixEnd_1951 : Nat := 4983230072969 + 3 ^ 40 * 1951 * 2
def baseEnd_1951 : Nat := 32981094881550630569

theorem tailTrace_1951 : CollatzResearch.WordTrace tailWord_1951 prefixEnd_1951 32981094881550630569 := by
  unfold tailWord_1951
  simp only [CollatzResearch.WordTrace]
  refine ⟨71158815939335049381707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47439210626223366254471 71158815939335049381707)
  ·
    refine ⟨106738223909002574072561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71158815939335049381707 106738223909002574072561)
    ·
      refine ⟨80053667931751930554421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106738223909002574072561 80053667931751930554421)
      ·
        refine ⟨7505031368601743489477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80053667931751930554421 7505031368601743489477)
        ·
          refine ⟨1407193381612826904277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7505031368601743489477 1407193381612826904277)
          ·
            refine ⟨32981094881550630569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1407193381612826904277 32981094881550630569)
            ·
              rfl

theorem cell20_1951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 7].length) (baseStart_1951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1951 prefixEnd_1951 := by exact prefixLift 1951
  have htrace : WordTrace (prefixWord ++ tailWord_1951) baseStart_1951 baseEnd_1951 := by
    simpa [prefixWord, tailWord_1951, baseEnd_1951] using wordTrace_append hprefix tailTrace_1951
  have hstable : (prefixWord ++ tailWord_1951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951).length < 2 ^ (prefixWord ++ tailWord_1951).sum := by decide
  have hdescent : baseEnd_1951 < baseStart_1951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954 : List Nat := [3, 3, 1, 2, 3, 1, 2, 2, 3]
def baseStart_1954 : Nat := 118140960795 + 1954 * 2 ^ 59
def prefixEnd_1954 : Nat := 4983230072969 + 3 ^ 40 * 1954 * 2
def baseEnd_1954 : Nat := 891858843547189925351

theorem tailTrace_1954 : CollatzResearch.WordTrace tailWord_1954 prefixEnd_1954 891858843547189925351 := by
  unfold tailWord_1954
  simp only [CollatzResearch.WordTrace]
  refine ⟨17817058732116640435229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47512156618977707827277 17817058732116640435229)
  ·
    refine ⟨6681397024543740163211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17817058732116640435229 6681397024543740163211)
    ·
      refine ⟨10022095536815610244817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6681397024543740163211 10022095536815610244817)
      ·
        refine ⟨7516571652611707683613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10022095536815610244817 7516571652611707683613)
        ·
          refine ⟨2818714369729390381355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7516571652611707683613 2818714369729390381355)
          ·
            refine ⟨4228071554594085572033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2818714369729390381355 4228071554594085572033)
            ·
              refine ⟨3171053665945564179025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4228071554594085572033 3171053665945564179025)
              ·
                refine ⟨2378290249459173134269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3171053665945564179025 2378290249459173134269)
                ·
                  refine ⟨891858843547189925351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2378290249459173134269 891858843547189925351)
                  ·
                    rfl

theorem cell20_1954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_1954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1954 prefixEnd_1954 := by exact prefixLift 1954
  have htrace : WordTrace (prefixWord ++ tailWord_1954) baseStart_1954 baseEnd_1954 := by
    simpa [prefixWord, tailWord_1954, baseEnd_1954] using wordTrace_append hprefix tailTrace_1954
  have hstable : (prefixWord ++ tailWord_1954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954).length < 2 ^ (prefixWord ++ tailWord_1954).sum := by decide
  have hdescent : baseEnd_1954 < baseStart_1954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982 : List Nat := [4, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_1982 : Nat := 118140960795 + 1982 * 2 ^ 59
def prefixEnd_1982 : Nat := 4983230072969 + 3 ^ 40 * 1982 * 2
def baseEnd_1982 : Nat := 904638806503536991903

theorem tailTrace_1982 : CollatzResearch.WordTrace tailWord_1982 prefixEnd_1982 904638806503536991903 := by
  unfold tailWord_1982
  simp only [CollatzResearch.WordTrace]
  refine ⟨9036184853378417970025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48192985884684895840133 9036184853378417970025)
  ·
    refine ⟨6777138640033813477519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9036184853378417970025 6777138640033813477519)
    ·
      refine ⟨10165707960050720216279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6777138640033813477519 10165707960050720216279)
      ·
        refine ⟨15248561940076080324419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10165707960050720216279 15248561940076080324419)
        ·
          refine ⟨22872842910114120486629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15248561940076080324419 22872842910114120486629)
          ·
            refine ⟨4288658045646397591243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22872842910114120486629 4288658045646397591243)
            ·
              refine ⟨6432987068469596386865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4288658045646397591243 6432987068469596386865)
              ·
                refine ⟨4824740301352197290149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6432987068469596386865 4824740301352197290149)
                ·
                  refine ⟨904638806503536991903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4824740301352197290149 904638806503536991903)
                  ·
                    rfl

theorem cell20_1982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_1982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1982 prefixEnd_1982 := by exact prefixLift 1982
  have htrace : WordTrace (prefixWord ++ tailWord_1982) baseStart_1982 baseEnd_1982 := by
    simpa [prefixWord, tailWord_1982, baseEnd_1982] using wordTrace_append hprefix tailTrace_1982
  have hstable : (prefixWord ++ tailWord_1982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982).length < 2 ^ (prefixWord ++ tailWord_1982).sum := by decide
  have hdescent : baseEnd_1982 < baseStart_1982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006 : List Nat := [5, 2, 1, 1, 3, 1, 7]
def baseStart_2006 : Nat := 118140960795 + 2006 * 2 ^ 59
def prefixEnd_2006 : Nat := 4983230072969 + 3 ^ 40 * 2006 * 2
def baseEnd_2006 : Nat := 101732562274013354645

theorem tailTrace_2006 : CollatzResearch.WordTrace tailWord_2006 prefixEnd_2006 101732562274013354645 := by
  unfold tailWord_2006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4572801921254965164617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48776553826719628422581 4572801921254965164617)
  ·
    refine ⟨3429601440941223873463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4572801921254965164617 3429601440941223873463)
    ·
      refine ⟨5144402161411835810195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3429601440941223873463 5144402161411835810195)
      ·
        refine ⟨7716603242117753715293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5144402161411835810195 7716603242117753715293)
        ·
          refine ⟨2893726215794157643235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7716603242117753715293 2893726215794157643235)
          ·
            refine ⟨4340589323691236464853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2893726215794157643235 4340589323691236464853)
            ·
              refine ⟨101732562274013354645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 4340589323691236464853 101732562274013354645)
              ·
                rfl

theorem cell20_2006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 7].length) (baseStart_2006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2006 prefixEnd_2006 := by exact prefixLift 2006
  have htrace : WordTrace (prefixWord ++ tailWord_2006) baseStart_2006 baseEnd_2006 := by
    simpa [prefixWord, tailWord_2006, baseEnd_2006] using wordTrace_append hprefix tailTrace_2006
  have hstable : (prefixWord ++ tailWord_2006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006).length < 2 ^ (prefixWord ++ tailWord_2006).sum := by decide
  have hdescent : baseEnd_2006 < baseStart_2006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 5]
def baseStart_2013 : Nat := 118140960795 + 2013 * 2 ^ 59
def prefixEnd_2013 : Nat := 4983230072969 + 3 ^ 40 * 2013 * 2
def baseEnd_2013 : Nat := 918788051205206958443

theorem tailTrace_2013 : CollatzResearch.WordTrace tailWord_2013 prefixEnd_2013 918788051205206958443 := by
  unfold tailWord_2013
  simp only [CollatzResearch.WordTrace]
  refine ⟨73420141714719638138693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48946761143146425425795 73420141714719638138693)
  ·
    refine ⟨13766276571509932151005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73420141714719638138693 13766276571509932151005)
    ·
      refine ⟨5162353714316224556627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13766276571509932151005 5162353714316224556627)
      ·
        refine ⟨7743530571474336834941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5162353714316224556627 7743530571474336834941)
        ·
          refine ⟨2903823964302876313103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7743530571474336834941 2903823964302876313103)
          ·
            refine ⟨4355735946454314469655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2903823964302876313103 4355735946454314469655)
            ·
              refine ⟨6533603919681471704483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4355735946454314469655 6533603919681471704483)
              ·
                refine ⟨9800405879522207556725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6533603919681471704483 9800405879522207556725)
                ·
                  refine ⟨918788051205206958443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9800405879522207556725 918788051205206958443)
                  ·
                    rfl

theorem cell20_2013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_2013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2013 prefixEnd_2013 := by exact prefixLift 2013
  have htrace : WordTrace (prefixWord ++ tailWord_2013) baseStart_2013 baseEnd_2013 := by
    simpa [prefixWord, tailWord_2013, baseEnd_2013] using wordTrace_append hprefix tailTrace_2013
  have hstable : (prefixWord ++ tailWord_2013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013).length < 2 ^ (prefixWord ++ tailWord_2013).sum := by decide
  have hdescent : baseEnd_2013 < baseStart_2013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020 : List Nat := [2, 3, 1, 1, 1, 1, 3, 6, 2]
def baseStart_2020 : Nat := 118140960795 + 2020 * 2 ^ 59
def prefixEnd_2020 : Nat := 4983230072969 + 3 ^ 40 * 2020 * 2
def baseEnd_2020 : Nat := 921983041944293725081

theorem tailTrace_2020 : CollatzResearch.WordTrace tailWord_2020 prefixEnd_2020 921983041944293725081 := by
  unfold tailWord_2020
  simp only [CollatzResearch.WordTrace]
  refine ⟨36837726344679916821757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49116968459573222429009 36837726344679916821757)
  ·
    refine ⟨13814147379254968808159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36837726344679916821757 13814147379254968808159)
    ·
      refine ⟨20721221068882453212239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13814147379254968808159 20721221068882453212239)
      ·
        refine ⟨31081831603323679818359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20721221068882453212239 31081831603323679818359)
        ·
          refine ⟨46622747404985519727539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31081831603323679818359 46622747404985519727539)
          ·
            refine ⟨69934121107478279591309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46622747404985519727539 69934121107478279591309)
            ·
              refine ⟨26225295415304354846741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69934121107478279591309 26225295415304354846741)
              ·
                refine ⟨1229310722592391633441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26225295415304354846741 1229310722592391633441)
                ·
                  refine ⟨921983041944293725081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1229310722592391633441 921983041944293725081)
                  ·
                    rfl

theorem cell20_2020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_2020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2020 prefixEnd_2020 := by exact prefixLift 2020
  have htrace : WordTrace (prefixWord ++ tailWord_2020) baseStart_2020 baseEnd_2020 := by
    simpa [prefixWord, tailWord_2020, baseEnd_2020] using wordTrace_append hprefix tailTrace_2020
  have hstable : (prefixWord ++ tailWord_2020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020).length < 2 ^ (prefixWord ++ tailWord_2020).sum := by decide
  have hdescent : baseEnd_2020 < baseStart_2020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030 : List Nat := [4, 1, 2, 1, 3, 2, 3, 1, 3]
def baseStart_2030 : Nat := 118140960795 + 2030 * 2 ^ 59
def prefixEnd_2030 : Nat := 4983230072969 + 3 ^ 40 * 2030 * 2
def baseEnd_2030 : Nat := 926547314428703391707

theorem tailTrace_2030 : CollatzResearch.WordTrace tailWord_2030 prefixEnd_2030 926547314428703391707 := by
  unfold tailWord_2030
  simp only [CollatzResearch.WordTrace]
  refine ⟨9255022831641442688443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49360121768754361005029 9255022831641442688443)
  ·
    refine ⟨13882534247462164032665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9255022831641442688443 13882534247462164032665)
    ·
      refine ⟨10411900685596623024499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13882534247462164032665 10411900685596623024499)
      ·
        refine ⟨15617851028394934536749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10411900685596623024499 15617851028394934536749)
        ·
          refine ⟨5856694135648100451281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15617851028394934536749 5856694135648100451281)
          ·
            refine ⟨4392520601736075338461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5856694135648100451281 4392520601736075338461)
            ·
              refine ⟨1647195225651028251923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4392520601736075338461 1647195225651028251923)
              ·
                refine ⟨2470792838476542377885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1647195225651028251923 2470792838476542377885)
                ·
                  refine ⟨926547314428703391707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2470792838476542377885 926547314428703391707)
                  ·
                    rfl

theorem cell20_2030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_2030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2030 prefixEnd_2030 := by exact prefixLift 2030
  have htrace : WordTrace (prefixWord ++ tailWord_2030) baseStart_2030 baseEnd_2030 := by
    simpa [prefixWord, tailWord_2030, baseEnd_2030] using wordTrace_append hprefix tailTrace_2030
  have hstable : (prefixWord ++ tailWord_2030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030).length < 2 ^ (prefixWord ++ tailWord_2030).sum := by decide
  have hdescent : baseEnd_2030 < baseStart_2030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041 : List Nat := [1, 2, 1, 3, 1, 4, 2, 2, 4]
def baseStart_2041 : Nat := 118140960795 + 2041 * 2 ^ 59
def prefixEnd_2041 : Nat := 4983230072969 + 3 ^ 40 * 2041 * 2
def baseEnd_2041 : Nat := 931568014161554024995

theorem tailTrace_2041 : CollatzResearch.WordTrace tailWord_2041 prefixEnd_2041 931568014161554024995 := by
  unfold tailWord_2041
  simp only [CollatzResearch.WordTrace]
  refine ⟨74441385613280420157977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49627590408853613438651 74441385613280420157977)
  ·
    refine ⟨55831039209960315118483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74441385613280420157977 55831039209960315118483)
    ·
      refine ⟨83746558814940472677725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55831039209960315118483 83746558814940472677725)
      ·
        refine ⟨31404959555602677254147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83746558814940472677725 31404959555602677254147)
        ·
          refine ⟨47107439333404015881221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31404959555602677254147 47107439333404015881221)
          ·
            refine ⟨8832644875013252977729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47107439333404015881221 8832644875013252977729)
            ·
              refine ⟨6624483656259939733297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8832644875013252977729 6624483656259939733297)
              ·
                refine ⟨4968362742194954799973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6624483656259939733297 4968362742194954799973)
                ·
                  refine ⟨931568014161554024995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4968362742194954799973 931568014161554024995)
                  ·
                    rfl

theorem cell20_2041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_2041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2041 prefixEnd_2041 := by exact prefixLift 2041
  have htrace : WordTrace (prefixWord ++ tailWord_2041) baseStart_2041 baseEnd_2041 := by
    simpa [prefixWord, tailWord_2041, baseEnd_2041] using wordTrace_append hprefix tailTrace_2041
  have hstable : (prefixWord ++ tailWord_2041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041).length < 2 ^ (prefixWord ++ tailWord_2041).sum := by decide
  have hdescent : baseEnd_2041 < baseStart_2041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072 : List Nat := [2, 1, 2, 3, 2, 1, 2, 4, 3]
def baseStart_2072 : Nat := 118140960795 + 2072 * 2 ^ 59
def prefixEnd_2072 : Nat := 4983230072969 + 3 ^ 40 * 2072 * 2
def baseEnd_2072 : Nat := 945717258863223991535

theorem tailTrace_2072 : CollatzResearch.WordTrace tailWord_2072 prefixEnd_2072 945717258863223991535 := by
  unfold tailWord_2072
  simp only [CollatzResearch.WordTrace]
  refine ⟨37786024250486357268235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50381365667315143024313 37786024250486357268235)
  ·
    refine ⟨56679036375729535902353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37786024250486357268235 56679036375729535902353)
    ·
      refine ⟨42509277281797151926765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56679036375729535902353 42509277281797151926765)
      ·
        refine ⟨15940978980673931972537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42509277281797151926765 15940978980673931972537)
        ·
          refine ⟨11955734235505448979403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15940978980673931972537 11955734235505448979403)
          ·
            refine ⟨17933601353258173469105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11955734235505448979403 17933601353258173469105)
            ·
              refine ⟨13450201014943630101829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17933601353258173469105 13450201014943630101829)
              ·
                refine ⟨2521912690301930644093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13450201014943630101829 2521912690301930644093)
                ·
                  refine ⟨945717258863223991535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2521912690301930644093 945717258863223991535)
                  ·
                    rfl

theorem cell20_2072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 3].length) (baseStart_2072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2072 prefixEnd_2072 := by exact prefixLift 2072
  have htrace : WordTrace (prefixWord ++ tailWord_2072) baseStart_2072 baseEnd_2072 := by
    simpa [prefixWord, tailWord_2072, baseEnd_2072] using wordTrace_append hprefix tailTrace_2072
  have hstable : (prefixWord ++ tailWord_2072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072).length < 2 ^ (prefixWord ++ tailWord_2072).sum := by decide
  have hdescent : baseEnd_2072 < baseStart_2072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148 : List Nat := [2, 3, 1, 1, 2, 1, 4, 3, 3]
def baseStart_2148 : Nat := 118140960795 + 2148 * 2 ^ 59
def prefixEnd_2148 : Nat := 4983230072969 + 3 ^ 40 * 2148 * 2
def baseEnd_2148 : Nat := 980405729744737457891

theorem tailTrace_2148 : CollatzResearch.WordTrace tailWord_2148 prefixEnd_2148 980405729744737457891 := by
  unfold tailWord_2148
  simp only [CollatzResearch.WordTrace]
  refine ⟨39171998112818847151549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52229330817091796202065 39171998112818847151549)
  ·
    refine ⟨14689499292307067681831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39171998112818847151549 14689499292307067681831)
    ·
      refine ⟨22034248938460601522747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14689499292307067681831 22034248938460601522747)
      ·
        refine ⟨33051373407690902284121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22034248938460601522747 33051373407690902284121)
        ·
          refine ⟨24788530055768176713091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33051373407690902284121 24788530055768176713091)
          ·
            refine ⟨37182795083652265069637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24788530055768176713091 37182795083652265069637)
            ·
              refine ⟨6971774078184799700557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37182795083652265069637 6971774078184799700557)
              ·
                refine ⟨2614415279319299887709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6971774078184799700557 2614415279319299887709)
                ·
                  refine ⟨980405729744737457891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2614415279319299887709 980405729744737457891)
                  ·
                    rfl

theorem cell20_2148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_2148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2148 prefixEnd_2148 := by exact prefixLift 2148
  have htrace : WordTrace (prefixWord ++ tailWord_2148) baseStart_2148 baseEnd_2148 := by
    simpa [prefixWord, tailWord_2148, baseEnd_2148] using wordTrace_append hprefix tailTrace_2148
  have hstable : (prefixWord ++ tailWord_2148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148).length < 2 ^ (prefixWord ++ tailWord_2148).sum := by decide
  have hdescent : baseEnd_2148 < baseStart_2148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172 : List Nat := [2, 2, 2, 1, 1, 4, 1, 5, 2]
def baseStart_2172 : Nat := 118140960795 + 2172 * 2 ^ 59
def prefixEnd_2172 : Nat := 4983230072969 + 3 ^ 40 * 2172 * 2
def baseEnd_2172 : Nat := 991359983707320657793

theorem tailTrace_2172 : CollatzResearch.WordTrace tailWord_2172 prefixEnd_2172 991359983707320657793 := by
  unfold tailWord_2172
  simp only [CollatzResearch.WordTrace]
  refine ⟨39609674069344896588385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52812898759126528784513 39609674069344896588385)
  ·
    refine ⟨29707255552008672441289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39609674069344896588385 29707255552008672441289)
    ·
      refine ⟨22280441664006504330967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29707255552008672441289 22280441664006504330967)
      ·
        refine ⟨33420662496009756496451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22280441664006504330967 33420662496009756496451)
        ·
          refine ⟨50130993744014634744677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33420662496009756496451 50130993744014634744677)
          ·
            refine ⟨9399561327002744014627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50130993744014634744677 9399561327002744014627)
            ·
              refine ⟨14099341990504116021941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9399561327002744014627 14099341990504116021941)
              ·
                refine ⟨1321813311609760877057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14099341990504116021941 1321813311609760877057)
                ·
                  refine ⟨991359983707320657793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1321813311609760877057 991359983707320657793)
                  ·
                    rfl

theorem cell20_2172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 2].length) (baseStart_2172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2172 prefixEnd_2172 := by exact prefixLift 2172
  have htrace : WordTrace (prefixWord ++ tailWord_2172) baseStart_2172 baseEnd_2172 := by
    simpa [prefixWord, tailWord_2172, baseEnd_2172] using wordTrace_append hprefix tailTrace_2172
  have hstable : (prefixWord ++ tailWord_2172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172).length < 2 ^ (prefixWord ++ tailWord_2172).sum := by decide
  have hdescent : baseEnd_2172 < baseStart_2172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 8]
def baseStart_2176 : Nat := 118140960795 + 2176 * 2 ^ 59
def prefixEnd_2176 : Nat := 4983230072969 + 3 ^ 40 * 2176 * 2
def baseEnd_2176 : Nat := 993185692701084524443

theorem tailTrace_2176 : CollatzResearch.WordTrace tailWord_2176 prefixEnd_2176 993185692701084524443 := by
  unfold tailWord_2176
  simp only [CollatzResearch.WordTrace]
  refine ⟨39682620062099238161191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52910160082798984214921 39682620062099238161191)
  ·
    refine ⟨59523930093148857241787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39682620062099238161191 59523930093148857241787)
    ·
      refine ⟨89285895139723285862681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59523930093148857241787 89285895139723285862681)
      ·
        refine ⟨66964421354792464397011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89285895139723285862681 66964421354792464397011)
        ·
          refine ⟨100446632032188696595517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66964421354792464397011 100446632032188696595517)
          ·
            refine ⟨37667487012070761223319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100446632032188696595517 37667487012070761223319)
            ·
              refine ⟨56501230518106141834979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37667487012070761223319 56501230518106141834979)
              ·
                refine ⟨84751845777159212752469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56501230518106141834979 84751845777159212752469)
                ·
                  refine ⟨993185692701084524443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 84751845777159212752469 993185692701084524443)
                  ·
                    rfl

theorem cell20_2176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_2176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2176 prefixEnd_2176 := by exact prefixLift 2176
  have htrace : WordTrace (prefixWord ++ tailWord_2176) baseStart_2176 baseEnd_2176 := by
    simpa [prefixWord, tailWord_2176, baseEnd_2176] using wordTrace_append hprefix tailTrace_2176
  have hstable : (prefixWord ++ tailWord_2176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176).length < 2 ^ (prefixWord ++ tailWord_2176).sum := by decide
  have hdescent : baseEnd_2176 < baseStart_2176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 5]
def baseStart_2186 : Nat := 118140960795 + 2186 * 2 ^ 59
def prefixEnd_2186 : Nat := 4983230072969 + 3 ^ 40 * 2186 * 2
def baseEnd_2186 : Nat := 997749965185494191069

theorem tailTrace_2186 : CollatzResearch.WordTrace tailWord_2186 prefixEnd_2186 997749965185494191069 := by
  unfold tailWord_2186
  simp only [CollatzResearch.WordTrace]
  refine ⟨19932492521992546046603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53153313391980122790941 19932492521992546046603)
  ·
    refine ⟨29898738782988819069905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19932492521992546046603 29898738782988819069905)
    ·
      refine ⟨22424054087241614302429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29898738782988819069905 22424054087241614302429)
      ·
        refine ⟨8409020282715605363411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22424054087241614302429 8409020282715605363411)
        ·
          refine ⟨12613530424073408045117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8409020282715605363411 12613530424073408045117)
          ·
            refine ⟨4730073909027528016919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12613530424073408045117 4730073909027528016919)
            ·
              refine ⟨7095110863541292025379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4730073909027528016919 7095110863541292025379)
              ·
                refine ⟨10642666295311938038069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7095110863541292025379 10642666295311938038069)
                ·
                  refine ⟨997749965185494191069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10642666295311938038069 997749965185494191069)
                  ·
                    rfl

theorem cell20_2186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_2186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2186 prefixEnd_2186 := by exact prefixLift 2186
  have htrace : WordTrace (prefixWord ++ tailWord_2186) baseStart_2186 baseEnd_2186 := by
    simpa [prefixWord, tailWord_2186, baseEnd_2186] using wordTrace_append hprefix tailTrace_2186
  have hstable : (prefixWord ++ tailWord_2186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186).length < 2 ^ (prefixWord ++ tailWord_2186).sum := by decide
  have hdescent : baseEnd_2186 < baseStart_2186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210 : List Nat := [3, 3, 1, 3, 1, 1, 2, 2, 4]
def baseStart_2210 : Nat := 118140960795 + 2210 * 2 ^ 59
def prefixEnd_2210 : Nat := 4983230072969 + 3 ^ 40 * 2210 * 2
def baseEnd_2210 : Nat := 1008704219148077390971

theorem tailTrace_2210 : CollatzResearch.WordTrace tailWord_2210 prefixEnd_2210 1008704219148077390971 := by
  unfold tailWord_2210
  simp only [CollatzResearch.WordTrace]
  refine ⟨20151330500255570765021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53736881334014855373389 20151330500255570765021)
  ·
    refine ⟨7556748937595839036883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20151330500255570765021 7556748937595839036883)
    ·
      refine ⟨11335123406393758555325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7556748937595839036883 11335123406393758555325)
      ·
        refine ⟨4250671277397659458247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11335123406393758555325 4250671277397659458247)
        ·
          refine ⟨6376006916096489187371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4250671277397659458247 6376006916096489187371)
          ·
            refine ⟨9564010374144733781057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6376006916096489187371 9564010374144733781057)
            ·
              refine ⟨7173007780608550335793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9564010374144733781057 7173007780608550335793)
              ·
                refine ⟨5379755835456412751845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7173007780608550335793 5379755835456412751845)
                ·
                  refine ⟨1008704219148077390971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5379755835456412751845 1008704219148077390971)
                  ·
                    rfl

theorem cell20_2210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_2210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2210 prefixEnd_2210 := by exact prefixLift 2210
  have htrace : WordTrace (prefixWord ++ tailWord_2210) baseStart_2210 baseEnd_2210 := by
    simpa [prefixWord, tailWord_2210, baseEnd_2210] using wordTrace_append hprefix tailTrace_2210
  have hstable : (prefixWord ++ tailWord_2210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210).length < 2 ^ (prefixWord ++ tailWord_2210).sum := by decide
  have hdescent : baseEnd_2210 < baseStart_2210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244 : List Nat := [2, 3, 3, 1, 2, 2, 3, 2, 2]
def baseStart_2244 : Nat := 118140960795 + 2244 * 2 ^ 59
def prefixEnd_2244 : Nat := 4983230072969 + 3 ^ 40 * 2244 * 2
def baseEnd_2244 : Nat := 1024222745595070257499

theorem tailTrace_2244 : CollatzResearch.WordTrace tailWord_2244 prefixEnd_2244 1024222745595070257499 := by
  unfold tailWord_2244
  simp only [CollatzResearch.WordTrace]
  refine ⟨40922701938923044898893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54563602585230726531857 40922701938923044898893)
  ·
    refine ⟨15346013227096141837085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40922701938923044898893 15346013227096141837085)
    ·
      refine ⟨5754754960161053188907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15346013227096141837085 5754754960161053188907)
      ·
        refine ⟨8632132440241579783361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5754754960161053188907 8632132440241579783361)
        ·
          refine ⟨6474099330181184837521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8632132440241579783361 6474099330181184837521)
          ·
            refine ⟨4855574497635888628141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6474099330181184837521 4855574497635888628141)
            ·
              refine ⟨1820840436613458235553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4855574497635888628141 1820840436613458235553)
              ·
                refine ⟨1365630327460093676665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1820840436613458235553 1365630327460093676665)
                ·
                  refine ⟨1024222745595070257499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1365630327460093676665 1024222745595070257499)
                  ·
                    rfl

theorem cell20_2244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_2244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2244 prefixEnd_2244 := by exact prefixLift 2244
  have htrace : WordTrace (prefixWord ++ tailWord_2244) baseStart_2244 baseEnd_2244 := by
    simpa [prefixWord, tailWord_2244, baseEnd_2244] using wordTrace_append hprefix tailTrace_2244
  have hstable : (prefixWord ++ tailWord_2244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244).length < 2 ^ (prefixWord ++ tailWord_2244).sum := by decide
  have hdescent : baseEnd_2244 < baseStart_2244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 5]
def baseStart_2245 : Nat := 118140960795 + 2245 * 2 ^ 59
def prefixEnd_2245 : Nat := 4983230072969 + 3 ^ 40 * 2245 * 2
def baseEnd_2245 : Nat := 1024679172843511224161

theorem tailTrace_2245 : CollatzResearch.WordTrace tailWord_2245 prefixEnd_2245 1024679172843511224161 := by
  unfold tailWord_2245
  simp only [CollatzResearch.WordTrace]
  refine ⟨81881876874223260584189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54587917916148840389459 81881876874223260584189)
  ·
    refine ⟨30705703827833722719071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81881876874223260584189 30705703827833722719071)
    ·
      refine ⟨46058555741750584078607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30705703827833722719071 46058555741750584078607)
      ·
        refine ⟨69087833612625876117911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46058555741750584078607 69087833612625876117911)
        ·
          refine ⟨103631750418938814176867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69087833612625876117911 103631750418938814176867)
          ·
            refine ⟨155447625628408221265301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103631750418938814176867 155447625628408221265301)
            ·
              refine ⟨7286607451331635371811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 155447625628408221265301 7286607451331635371811)
              ·
                refine ⟨10929911176997453057717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7286607451331635371811 10929911176997453057717)
                ·
                  refine ⟨1024679172843511224161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10929911176997453057717 1024679172843511224161)
                  ·
                    rfl

theorem cell20_2245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_2245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2245 prefixEnd_2245 := by exact prefixLift 2245
  have htrace : WordTrace (prefixWord ++ tailWord_2245) baseStart_2245 baseEnd_2245 := by
    simpa [prefixWord, tailWord_2245, baseEnd_2245] using wordTrace_append hprefix tailTrace_2245
  have hstable : (prefixWord ++ tailWord_2245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245).length < 2 ^ (prefixWord ++ tailWord_2245).sum := by decide
  have hdescent : baseEnd_2245 < baseStart_2245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258 : List Nat := [3, 2, 2, 2, 1, 4, 2, 1, 3]
def baseStart_2258 : Nat := 118140960795 + 2258 * 2 ^ 59
def prefixEnd_2258 : Nat := 4983230072969 + 3 ^ 40 * 2258 * 2
def baseEnd_2258 : Nat := 1030612727073243790775

theorem tailTrace_2258 : CollatzResearch.WordTrace tailWord_2258 prefixEnd_2258 1030612727073243790775 := by
  unfold tailWord_2258
  simp only [CollatzResearch.WordTrace]
  refine ⟨20589006456781620201857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54904017218084320538285 20589006456781620201857)
  ·
    refine ⟨15441754842586215151393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20589006456781620201857 15441754842586215151393)
    ·
      refine ⟨11581316131939661363545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15441754842586215151393 11581316131939661363545)
      ·
        refine ⟨8685987098954746022659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11581316131939661363545 8685987098954746022659)
        ·
          refine ⟨13028980648432119033989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8685987098954746022659 13028980648432119033989)
          ·
            refine ⟨2442933871581022318873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13028980648432119033989 2442933871581022318873)
            ·
              refine ⟨1832200403685766739155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2442933871581022318873 1832200403685766739155)
              ·
                refine ⟨2748300605528650108733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1832200403685766739155 2748300605528650108733)
                ·
                  refine ⟨1030612727073243790775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2748300605528650108733 1030612727073243790775)
                  ·
                    rfl

theorem cell20_2258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_2258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2258 prefixEnd_2258 := by exact prefixLift 2258
  have htrace : WordTrace (prefixWord ++ tailWord_2258) baseStart_2258 baseEnd_2258 := by
    simpa [prefixWord, tailWord_2258, baseEnd_2258] using wordTrace_append hprefix tailTrace_2258
  have hstable : (prefixWord ++ tailWord_2258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258).length < 2 ^ (prefixWord ++ tailWord_2258).sum := by decide
  have hdescent : baseEnd_2258 < baseStart_2258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286 : List Nat := [4, 1, 2, 1, 1, 1, 1, 7, 2]
def baseStart_2286 : Nat := 118140960795 + 2286 * 2 ^ 59
def prefixEnd_2286 : Nat := 4983230072969 + 3 ^ 40 * 2286 * 2
def baseEnd_2286 : Nat := 1043392690029590857327

theorem tailTrace_2286 : CollatzResearch.WordTrace tailWord_2286 prefixEnd_2286 1043392690029590857327 := by
  unfold tailWord_2286
  simp only [CollatzResearch.WordTrace]
  refine ⟨10422158715710907853339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55584846483791508551141 10422158715710907853339)
  ·
    refine ⟨15633238073566361780009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10422158715710907853339 15633238073566361780009)
    ·
      refine ⟨11724928555174771335007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15633238073566361780009 11724928555174771335007)
      ·
        refine ⟨17587392832762157002511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11724928555174771335007 17587392832762157002511)
        ·
          refine ⟨26381089249143235503767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17587392832762157002511 26381089249143235503767)
          ·
            refine ⟨39571633873714853255651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26381089249143235503767 39571633873714853255651)
            ·
              refine ⟨59357450810572279883477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39571633873714853255651 59357450810572279883477)
              ·
                refine ⟨1391190253372787809769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 59357450810572279883477 1391190253372787809769)
                ·
                  refine ⟨1043392690029590857327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1391190253372787809769 1043392690029590857327)
                  ·
                    rfl

theorem cell20_2286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_2286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2286 prefixEnd_2286 := by exact prefixLift 2286
  have htrace : WordTrace (prefixWord ++ tailWord_2286) baseStart_2286 baseEnd_2286 := by
    simpa [prefixWord, tailWord_2286, baseEnd_2286] using wordTrace_append hprefix tailTrace_2286
  have hstable : (prefixWord ++ tailWord_2286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286).length < 2 ^ (prefixWord ++ tailWord_2286).sum := by decide
  have hdescent : baseEnd_2286 < baseStart_2286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300 : List Nat := [2, 2, 2, 1, 4, 1, 1, 4, 3]
def baseStart_2300 : Nat := 118140960795 + 2300 * 2 ^ 59
def prefixEnd_2300 : Nat := 4983230072969 + 3 ^ 40 * 2300 * 2
def baseEnd_2300 : Nat := 1049782671507764390603

theorem tailTrace_2300 : CollatzResearch.WordTrace tailWord_2300 prefixEnd_2300 1049782671507764390603 := by
  unfold tailWord_2300
  simp only [CollatzResearch.WordTrace]
  refine ⟨41943945837483826918177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55925261116645102557569 41943945837483826918177)
  ·
    refine ⟨31457959378112870188633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41943945837483826918177 31457959378112870188633)
    ·
      refine ⟨23593469533584652641475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31457959378112870188633 23593469533584652641475)
      ·
        refine ⟨35390204300376978962213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23593469533584652641475 35390204300376978962213)
        ·
          refine ⟨6635663306320683555415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35390204300376978962213 6635663306320683555415)
          ·
            refine ⟨9953494959481025333123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6635663306320683555415 9953494959481025333123)
            ·
              refine ⟨14930242439221537999685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9953494959481025333123 14930242439221537999685)
              ·
                refine ⟨2799420457354038374941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14930242439221537999685 2799420457354038374941)
                ·
                  refine ⟨1049782671507764390603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2799420457354038374941 1049782671507764390603)
                  ·
                    rfl

theorem cell20_2300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_2300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2300 prefixEnd_2300 := by exact prefixLift 2300
  have htrace : WordTrace (prefixWord ++ tailWord_2300) baseStart_2300 baseEnd_2300 := by
    simpa [prefixWord, tailWord_2300, baseEnd_2300] using wordTrace_append hprefix tailTrace_2300
  have hstable : (prefixWord ++ tailWord_2300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300).length < 2 ^ (prefixWord ++ tailWord_2300).sum := by decide
  have hdescent : baseEnd_2300 < baseStart_2300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314 : List Nat := [3, 1, 2, 2, 1, 1, 5, 5]
def baseStart_2314 : Nat := 118140960795 + 2314 * 2 ^ 59
def prefixEnd_2314 : Nat := 4983230072969 + 3 ^ 40 * 2314 * 2
def baseEnd_2314 : Nat := 352057550995312641293

theorem tailTrace_2314 : CollatzResearch.WordTrace tailWord_2314 prefixEnd_2314 352057550995312641293 := by
  unfold tailWord_2314
  simp only [CollatzResearch.WordTrace]
  refine ⟨21099628406062011211499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56265675749498696563997 21099628406062011211499)
  ·
    refine ⟨31649442609093016817249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21099628406062011211499 31649442609093016817249)
    ·
      refine ⟨23737081956819762612937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31649442609093016817249 23737081956819762612937)
      ·
        refine ⟨17802811467614821959703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23737081956819762612937 17802811467614821959703)
        ·
          refine ⟨26704217201422232939555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17802811467614821959703 26704217201422232939555)
          ·
            refine ⟨40056325802133349409333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26704217201422232939555 40056325802133349409333)
            ·
              refine ⟨3755280543950001507125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40056325802133349409333 3755280543950001507125)
              ·
                refine ⟨352057550995312641293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3755280543950001507125 352057550995312641293)
                ·
                  rfl

theorem cell20_2314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_2314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2314 prefixEnd_2314 := by exact prefixLift 2314
  have htrace : WordTrace (prefixWord ++ tailWord_2314) baseStart_2314 baseEnd_2314 := by
    simpa [prefixWord, tailWord_2314, baseEnd_2314] using wordTrace_append hprefix tailTrace_2314
  have hstable : (prefixWord ++ tailWord_2314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314).length < 2 ^ (prefixWord ++ tailWord_2314).sum := by decide
  have hdescent : baseEnd_2314 < baseStart_2314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341 : List Nat := [1, 3, 1, 2, 5, 1, 2, 3, 2]
def baseStart_2341 : Nat := 118140960795 + 2341 * 2 ^ 59
def prefixEnd_2341 : Nat := 4983230072969 + 3 ^ 40 * 2341 * 2
def baseEnd_2341 : Nat := 1068496188693844023769

theorem tailTrace_2341 : CollatzResearch.WordTrace tailWord_2341 prefixEnd_2341 1068496188693844023769 := by
  unfold tailWord_2341
  simp only [CollatzResearch.WordTrace]
  refine ⟨85383284526431656078877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56922189684287770719251 85383284526431656078877)
  ·
    refine ⟨32018731697411871029579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85383284526431656078877 32018731697411871029579)
    ·
      refine ⟨48028097546117806544369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32018731697411871029579 48028097546117806544369)
      ·
        refine ⟨36021073159588354908277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48028097546117806544369 36021073159588354908277)
        ·
          refine ⟨3376975608711408272651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36021073159588354908277 3376975608711408272651)
          ·
            refine ⟨5065463413067112408977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3376975608711408272651 5065463413067112408977)
            ·
              refine ⟨3799097559800334306733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5065463413067112408977 3799097559800334306733)
              ·
                refine ⟨1424661584925125365025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3799097559800334306733 1424661584925125365025)
                ·
                  refine ⟨1068496188693844023769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1424661584925125365025 1068496188693844023769)
                  ·
                    rfl

theorem cell20_2341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 2].length) (baseStart_2341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2341 prefixEnd_2341 := by exact prefixLift 2341
  have htrace : WordTrace (prefixWord ++ tailWord_2341) baseStart_2341 baseEnd_2341 := by
    simpa [prefixWord, tailWord_2341, baseEnd_2341] using wordTrace_append hprefix tailTrace_2341
  have hstable : (prefixWord ++ tailWord_2341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341).length < 2 ^ (prefixWord ++ tailWord_2341).sum := by decide
  have hdescent : baseEnd_2341 < baseStart_2341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362 : List Nat := [3, 1, 1, 1, 4, 2, 2, 4, 2]
def baseStart_2362 : Nat := 118140960795 + 2362 * 2 ^ 59
def prefixEnd_2362 : Nat := 4983230072969 + 3 ^ 40 * 2362 * 2
def baseEnd_2362 : Nat := 1078081160911104323683

theorem tailTrace_2362 : CollatzResearch.WordTrace tailWord_2362 prefixEnd_2362 1078081160911104323683 := by
  unfold tailWord_2362
  simp only [CollatzResearch.WordTrace]
  refine ⟨21537304362588060648335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57432811633568161728893 21537304362588060648335)
  ·
    refine ⟨32305956543882090972503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21537304362588060648335 32305956543882090972503)
    ·
      refine ⟨48458934815823136458755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32305956543882090972503 48458934815823136458755)
      ·
        refine ⟨72688402223734704688133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48458934815823136458755 72688402223734704688133)
        ·
          refine ⟨13629075416950257129025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72688402223734704688133 13629075416950257129025)
          ·
            refine ⟨10221806562712692846769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13629075416950257129025 10221806562712692846769)
            ·
              refine ⟨7666354922034519635077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10221806562712692846769 7666354922034519635077)
              ·
                refine ⟨1437441547881472431577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7666354922034519635077 1437441547881472431577)
                ·
                  refine ⟨1078081160911104323683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1437441547881472431577 1078081160911104323683)
                  ·
                    rfl

theorem cell20_2362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 2].length) (baseStart_2362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2362 prefixEnd_2362 := by exact prefixLift 2362
  have htrace : WordTrace (prefixWord ++ tailWord_2362) baseStart_2362 baseEnd_2362 := by
    simpa [prefixWord, tailWord_2362, baseEnd_2362] using wordTrace_append hprefix tailTrace_2362
  have hstable : (prefixWord ++ tailWord_2362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362).length < 2 ^ (prefixWord ++ tailWord_2362).sum := by decide
  have hdescent : baseEnd_2362 < baseStart_2362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472 : List Nat := [2, 1, 6, 1, 1, 1, 4, 2, 2]
def baseStart_2472 : Nat := 118140960795 + 2472 * 2 ^ 59
def prefixEnd_2472 : Nat := 4983230072969 + 3 ^ 40 * 2472 * 2
def baseEnd_2472 : Nat := 1128288158239610656567

theorem tailTrace_2472 : CollatzResearch.WordTrace tailWord_2472 prefixEnd_2472 1128288158239610656567 := by
  unfold tailWord_2472
  simp only [CollatzResearch.WordTrace]
  refine ⟨45080623525920514548835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60107498034560686065113 45080623525920514548835)
  ·
    refine ⟨67620935288880771823253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45080623525920514548835 67620935288880771823253)
    ·
      refine ⟨3169731341666286179215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 67620935288880771823253 3169731341666286179215)
      ·
        refine ⟨4754597012499429268823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3169731341666286179215 4754597012499429268823)
        ·
          refine ⟨7131895518749143903235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4754597012499429268823 7131895518749143903235)
          ·
            refine ⟨10697843278123715854853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7131895518749143903235 10697843278123715854853)
            ·
              refine ⟨2005845614648196722785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10697843278123715854853 2005845614648196722785)
              ·
                refine ⟨1504384210986147542089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2005845614648196722785 1504384210986147542089)
                ·
                  refine ⟨1128288158239610656567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1504384210986147542089 1128288158239610656567)
                  ·
                    rfl

theorem cell20_2472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 2].length) (baseStart_2472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2472 prefixEnd_2472 := by exact prefixLift 2472
  have htrace : WordTrace (prefixWord ++ tailWord_2472) baseStart_2472 baseEnd_2472 := by
    simpa [prefixWord, tailWord_2472, baseEnd_2472] using wordTrace_append hprefix tailTrace_2472
  have hstable : (prefixWord ++ tailWord_2472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472).length < 2 ^ (prefixWord ++ tailWord_2472).sum := by decide
  have hdescent : baseEnd_2472 < baseStart_2472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500 : List Nat := [2, 3, 3, 2, 2, 1, 3, 4]
def baseStart_2500 : Nat := 118140960795 + 2500 * 2 ^ 59
def prefixEnd_2500 : Nat := 4983230072969 + 3 ^ 40 * 2500 * 2
def baseEnd_2500 : Nat := 380356040398652574373

theorem tailTrace_2500 : CollatzResearch.WordTrace tailWord_2500 prefixEnd_2500 380356040398652574373 := by
  unfold tailWord_2500
  simp only [CollatzResearch.WordTrace]
  refine ⟨45591245475200905558477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60788327300267874077969 45591245475200905558477)
  ·
    refine ⟨17096717053200339584429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45591245475200905558477 17096717053200339584429)
    ·
      refine ⟨6411268894950127344161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17096717053200339584429 6411268894950127344161)
      ·
        refine ⟨4808451671212595508121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6411268894950127344161 4808451671212595508121)
        ·
          refine ⟨3606338753409446631091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4808451671212595508121 3606338753409446631091)
          ·
            refine ⟨5409508130114169946637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3606338753409446631091 5409508130114169946637)
            ·
              refine ⟨2028565548792813729989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5409508130114169946637 2028565548792813729989)
              ·
                refine ⟨380356040398652574373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2028565548792813729989 380356040398652574373)
                ·
                  rfl

theorem cell20_2500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 4].length) (baseStart_2500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2500 prefixEnd_2500 := by exact prefixLift 2500
  have htrace : WordTrace (prefixWord ++ tailWord_2500) baseStart_2500 baseEnd_2500 := by
    simpa [prefixWord, tailWord_2500, baseEnd_2500] using wordTrace_append hprefix tailTrace_2500
  have hstable : (prefixWord ++ tailWord_2500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500).length < 2 ^ (prefixWord ++ tailWord_2500).sum := by decide
  have hdescent : baseEnd_2500 < baseStart_2500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535 : List Nat := [1, 1, 5, 2, 1, 1, 4, 1, 4]
def baseStart_2535 : Nat := 118140960795 + 2535 * 2 ^ 59
def prefixEnd_2535 : Nat := 4983230072969 + 3 ^ 40 * 2535 * 2
def baseEnd_2535 : Nat := 1157043074891391556309

theorem tailTrace_2535 : CollatzResearch.WordTrace tailWord_2535 prefixEnd_2535 1157043074891391556309 := by
  unfold tailWord_2535
  simp only [CollatzResearch.WordTrace]
  refine ⟨92459045823602788641059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61639363882401859094039 92459045823602788641059)
  ·
    refine ⟨138688568735404182961589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92459045823602788641059 138688568735404182961589)
    ·
      refine ⟨13002053318944142152649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138688568735404182961589 13002053318944142152649)
      ·
        refine ⟨9751539989208106614487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13002053318944142152649 9751539989208106614487)
        ·
          refine ⟨14627309983812159921731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9751539989208106614487 14627309983812159921731)
          ·
            refine ⟨21940964975718239882597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14627309983812159921731 21940964975718239882597)
            ·
              refine ⟨4113930932947169977987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21940964975718239882597 4113930932947169977987)
              ·
                refine ⟨6170896399420754966981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4113930932947169977987 6170896399420754966981)
                ·
                  refine ⟨1157043074891391556309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6170896399420754966981 1157043074891391556309)
                  ·
                    rfl

theorem cell20_2535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 4].length) (baseStart_2535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2535 prefixEnd_2535 := by exact prefixLift 2535
  have htrace : WordTrace (prefixWord ++ tailWord_2535) baseStart_2535 baseEnd_2535 := by
    simpa [prefixWord, tailWord_2535, baseEnd_2535] using wordTrace_append hprefix tailTrace_2535
  have hstable : (prefixWord ++ tailWord_2535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535).length < 2 ^ (prefixWord ++ tailWord_2535).sum := by decide
  have hdescent : baseEnd_2535 < baseStart_2535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563 : List Nat := [1, 1, 1, 3, 2, 1, 5, 6]
def baseStart_2563 : Nat := 118140960795 + 2563 * 2 ^ 59
def prefixEnd_2563 : Nat := 4983230072969 + 3 ^ 40 * 2563 * 2
def baseEnd_2563 : Nat := 389941012615912874287

theorem tailTrace_2563 : CollatzResearch.WordTrace tailWord_2563 prefixEnd_2563 389941012615912874287 := by
  unfold tailWord_2563
  simp only [CollatzResearch.WordTrace]
  refine ⟨93480289722163570660343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62320193148109047106895 93480289722163570660343)
  ·
    refine ⟨140220434583245355990515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93480289722163570660343 140220434583245355990515)
    ·
      refine ⟨210330651874868033985773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140220434583245355990515 210330651874868033985773)
      ·
        refine ⟨78873994453075512744665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210330651874868033985773 78873994453075512744665)
        ·
          refine ⟨59155495839806634558499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78873994453075512744665 59155495839806634558499)
          ·
            refine ⟨88733243759709951837749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59155495839806634558499 88733243759709951837749)
            ·
              refine ⟨8318741602472807984789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88733243759709951837749 8318741602472807984789)
              ·
                refine ⟨389941012615912874287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8318741602472807984789 389941012615912874287)
                ·
                  rfl

theorem cell20_2563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 6].length) (baseStart_2563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2563 prefixEnd_2563 := by exact prefixLift 2563
  have htrace : WordTrace (prefixWord ++ tailWord_2563) baseStart_2563 baseEnd_2563 := by
    simpa [prefixWord, tailWord_2563, baseEnd_2563] using wordTrace_append hprefix tailTrace_2563
  have hstable : (prefixWord ++ tailWord_2563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563).length < 2 ^ (prefixWord ++ tailWord_2563).sum := by decide
  have hdescent : baseEnd_2563 < baseStart_2563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600 : List Nat := [2, 1, 5, 2, 1, 3, 2, 1, 3]
def baseStart_2600 : Nat := 118140960795 + 2600 * 2 ^ 59
def prefixEnd_2600 : Nat := 4983230072969 + 3 ^ 40 * 2600 * 2
def baseEnd_2600 : Nat := 1186710846040054389377

theorem tailTrace_2600 : CollatzResearch.WordTrace tailWord_2600 prefixEnd_2600 1186710846040054389377 := by
  unfold tailWord_2600
  simp only [CollatzResearch.WordTrace]
  refine ⟨47414895294059444878627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63219860392079259838169 47414895294059444878627)
  ·
    refine ⟨71122342941089167317941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47414895294059444878627 71122342941089167317941)
    ·
      refine ⟨6667719650727109436057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71122342941089167317941 6667719650727109436057)
      ·
        refine ⟨5000789738045332077043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6667719650727109436057 5000789738045332077043)
        ·
          refine ⟨7501184607067998115565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5000789738045332077043 7501184607067998115565)
          ·
            refine ⟨2812944227650499293337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7501184607067998115565 2812944227650499293337)
            ·
              refine ⟨2109708170737874470003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2812944227650499293337 2109708170737874470003)
              ·
                refine ⟨3164562256106811705005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2109708170737874470003 3164562256106811705005)
                ·
                  refine ⟨1186710846040054389377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3164562256106811705005 1186710846040054389377)
                  ·
                    rfl

theorem cell20_2600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 3].length) (baseStart_2600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2600 prefixEnd_2600 := by exact prefixLift 2600
  have htrace : WordTrace (prefixWord ++ tailWord_2600) baseStart_2600 baseEnd_2600 := by
    simpa [prefixWord, tailWord_2600, baseEnd_2600] using wordTrace_append hprefix tailTrace_2600
  have hstable : (prefixWord ++ tailWord_2600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600).length < 2 ^ (prefixWord ++ tailWord_2600).sum := by decide
  have hdescent : baseEnd_2600 < baseStart_2600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642 : List Nat := [3, 2, 2, 1, 2, 1, 4, 2, 3]
def baseStart_2642 : Nat := 118140960795 + 2642 * 2 ^ 59
def prefixEnd_2642 : Nat := 4983230072969 + 3 ^ 40 * 2642 * 2
def baseEnd_2642 : Nat := 1205880790474574989205

theorem tailTrace_2642 : CollatzResearch.WordTrace tailWord_2642 prefixEnd_2642 1205880790474574989205 := by
  unfold tailWord_2642
  simp only [CollatzResearch.WordTrace]
  refine ⟨24090414108990015696545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64241104290640041857453 24090414108990015696545)
  ·
    refine ⟨18067810581742511772409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24090414108990015696545 18067810581742511772409)
    ·
      refine ⟨13550857936306883829307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18067810581742511772409 13550857936306883829307)
      ·
        refine ⟨20326286904460325743961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13550857936306883829307 20326286904460325743961)
        ·
          refine ⟨15244715178345244307971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20326286904460325743961 15244715178345244307971)
          ·
            refine ⟨22867072767517866461957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15244715178345244307971 22867072767517866461957)
            ·
              refine ⟨4287576143909599961617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22867072767517866461957 4287576143909599961617)
              ·
                refine ⟨3215682107932199971213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4287576143909599961617 3215682107932199971213)
                ·
                  refine ⟨1205880790474574989205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3215682107932199971213 1205880790474574989205)
                  ·
                    rfl

theorem cell20_2642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_2642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2642 prefixEnd_2642 := by exact prefixLift 2642
  have htrace : WordTrace (prefixWord ++ tailWord_2642) baseStart_2642 baseEnd_2642 := by
    simpa [prefixWord, tailWord_2642, baseEnd_2642] using wordTrace_append hprefix tailTrace_2642
  have hstable : (prefixWord ++ tailWord_2642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642).length < 2 ^ (prefixWord ++ tailWord_2642).sum := by decide
  have hdescent : baseEnd_2642 < baseStart_2642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652 : List Nat := [2, 2, 4, 1, 4, 1, 1, 5]
def baseStart_2652 : Nat := 118140960795 + 2652 * 2 ^ 59
def prefixEnd_2652 : Nat := 4983230072969 + 3 ^ 40 * 2652 * 2
def baseEnd_2652 : Nat := 403481687652994885277

theorem tailTrace_2652 : CollatzResearch.WordTrace tailWord_2652 prefixEnd_2652 403481687652994885277 := by
  unfold tailWord_2652
  simp only [CollatzResearch.WordTrace]
  refine ⟨48363193199865885325105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64484257599821180433473 48363193199865885325105)
  ·
    refine ⟨36272394899899413993829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48363193199865885325105 36272394899899413993829)
    ·
      refine ⟨6801074043731140123843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36272394899899413993829 6801074043731140123843)
      ·
        refine ⟨10201611065596710185765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6801074043731140123843 10201611065596710185765)
        ·
          refine ⟨1912802074799383159831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10201611065596710185765 1912802074799383159831)
          ·
            refine ⟨2869203112199074739747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1912802074799383159831 2869203112199074739747)
            ·
              refine ⟨4303804668298612109621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2869203112199074739747 4303804668298612109621)
              ·
                refine ⟨403481687652994885277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4303804668298612109621 403481687652994885277)
                ·
                  rfl

theorem cell20_2652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 5].length) (baseStart_2652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2652 prefixEnd_2652 := by exact prefixLift 2652
  have htrace : WordTrace (prefixWord ++ tailWord_2652) baseStart_2652 baseEnd_2652 := by
    simpa [prefixWord, tailWord_2652, baseEnd_2652] using wordTrace_append hprefix tailTrace_2652
  have hstable : (prefixWord ++ tailWord_2652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652).length < 2 ^ (prefixWord ++ tailWord_2652).sum := by decide
  have hdescent : baseEnd_2652 < baseStart_2652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714 : List Nat := [3, 1, 1, 6, 1, 1, 3, 1, 3]
def baseStart_2714 : Nat := 118140960795 + 2714 * 2 ^ 59
def prefixEnd_2714 : Nat := 4983230072969 + 3 ^ 40 * 2714 * 2
def baseEnd_2714 : Nat := 1238743552362324588911

theorem tailTrace_2714 : CollatzResearch.WordTrace tailWord_2714 prefixEnd_2714 1238743552362324588911 := by
  unfold tailWord_2714
  simp only [CollatzResearch.WordTrace]
  refine ⟨24746928043779089851799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65991808116744239604797 24746928043779089851799)
  ·
    refine ⟨37120392065668634777699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24746928043779089851799 37120392065668634777699)
    ·
      refine ⟨55680588098502952166549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37120392065668634777699 55680588098502952166549)
      ·
        refine ⟨2610027567117325882807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55680588098502952166549 2610027567117325882807)
        ·
          refine ⟨3915041350675988824211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2610027567117325882807 3915041350675988824211)
          ·
            refine ⟨5872562026013983236317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3915041350675988824211 5872562026013983236317)
            ·
              refine ⟨2202210759755243713619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5872562026013983236317 2202210759755243713619)
              ·
                refine ⟨3303316139632865570429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2202210759755243713619 3303316139632865570429)
                ·
                  refine ⟨1238743552362324588911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3303316139632865570429 1238743552362324588911)
                  ·
                    rfl

theorem cell20_2714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_2714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2714 prefixEnd_2714 := by exact prefixLift 2714
  have htrace : WordTrace (prefixWord ++ tailWord_2714) baseStart_2714 baseEnd_2714 := by
    simpa [prefixWord, tailWord_2714, baseEnd_2714] using wordTrace_append hprefix tailTrace_2714
  have hstable : (prefixWord ++ tailWord_2714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714).length < 2 ^ (prefixWord ++ tailWord_2714).sum := by decide
  have hdescent : baseEnd_2714 < baseStart_2714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773 : List Nat := [1, 3, 2, 5, 1, 1, 1, 3, 3]
def baseStart_2773 : Nat := 118140960795 + 2773 * 2 ^ 59
def prefixEnd_2773 : Nat := 4983230072969 + 3 ^ 40 * 2773 * 2
def baseEnd_2773 : Nat := 1265672760020341622003

theorem tailTrace_2773 : CollatzResearch.WordTrace tailWord_2773 prefixEnd_2773 1265672760020341622003 := by
  unfold tailWord_2773
  simp only [CollatzResearch.WordTrace]
  refine ⟨101139618961369435804973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67426412640912957203315 101139618961369435804973)
  ·
    refine ⟨37927357110513538426865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101139618961369435804973 37927357110513538426865)
    ·
      refine ⟨28445517832885153820149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37927357110513538426865 28445517832885153820149)
      ·
        refine ⟨2666767296832983170639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28445517832885153820149 2666767296832983170639)
        ·
          refine ⟨4000150945249474755959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2666767296832983170639 4000150945249474755959)
          ·
            refine ⟨6000226417874212133939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4000150945249474755959 6000226417874212133939)
            ·
              refine ⟨9000339626811318200909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6000226417874212133939 9000339626811318200909)
              ·
                refine ⟨3375127360054244325341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9000339626811318200909 3375127360054244325341)
                ·
                  refine ⟨1265672760020341622003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3375127360054244325341 1265672760020341622003)
                  ·
                    rfl

theorem cell20_2773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_2773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2773 prefixEnd_2773 := by exact prefixLift 2773
  have htrace : WordTrace (prefixWord ++ tailWord_2773) baseStart_2773 baseEnd_2773 := by
    simpa [prefixWord, tailWord_2773, baseEnd_2773] using wordTrace_append hprefix tailTrace_2773
  have hstable : (prefixWord ++ tailWord_2773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773).length < 2 ^ (prefixWord ++ tailWord_2773).sum := by decide
  have hdescent : baseEnd_2773 < baseStart_2773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777 : List Nat := [1, 2, 1, 2, 3, 2, 3, 3, 3]
def baseStart_2777 : Nat := 118140960795 + 2777 * 2 ^ 59
def prefixEnd_2777 : Nat := 4983230072969 + 3 ^ 40 * 2777 * 2
def baseEnd_2777 : Nat := 1267498469014105488653

theorem tailTrace_2777 : CollatzResearch.WordTrace tailWord_2777 prefixEnd_2777 1267498469014105488653 := by
  unfold tailWord_2777
  simp only [CollatzResearch.WordTrace]
  refine ⟨101285510946878118950585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67523673964585412633723 101285510946878118950585)
  ·
    refine ⟨75964133210158589212939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101285510946878118950585 75964133210158589212939)
    ·
      refine ⟨113946199815237883819409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75964133210158589212939 113946199815237883819409)
      ·
        refine ⟨85459649861428412864557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113946199815237883819409 85459649861428412864557)
        ·
          refine ⟨32047368698035654824209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85459649861428412864557 32047368698035654824209)
          ·
            refine ⟨24035526523526741118157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32047368698035654824209 24035526523526741118157)
            ·
              refine ⟨9013322446322527919309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24035526523526741118157 9013322446322527919309)
              ·
                refine ⟨3379995917370947969741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9013322446322527919309 3379995917370947969741)
                ·
                  refine ⟨1267498469014105488653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3379995917370947969741 1267498469014105488653)
                  ·
                    rfl

theorem cell20_2777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 3].length) (baseStart_2777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2777 prefixEnd_2777 := by exact prefixLift 2777
  have htrace : WordTrace (prefixWord ++ tailWord_2777) baseStart_2777 baseEnd_2777 := by
    simpa [prefixWord, tailWord_2777, baseEnd_2777] using wordTrace_append hprefix tailTrace_2777
  have hstable : (prefixWord ++ tailWord_2777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777).length < 2 ^ (prefixWord ++ tailWord_2777).sum := by decide
  have hdescent : baseEnd_2777 < baseStart_2777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801 : List Nat := [1, 2, 2, 2, 2, 2, 2, 5, 2]
def baseStart_2801 : Nat := 118140960795 + 2801 * 2 ^ 59
def prefixEnd_2801 : Nat := 4983230072969 + 3 ^ 40 * 2801 * 2
def baseEnd_2801 : Nat := 1278452722976688688555

theorem tailTrace_2801 : CollatzResearch.WordTrace tailWord_2801 prefixEnd_2801 1278452722976688688555 := by
  unfold tailWord_2801
  simp only [CollatzResearch.WordTrace]
  refine ⟨102160862859930217824257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68107241906620145216171 102160862859930217824257)
  ·
    refine ⟨76620647144947663368193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102160862859930217824257 76620647144947663368193)
    ·
      refine ⟨57465485358710747526145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76620647144947663368193 57465485358710747526145)
      ·
        refine ⟨43099114019033060644609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57465485358710747526145 43099114019033060644609)
        ·
          refine ⟨32324335514274795483457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43099114019033060644609 32324335514274795483457)
          ·
            refine ⟨24243251635706096612593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32324335514274795483457 24243251635706096612593)
            ·
              refine ⟨18182438726779572459445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24243251635706096612593 18182438726779572459445)
              ·
                refine ⟨1704603630635584918073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18182438726779572459445 1704603630635584918073)
                ·
                  refine ⟨1278452722976688688555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1704603630635584918073 1278452722976688688555)
                  ·
                    rfl

theorem cell20_2801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 2].length) (baseStart_2801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2801 prefixEnd_2801 := by exact prefixLift 2801
  have htrace : WordTrace (prefixWord ++ tailWord_2801) baseStart_2801 baseEnd_2801 := by
    simpa [prefixWord, tailWord_2801, baseEnd_2801] using wordTrace_append hprefix tailTrace_2801
  have hstable : (prefixWord ++ tailWord_2801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801).length < 2 ^ (prefixWord ++ tailWord_2801).sum := by decide
  have hdescent : baseEnd_2801 < baseStart_2801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804 : List Nat := [2, 6, 1, 1, 3, 7]
def baseStart_2804 : Nat := 118140960795 + 2804 * 2 ^ 59
def prefixEnd_2804 : Nat := 4983230072969 + 3 ^ 40 * 2804 * 2
def baseEnd_2804 : Nat := 47400814989704132909

theorem tailTrace_2804 : CollatzResearch.WordTrace tailWord_2804 prefixEnd_2804 47400814989704132909 := by
  unfold tailWord_2804
  simp only [CollatzResearch.WordTrace]
  refine ⟨51135140924530865091733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68180187899374486788977 51135140924530865091733)
  ·
    refine ⟨2396959730837384301175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51135140924530865091733 2396959730837384301175)
    ·
      refine ⟨3595439596256076451763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2396959730837384301175 3595439596256076451763)
      ·
        refine ⟨5393159394384114677645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3595439596256076451763 5393159394384114677645)
        ·
          refine ⟨2022434772894043004117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5393159394384114677645 2022434772894043004117)
          ·
            refine ⟨47400814989704132909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 2022434772894043004117 47400814989704132909)
            ·
              rfl

theorem cell20_2804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 7].length) (baseStart_2804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2804 prefixEnd_2804 := by exact prefixLift 2804
  have htrace : WordTrace (prefixWord ++ tailWord_2804) baseStart_2804 baseEnd_2804 := by
    simpa [prefixWord, tailWord_2804, baseEnd_2804] using wordTrace_append hprefix tailTrace_2804
  have hstable : (prefixWord ++ tailWord_2804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804).length < 2 ^ (prefixWord ++ tailWord_2804).sum := by decide
  have hdescent : baseEnd_2804 < baseStart_2804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814 : List Nat := [4, 2, 2, 1, 2, 3, 2, 2, 2]
def baseStart_2814 : Nat := 118140960795 + 2814 * 2 ^ 59
def prefixEnd_2814 : Nat := 4983230072969 + 3 ^ 40 * 2814 * 2
def baseEnd_2814 : Nat := 1284386277206421255169

theorem tailTrace_2814 : CollatzResearch.WordTrace tailWord_2814 prefixEnd_2814 1284386277206421255169 := by
  unfold tailWord_2814
  simp only [CollatzResearch.WordTrace]
  refine ⟨12829376476604179755937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68423341208555625364997 12829376476604179755937)
  ·
    refine ⟨9622032357453134816953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12829376476604179755937 9622032357453134816953)
    ·
      refine ⟨7216524268089851112715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9622032357453134816953 7216524268089851112715)
      ·
        refine ⟨10824786402134776669073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7216524268089851112715 10824786402134776669073)
        ·
          refine ⟨8118589801601082501805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10824786402134776669073 8118589801601082501805)
          ·
            refine ⟨3044471175600405938177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8118589801601082501805 3044471175600405938177)
            ·
              refine ⟨2283353381700304453633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3044471175600405938177 2283353381700304453633)
              ·
                refine ⟨1712515036275228340225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2283353381700304453633 1712515036275228340225)
                ·
                  refine ⟨1284386277206421255169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1712515036275228340225 1284386277206421255169)
                  ·
                    rfl

theorem cell20_2814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_2814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2814 prefixEnd_2814 := by exact prefixLift 2814
  have htrace : WordTrace (prefixWord ++ tailWord_2814) baseStart_2814 baseEnd_2814 := by
    simpa [prefixWord, tailWord_2814, baseEnd_2814] using wordTrace_append hprefix tailTrace_2814
  have hstable : (prefixWord ++ tailWord_2814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814).length < 2 ^ (prefixWord ++ tailWord_2814).sum := by decide
  have hdescent : baseEnd_2814 < baseStart_2814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839 : List Nat := [1, 1, 3, 4, 3, 1, 1, 2, 4]
def baseStart_2839 : Nat := 118140960795 + 2839 * 2 ^ 59
def prefixEnd_2839 : Nat := 4983230072969 + 3 ^ 40 * 2839 * 2
def baseEnd_2839 : Nat := 1295796958417445421733

theorem tailTrace_2839 : CollatzResearch.WordTrace tailWord_2839 prefixEnd_2839 1295796958417445421733 := by
  unfold tailWord_2839
  simp only [CollatzResearch.WordTrace]
  refine ⟨103546836722262707707571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69031224481508471805047 103546836722262707707571)
  ·
    refine ⟨155320255083394061561357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103546836722262707707571 155320255083394061561357)
    ·
      refine ⟨58245095656272773085509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155320255083394061561357 58245095656272773085509)
      ·
        refine ⟨10920955435551144953533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58245095656272773085509 10920955435551144953533)
        ·
          refine ⟨4095358288331679357575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10920955435551144953533 4095358288331679357575)
          ·
            refine ⟨6143037432497519036363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4095358288331679357575 6143037432497519036363)
            ·
              refine ⟨9214556148746278554545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6143037432497519036363 9214556148746278554545)
              ·
                refine ⟨6910917111559708915909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9214556148746278554545 6910917111559708915909)
                ·
                  refine ⟨1295796958417445421733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6910917111559708915909 1295796958417445421733)
                  ·
                    rfl

theorem cell20_2839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 4].length) (baseStart_2839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2839 prefixEnd_2839 := by exact prefixLift 2839
  have htrace : WordTrace (prefixWord ++ tailWord_2839) baseStart_2839 baseEnd_2839 := by
    simpa [prefixWord, tailWord_2839, baseEnd_2839] using wordTrace_append hprefix tailTrace_2839
  have hstable : (prefixWord ++ tailWord_2839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839).length < 2 ^ (prefixWord ++ tailWord_2839).sum := by decide
  have hdescent : baseEnd_2839 < baseStart_2839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856 : List Nat := [2, 1, 5, 1, 1, 1, 4, 3, 2]
def baseStart_2856 : Nat := 118140960795 + 2856 * 2 ^ 59
def prefixEnd_2856 : Nat := 4983230072969 + 3 ^ 40 * 2856 * 2
def baseEnd_2856 : Nat := 1303556221640941854997

theorem tailTrace_2856 : CollatzResearch.WordTrace tailWord_2856 prefixEnd_2856 1303556221640941854997 := by
  unfold tailWord_2856
  simp only [CollatzResearch.WordTrace]
  refine ⟨52083438830337305538211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69444585107116407384281 52083438830337305538211)
  ·
    refine ⟨78125158245505958307317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52083438830337305538211 78125158245505958307317)
    ·
      refine ⟨7324233585516183591311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78125158245505958307317 7324233585516183591311)
      ·
        refine ⟨10986350378274275386967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7324233585516183591311 10986350378274275386967)
        ·
          refine ⟨16479525567411413080451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10986350378274275386967 16479525567411413080451)
          ·
            refine ⟨24719288351117119620677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16479525567411413080451 24719288351117119620677)
            ·
              refine ⟨4634866565834459928877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24719288351117119620677 4634866565834459928877)
              ·
                refine ⟨1738074962187922473329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4634866565834459928877 1738074962187922473329)
                ·
                  refine ⟨1303556221640941854997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1738074962187922473329 1303556221640941854997)
                  ·
                    rfl

theorem cell20_2856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 2].length) (baseStart_2856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2856 prefixEnd_2856 := by exact prefixLift 2856
  have htrace : WordTrace (prefixWord ++ tailWord_2856) baseStart_2856 baseEnd_2856 := by
    simpa [prefixWord, tailWord_2856, baseEnd_2856] using wordTrace_append hprefix tailTrace_2856
  have hstable : (prefixWord ++ tailWord_2856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856).length < 2 ^ (prefixWord ++ tailWord_2856).sum := by decide
  have hdescent : baseEnd_2856 < baseStart_2856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867 : List Nat := [1, 1, 1, 2, 6, 2, 7]
def baseStart_2867 : Nat := 118140960795 + 2867 * 2 ^ 59
def prefixEnd_2867 : Nat := 4983230072969 + 3 ^ 40 * 2867 * 2
def baseEnd_2867 : Nat := 145397435708199165365

theorem tailTrace_2867 : CollatzResearch.WordTrace tailWord_2867 prefixEnd_2867 145397435708199165365 := by
  unfold tailWord_2867
  simp only [CollatzResearch.WordTrace]
  refine ⟨104568080620823489726855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69712053747215659817903 104568080620823489726855)
  ·
    refine ⟨156852120931235234590283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104568080620823489726855 156852120931235234590283)
    ·
      refine ⟨235278181396852851885425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156852120931235234590283 235278181396852851885425)
      ·
        refine ⟨176458636047639638914069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235278181396852851885425 176458636047639638914069)
        ·
          refine ⟨8271498564733108074097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 176458636047639638914069 8271498564733108074097)
          ·
            refine ⟨6203623923549831055573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8271498564733108074097 6203623923549831055573)
            ·
              refine ⟨145397435708199165365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 6203623923549831055573 145397435708199165365)
              ·
                rfl

theorem cell20_2867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 7].length) (baseStart_2867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2867 prefixEnd_2867 := by exact prefixLift 2867
  have htrace : WordTrace (prefixWord ++ tailWord_2867) baseStart_2867 baseEnd_2867 := by
    simpa [prefixWord, tailWord_2867, baseEnd_2867] using wordTrace_append hprefix tailTrace_2867
  have hstable : (prefixWord ++ tailWord_2867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867).length < 2 ^ (prefixWord ++ tailWord_2867).sum := by decide
  have hdescent : baseEnd_2867 < baseStart_2867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898 : List Nat := [3, 2, 2, 1, 1, 2, 1, 4, 4]
def baseStart_2898 : Nat := 118140960795 + 2898 * 2 ^ 59
def prefixEnd_2898 : Nat := 4983230072969 + 3 ^ 40 * 2898 * 2
def baseEnd_2898 : Nat := 1322726166075462454825

theorem tailTrace_2898 : CollatzResearch.WordTrace tailWord_2898 prefixEnd_2898 1322726166075462454825 := by
  unfold tailWord_2898
  simp only [CollatzResearch.WordTrace]
  refine ⟨26424685877128946026337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70465829005677189403565 26424685877128946026337)
  ·
    refine ⟨19818514407846709519753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26424685877128946026337 19818514407846709519753)
    ·
      refine ⟨14863885805885032139815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19818514407846709519753 14863885805885032139815)
      ·
        refine ⟨22295828708827548209723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14863885805885032139815 22295828708827548209723)
        ·
          refine ⟨33443743063241322314585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22295828708827548209723 33443743063241322314585)
          ·
            refine ⟨25082807297430991735939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33443743063241322314585 25082807297430991735939)
            ·
              refine ⟨37624210946146487603909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25082807297430991735939 37624210946146487603909)
              ·
                refine ⟨7054539552402466425733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37624210946146487603909 7054539552402466425733)
                ·
                  refine ⟨1322726166075462454825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7054539552402466425733 1322726166075462454825)
                  ·
                    rfl

theorem cell20_2898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_2898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2898 prefixEnd_2898 := by exact prefixLift 2898
  have htrace : WordTrace (prefixWord ++ tailWord_2898) baseStart_2898 baseEnd_2898 := by
    simpa [prefixWord, tailWord_2898, baseEnd_2898] using wordTrace_append hprefix tailTrace_2898
  have hstable : (prefixWord ++ tailWord_2898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898).length < 2 ^ (prefixWord ++ tailWord_2898).sum := by decide
  have hdescent : baseEnd_2898 < baseStart_2898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905 : List Nat := [1, 2, 1, 2, 2, 5, 1, 6]
def baseStart_2905 : Nat := 118140960795 + 2905 * 2 ^ 59
def prefixEnd_2905 : Nat := 4983230072969 + 3 ^ 40 * 2905 * 2
def baseEnd_2905 : Nat := 441973718938183073821

theorem tailTrace_2905 : CollatzResearch.WordTrace tailWord_2905 prefixEnd_2905 441973718938183073821 := by
  unfold tailWord_2905
  simp only [CollatzResearch.WordTrace]
  refine ⟨105954054483155979610169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70636036322103986406779 105954054483155979610169)
  ·
    refine ⟨79465540862366984707627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105954054483155979610169 79465540862366984707627)
    ·
      refine ⟨119198311293550477061441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79465540862366984707627 119198311293550477061441)
      ·
        refine ⟨89398733470162857796081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119198311293550477061441 89398733470162857796081)
        ·
          refine ⟨67049050102622143347061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89398733470162857796081 67049050102622143347061)
          ·
            refine ⟨6285848447120825938787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67049050102622143347061 6285848447120825938787)
            ·
              refine ⟨9428772670681238908181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6285848447120825938787 9428772670681238908181)
              ·
                refine ⟨441973718938183073821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9428772670681238908181 441973718938183073821)
                ·
                  rfl

theorem cell20_2905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 6].length) (baseStart_2905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2905 prefixEnd_2905 := by exact prefixLift 2905
  have htrace : WordTrace (prefixWord ++ tailWord_2905) baseStart_2905 baseEnd_2905 := by
    simpa [prefixWord, tailWord_2905, baseEnd_2905] using wordTrace_append hprefix tailTrace_2905
  have hstable : (prefixWord ++ tailWord_2905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905).length < 2 ^ (prefixWord ++ tailWord_2905).sum := by decide
  have hdescent : baseEnd_2905 < baseStart_2905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 7]
def baseStart_2912 : Nat := 118140960795 + 2912 * 2 ^ 59
def prefixEnd_2912 : Nat := 4983230072969 + 3 ^ 40 * 2912 * 2
def baseEnd_2912 : Nat := 1329116147553635988101

theorem tailTrace_2912 : CollatzResearch.WordTrace tailWord_2912 prefixEnd_2912 1329116147553635988101 := by
  unfold tailWord_2912
  simp only [CollatzResearch.WordTrace]
  refine ⟨53104682728898087557495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70806243638530783409993 53104682728898087557495)
  ·
    refine ⟨79657024093347131336243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53104682728898087557495 79657024093347131336243)
    ·
      refine ⟨119485536140020697004365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79657024093347131336243 119485536140020697004365)
      ·
        refine ⟨44807076052507761376637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119485536140020697004365 44807076052507761376637)
        ·
          refine ⟨16802653519690410516239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44807076052507761376637 16802653519690410516239)
          ·
            refine ⟨25203980279535615774359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16802653519690410516239 25203980279535615774359)
            ·
              refine ⟨37805970419303423661539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25203980279535615774359 37805970419303423661539)
              ·
                refine ⟨56708955628955135492309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37805970419303423661539 56708955628955135492309)
                ·
                  refine ⟨1329116147553635988101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 56708955628955135492309 1329116147553635988101)
                  ·
                    rfl

theorem cell20_2912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_2912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_2912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_2912 prefixEnd_2912 := by exact prefixLift 2912
  have htrace : WordTrace (prefixWord ++ tailWord_2912) baseStart_2912 baseEnd_2912 := by
    simpa [prefixWord, tailWord_2912, baseEnd_2912] using wordTrace_append hprefix tailTrace_2912
  have hstable : (prefixWord ++ tailWord_2912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912).length < 2 ^ (prefixWord ++ tailWord_2912).sum := by decide
  have hdescent : baseEnd_2912 < baseStart_2912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021 : List Nat := [1, 6, 3, 1, 1, 1, 2, 3, 2]
def baseStart_3021 : Nat := 118140960795 + 3021 * 2 ^ 59
def prefixEnd_3021 : Nat := 4983230072969 + 3 ^ 40 * 3021 * 2
def baseEnd_3021 : Nat := 1378866717633701354323

theorem tailTrace_3021 : CollatzResearch.WordTrace tailWord_3021 prefixEnd_3021 1378866717633701354323 := by
  unfold tailWord_3021
  simp only [CollatzResearch.WordTrace]
  refine ⟨110184922062907790832917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73456614708605193888611 110184922062907790832917)
  ·
    refine ⟨5164918221698802695293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 110184922062907790832917 5164918221698802695293)
    ·
      refine ⟨1936844333137051010735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5164918221698802695293 1936844333137051010735)
      ·
        refine ⟨2905266499705576516103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1936844333137051010735 2905266499705576516103)
        ·
          refine ⟨4357899749558364774155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2905266499705576516103 4357899749558364774155)
          ·
            refine ⟨6536849624337547161233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4357899749558364774155 6536849624337547161233)
            ·
              refine ⟨4902637218253160370925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6536849624337547161233 4902637218253160370925)
              ·
                refine ⟨1838488956844935139097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4902637218253160370925 1838488956844935139097)
                ·
                  refine ⟨1378866717633701354323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1838488956844935139097 1378866717633701354323)
                  ·
                    rfl

theorem cell20_3021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_3021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3021 prefixEnd_3021 := by exact prefixLift 3021
  have htrace : WordTrace (prefixWord ++ tailWord_3021) baseStart_3021 baseEnd_3021 := by
    simpa [prefixWord, tailWord_3021, baseEnd_3021] using wordTrace_append hprefix tailTrace_3021
  have hstable : (prefixWord ++ tailWord_3021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021).length < 2 ^ (prefixWord ++ tailWord_3021).sum := by decide
  have hdescent : baseEnd_3021 < baseStart_3021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039 : List Nat := [1, 1, 2, 3, 6, 1, 1, 2, 3]
def baseStart_3039 : Nat := 118140960795 + 3039 * 2 ^ 59
def prefixEnd_3039 : Nat := 4983230072969 + 3 ^ 40 * 3039 * 2
def baseEnd_3039 : Nat := 1387082408105638754249

theorem tailTrace_3039 : CollatzResearch.WordTrace tailWord_3039 prefixEnd_3039 1387082408105638754249 := by
  unfold tailWord_3039
  simp only [CollatzResearch.WordTrace]
  refine ⟨110841435997696864988171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73894290665131243325447 110841435997696864988171)
  ·
    refine ⟨166262153996545297482257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110841435997696864988171 166262153996545297482257)
    ·
      refine ⟨124696615497408973111693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166262153996545297482257 124696615497408973111693)
      ·
        refine ⟨46761230811528364916885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124696615497408973111693 46761230811528364916885)
        ·
          refine ⟨2191932694290392105479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46761230811528364916885 2191932694290392105479)
          ·
            refine ⟨3287899041435588158219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2191932694290392105479 3287899041435588158219)
            ·
              refine ⟨4931848562153382237329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3287899041435588158219 4931848562153382237329)
              ·
                refine ⟨3698886421615036677997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4931848562153382237329 3698886421615036677997)
                ·
                  refine ⟨1387082408105638754249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3698886421615036677997 1387082408105638754249)
                  ·
                    rfl

theorem cell20_3039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 3].length) (baseStart_3039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3039 prefixEnd_3039 := by exact prefixLift 3039
  have htrace : WordTrace (prefixWord ++ tailWord_3039) baseStart_3039 baseEnd_3039 := by
    simpa [prefixWord, tailWord_3039, baseEnd_3039] using wordTrace_append hprefix tailTrace_3039
  have hstable : (prefixWord ++ tailWord_3039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039).length < 2 ^ (prefixWord ++ tailWord_3039).sum := by decide
  have hdescent : baseEnd_3039 < baseStart_3039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050 : List Nat := [3, 1, 3, 1, 2, 2, 1, 3, 4]
def baseStart_3050 : Nat := 118140960795 + 3050 * 2 ^ 59
def prefixEnd_3050 : Nat := 4983230072969 + 3 ^ 40 * 3050 * 2
def baseEnd_3050 : Nat := 1392103107838489387537

theorem tailTrace_3050 : CollatzResearch.WordTrace tailWord_3050 prefixEnd_3050 1392103107838489387537 := by
  unfold tailWord_3050
  simp only [CollatzResearch.WordTrace]
  refine ⟨27810659739461435909651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74161759305230495759069 27810659739461435909651)
  ·
    refine ⟨41715989609192153864477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27810659739461435909651 41715989609192153864477)
    ·
      refine ⟨15643496103447057699179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41715989609192153864477 15643496103447057699179)
      ·
        refine ⟨23465244155170586548769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15643496103447057699179 23465244155170586548769)
        ·
          refine ⟨17598933116377939911577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23465244155170586548769 17598933116377939911577)
          ·
            refine ⟨13199199837283454933683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17598933116377939911577 13199199837283454933683)
            ·
              refine ⟨19798799755925182400525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13199199837283454933683 19798799755925182400525)
              ·
                refine ⟨7424549908471943400197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19798799755925182400525 7424549908471943400197)
                ·
                  refine ⟨1392103107838489387537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7424549908471943400197 1392103107838489387537)
                  ·
                    rfl

theorem cell20_3050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_3050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3050 prefixEnd_3050 := by exact prefixLift 3050
  have htrace : WordTrace (prefixWord ++ tailWord_3050) baseStart_3050 baseEnd_3050 := by
    simpa [prefixWord, tailWord_3050, baseEnd_3050] using wordTrace_append hprefix tailTrace_3050
  have hstable : (prefixWord ++ tailWord_3050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050).length < 2 ^ (prefixWord ++ tailWord_3050).sum := by decide
  have hdescent : baseEnd_3050 < baseStart_3050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070 : List Nat := [4, 2, 2, 2, 2, 2, 2, 4]
def baseStart_3070 : Nat := 118140960795 + 3070 * 2 ^ 59
def prefixEnd_3070 : Nat := 4983230072969 + 3 ^ 40 * 3070 * 2
def baseEnd_3070 : Nat := 467077217602436240263

theorem tailTrace_3070 : CollatzResearch.WordTrace tailWord_3070 prefixEnd_3070 467077217602436240263 := by
  unfold tailWord_3070
  simp only [CollatzResearch.WordTrace]
  refine ⟨13996512360673644920833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74648065923592772911109 13996512360673644920833)
  ·
    refine ⟨10497384270505233690625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13996512360673644920833 10497384270505233690625)
    ·
      refine ⟨7873038202878925267969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10497384270505233690625 7873038202878925267969)
      ·
        refine ⟨5904778652159193950977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7873038202878925267969 5904778652159193950977)
        ·
          refine ⟨4428583989119395463233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5904778652159193950977 4428583989119395463233)
          ·
            refine ⟨3321437991839546597425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4428583989119395463233 3321437991839546597425)
            ·
              refine ⟨2491078493879659948069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3321437991839546597425 2491078493879659948069)
              ·
                refine ⟨467077217602436240263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2491078493879659948069 467077217602436240263)
                ·
                  rfl

theorem cell20_3070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_3070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3070 prefixEnd_3070 := by exact prefixLift 3070
  have htrace : WordTrace (prefixWord ++ tailWord_3070) baseStart_3070 baseEnd_3070 := by
    simpa [prefixWord, tailWord_3070, baseEnd_3070] using wordTrace_append hprefix tailTrace_3070
  have hstable : (prefixWord ++ tailWord_3070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070).length < 2 ^ (prefixWord ++ tailWord_3070).sum := by decide
  have hdescent : baseEnd_3070 < baseStart_3070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084 : List Nat := [2, 2, 1, 2, 3, 4, 1, 3, 2]
def baseStart_3084 : Nat := 118140960795 + 3084 * 2 ^ 59
def prefixEnd_3084 : Nat := 4983230072969 + 3 ^ 40 * 3084 * 2
def baseEnd_3084 : Nat := 1407621634285482254065

theorem tailTrace_3084 : CollatzResearch.WordTrace tailWord_3084 prefixEnd_3084 1407621634285482254065 := by
  unfold tailWord_3084
  simp only [CollatzResearch.WordTrace]
  refine ⟨56241360417334775188153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74988480556446366917537 56241360417334775188153)
  ·
    refine ⟨42181020313001081391115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56241360417334775188153 42181020313001081391115)
    ·
      refine ⟨63271530469501622086673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42181020313001081391115 63271530469501622086673)
      ·
        refine ⟨47453647852126216565005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63271530469501622086673 47453647852126216565005)
        ·
          refine ⟨17795117944547331211877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47453647852126216565005 17795117944547331211877)
          ·
            refine ⟨3336584614602624602227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17795117944547331211877 3336584614602624602227)
            ·
              refine ⟨5004876921903936903341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3336584614602624602227 5004876921903936903341)
              ·
                refine ⟨1876828845713976338753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5004876921903936903341 1876828845713976338753)
                ·
                  refine ⟨1407621634285482254065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1876828845713976338753 1407621634285482254065)
                  ·
                    rfl

theorem cell20_3084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 2].length) (baseStart_3084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3084 prefixEnd_3084 := by exact prefixLift 3084
  have htrace : WordTrace (prefixWord ++ tailWord_3084) baseStart_3084 baseEnd_3084 := by
    simpa [prefixWord, tailWord_3084, baseEnd_3084] using wordTrace_append hprefix tailTrace_3084
  have hstable : (prefixWord ++ tailWord_3084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084).length < 2 ^ (prefixWord ++ tailWord_3084).sum := by decide
  have hdescent : baseEnd_3084 < baseStart_3084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095 : List Nat := [1, 1, 3, 5, 1, 1, 8]
def baseStart_3095 : Nat := 118140960795 + 3095 * 2 ^ 59
def prefixEnd_3095 : Nat := 4983230072969 + 3 ^ 40 * 3095 * 2
def baseEnd_3095 : Nat := 156960259335370320817

theorem tailTrace_3095 : CollatzResearch.WordTrace tailWord_3095 prefixEnd_3095 156960259335370320817 := by
  unfold tailWord_3095
  simp only [CollatzResearch.WordTrace]
  refine ⟨112883923794818429026739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75255949196545619351159 112883923794818429026739)
  ·
    refine ⟨169325885692227643540109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112883923794818429026739 169325885692227643540109)
    ·
      refine ⟨63497207134585366327541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169325885692227643540109 63497207134585366327541)
      ·
        refine ⟨5952863168867378093207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63497207134585366327541 5952863168867378093207)
        ·
          refine ⟨8929294753301067139811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5952863168867378093207 8929294753301067139811)
          ·
            refine ⟨13393942129951600709717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8929294753301067139811 13393942129951600709717)
            ·
              refine ⟨156960259335370320817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 13393942129951600709717 156960259335370320817)
              ·
                rfl

theorem cell20_3095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 8].length) (baseStart_3095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3095 prefixEnd_3095 := by exact prefixLift 3095
  have htrace : WordTrace (prefixWord ++ tailWord_3095) baseStart_3095 baseEnd_3095 := by
    simpa [prefixWord, tailWord_3095, baseEnd_3095] using wordTrace_append hprefix tailTrace_3095
  have hstable : (prefixWord ++ tailWord_3095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095).length < 2 ^ (prefixWord ++ tailWord_3095).sum := by decide
  have hdescent : baseEnd_3095 < baseStart_3095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101 : List Nat := [1, 4, 2, 2, 3, 1, 3, 2, 2]
def baseStart_3101 : Nat := 118140960795 + 3101 * 2 ^ 59
def prefixEnd_3101 : Nat := 4983230072969 + 3 ^ 40 * 3101 * 2
def baseEnd_3101 : Nat := 1415380897508978687329

theorem tailTrace_3101 : CollatzResearch.WordTrace tailWord_3101 prefixEnd_3101 1415380897508978687329 := by
  unfold tailWord_3101
  simp only [CollatzResearch.WordTrace]
  refine ⟨113102761773081453745157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75401841182054302496771 113102761773081453745157)
  ·
    refine ⟨21206767832452772577217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113102761773081453745157 21206767832452772577217)
    ·
      refine ⟨15905075874339579432913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21206767832452772577217 15905075874339579432913)
      ·
        refine ⟨11928806905754684574685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15905075874339579432913 11928806905754684574685)
        ·
          refine ⟨4473302589658006715507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11928806905754684574685 4473302589658006715507)
          ·
            refine ⟨6709953884487010073261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4473302589658006715507 6709953884487010073261)
            ·
              refine ⟨2516232706682628777473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6709953884487010073261 2516232706682628777473)
              ·
                refine ⟨1887174530011971583105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2516232706682628777473 1887174530011971583105)
                ·
                  refine ⟨1415380897508978687329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1887174530011971583105 1415380897508978687329)
                  ·
                    rfl

theorem cell20_3101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_3101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3101 prefixEnd_3101 := by exact prefixLift 3101
  have htrace : WordTrace (prefixWord ++ tailWord_3101) baseStart_3101 baseEnd_3101 := by
    simpa [prefixWord, tailWord_3101, baseEnd_3101] using wordTrace_append hprefix tailTrace_3101
  have hstable : (prefixWord ++ tailWord_3101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101).length < 2 ^ (prefixWord ++ tailWord_3101).sum := by decide
  have hdescent : baseEnd_3101 < baseStart_3101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105 : List Nat := [1, 2, 3, 2, 3, 3, 1, 1, 4]
def baseStart_3105 : Nat := 118140960795 + 3105 * 2 ^ 59
def prefixEnd_3105 : Nat := 4983230072969 + 3 ^ 40 * 3105 * 2
def baseEnd_3105 : Nat := 1417206606502742553979

theorem tailTrace_3105 : CollatzResearch.WordTrace tailWord_3105 prefixEnd_3105 1417206606502742553979 := by
  unfold tailWord_3105
  simp only [CollatzResearch.WordTrace]
  refine ⟨113248653758590136890769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75499102505726757927179 113248653758590136890769)
  ·
    refine ⟨84936490318942602668077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113248653758590136890769 84936490318942602668077)
    ·
      refine ⟨31851183869603476000529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84936490318942602668077 31851183869603476000529)
      ·
        refine ⟨23888387902202607000397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31851183869603476000529 23888387902202607000397)
        ·
          refine ⟨8958145463325977625149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23888387902202607000397 8958145463325977625149)
          ·
            refine ⟨3359304548747241609431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8958145463325977625149 3359304548747241609431)
            ·
              refine ⟨5038956823120862414147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3359304548747241609431 5038956823120862414147)
              ·
                refine ⟨7558435234681293621221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5038956823120862414147 7558435234681293621221)
                ·
                  refine ⟨1417206606502742553979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7558435234681293621221 1417206606502742553979)
                  ·
                    rfl

theorem cell20_3105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 4].length) (baseStart_3105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3105 prefixEnd_3105 := by exact prefixLift 3105
  have htrace : WordTrace (prefixWord ++ tailWord_3105) baseStart_3105 baseEnd_3105 := by
    simpa [prefixWord, tailWord_3105, baseEnd_3105] using wordTrace_append hprefix tailTrace_3105
  have hstable : (prefixWord ++ tailWord_3105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105).length < 2 ^ (prefixWord ++ tailWord_3105).sum := by decide
  have hdescent : baseEnd_3105 < baseStart_3105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133 : List Nat := [1, 4, 1, 3, 1, 2, 2, 6]
def baseStart_3133 : Nat := 118140960795 + 3133 * 2 ^ 59
def prefixEnd_3133 : Nat := 4983230072969 + 3 ^ 40 * 3133 * 2
def baseEnd_3133 : Nat := 476662189819696540177

theorem tailTrace_3133 : CollatzResearch.WordTrace tailWord_3133 prefixEnd_3133 476662189819696540177 := by
  unfold tailWord_3133
  simp only [CollatzResearch.WordTrace]
  refine ⟨114269897657150918910053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76179931771433945940035 114269897657150918910053)
  ·
    refine ⟨21425605810715797295635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114269897657150918910053 21425605810715797295635)
    ·
      refine ⟨32138408716073695943453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21425605810715797295635 32138408716073695943453)
      ·
        refine ⟨12051903268527635978795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32138408716073695943453 12051903268527635978795)
        ·
          refine ⟨18077854902791453968193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12051903268527635978795 18077854902791453968193)
          ·
            refine ⟨13558391177093590476145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18077854902791453968193 13558391177093590476145)
            ·
              refine ⟨10168793382820192857109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13558391177093590476145 10168793382820192857109)
              ·
                refine ⟨476662189819696540177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10168793382820192857109 476662189819696540177)
                ·
                  rfl

theorem cell20_3133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 6].length) (baseStart_3133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3133 prefixEnd_3133 := by exact prefixLift 3133
  have htrace : WordTrace (prefixWord ++ tailWord_3133) baseStart_3133 baseEnd_3133 := by
    simpa [prefixWord, tailWord_3133, baseEnd_3133] using wordTrace_append hprefix tailTrace_3133
  have hstable : (prefixWord ++ tailWord_3133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133).length < 2 ^ (prefixWord ++ tailWord_3133).sum := by decide
  have hdescent : baseEnd_3133 < baseStart_3133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157 : List Nat := [1, 3, 2, 2, 1, 2, 4, 2, 3]
def baseStart_3157 : Nat := 118140960795 + 3157 * 2 ^ 59
def prefixEnd_3157 : Nat := 4983230072969 + 3 ^ 40 * 3157 * 2
def baseEnd_3157 : Nat := 1440940823421672820433

theorem tailTrace_3157 : CollatzResearch.WordTrace tailWord_3157 prefixEnd_3157 1440940823421672820433 := by
  unfold tailWord_3157
  simp only [CollatzResearch.WordTrace]
  refine ⟨115145249570203017783725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76763499713468678522483 115145249570203017783725)
  ·
    refine ⟨43179468588826131668897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115145249570203017783725 43179468588826131668897)
    ·
      refine ⟨32384601441619598751673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43179468588826131668897 32384601441619598751673)
      ·
        refine ⟨24288451081214699063755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32384601441619598751673 24288451081214699063755)
        ·
          refine ⟨36432676621822048595633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24288451081214699063755 36432676621822048595633)
          ·
            refine ⟨27324507466366536446725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36432676621822048595633 27324507466366536446725)
            ·
              refine ⟨5123345149943725583761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27324507466366536446725 5123345149943725583761)
              ·
                refine ⟨3842508862457794187821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5123345149943725583761 3842508862457794187821)
                ·
                  refine ⟨1440940823421672820433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3842508862457794187821 1440940823421672820433)
                  ·
                    rfl

theorem cell20_3157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_3157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3157 prefixEnd_3157 := by exact prefixLift 3157
  have htrace : WordTrace (prefixWord ++ tailWord_3157) baseStart_3157 baseEnd_3157 := by
    simpa [prefixWord, tailWord_3157, baseEnd_3157] using wordTrace_append hprefix tailTrace_3157
  have hstable : (prefixWord ++ tailWord_3157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157).length < 2 ^ (prefixWord ++ tailWord_3157).sum := by decide
  have hdescent : baseEnd_3157 < baseStart_3157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164 : List Nat := [2, 2, 4, 1, 1, 1, 2, 3, 4]
def baseStart_3164 : Nat := 118140960795 + 3164 * 2 ^ 59
def prefixEnd_3164 : Nat := 4983230072969 + 3 ^ 40 * 3164 * 2
def baseEnd_3164 : Nat := 1444135814160759587071

theorem tailTrace_3164 : CollatzResearch.WordTrace tailWord_3164 prefixEnd_3164 1444135814160759587071 := by
  unfold tailWord_3164
  simp only [CollatzResearch.WordTrace]
  refine ⟨57700280272421606644273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76933707029895475525697 57700280272421606644273)
  ·
    refine ⟨43275210204316204983205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57700280272421606644273 43275210204316204983205)
    ·
      refine ⟨8114101913309288434351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43275210204316204983205 8114101913309288434351)
      ·
        refine ⟨12171152869963932651527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8114101913309288434351 12171152869963932651527)
        ·
          refine ⟨18256729304945898977291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12171152869963932651527 18256729304945898977291)
          ·
            refine ⟨27385093957418848465937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18256729304945898977291 27385093957418848465937)
            ·
              refine ⟨20538820468064136349453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27385093957418848465937 20538820468064136349453)
              ·
                refine ⟨7702057675524051131045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20538820468064136349453 7702057675524051131045)
                ·
                  refine ⟨1444135814160759587071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7702057675524051131045 1444135814160759587071)
                  ·
                    rfl

theorem cell20_3164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_3164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3164 prefixEnd_3164 := by exact prefixLift 3164
  have htrace : WordTrace (prefixWord ++ tailWord_3164) baseStart_3164 baseEnd_3164 := by
    simpa [prefixWord, tailWord_3164, baseEnd_3164] using wordTrace_append hprefix tailTrace_3164
  have hstable : (prefixWord ++ tailWord_3164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164).length < 2 ^ (prefixWord ++ tailWord_3164).sum := by decide
  have hdescent : baseEnd_3164 < baseStart_3164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192 : List Nat := [2, 1, 2, 1, 1, 1, 4, 8]
def baseStart_3192 : Nat := 118140960795 + 3192 * 2 ^ 59
def prefixEnd_3192 : Nat := 4983230072969 + 3 ^ 40 * 3192 * 2
def baseEnd_3192 : Nat := 485638592372368884541

theorem tailTrace_3192 : CollatzResearch.WordTrace tailWord_3192 prefixEnd_3192 485638592372368884541 := by
  unfold tailWord_3192
  simp only [CollatzResearch.WordTrace]
  refine ⟨58210902221701997653915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77614536295602663538553 58210902221701997653915)
  ·
    refine ⟨87316353332552996480873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58210902221701997653915 87316353332552996480873)
    ·
      refine ⟨65487264999414747360655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87316353332552996480873 65487264999414747360655)
      ·
        refine ⟨98230897499122121040983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65487264999414747360655 98230897499122121040983)
        ·
          refine ⟨147346346248683181561475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98230897499122121040983 147346346248683181561475)
          ·
            refine ⟨221019519373024772342213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147346346248683181561475 221019519373024772342213)
            ·
              refine ⟨41441159882442144814165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 221019519373024772342213 41441159882442144814165)
              ·
                refine ⟨485638592372368884541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 41441159882442144814165 485638592372368884541)
                ·
                  rfl

theorem cell20_3192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_3192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3192 prefixEnd_3192 := by exact prefixLift 3192
  have htrace : WordTrace (prefixWord ++ tailWord_3192) baseStart_3192 baseEnd_3192 := by
    simpa [prefixWord, tailWord_3192, baseEnd_3192] using wordTrace_append hprefix tailTrace_3192
  have hstable : (prefixWord ++ tailWord_3192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192).length < 2 ^ (prefixWord ++ tailWord_3192).sum := by decide
  have hdescent : baseEnd_3192 < baseStart_3192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216 : List Nat := [2, 1, 1, 1, 1, 1, 4, 6, 3]
def baseStart_3216 : Nat := 118140960795 + 3216 * 2 ^ 59
def prefixEnd_3216 : Nat := 4983230072969 + 3 ^ 40 * 3216 * 2
def baseEnd_3216 : Nat := 1467870031079689853525

theorem tailTrace_3216 : CollatzResearch.WordTrace tailWord_3216 prefixEnd_3216 1467870031079689853525 := by
  unfold tailWord_3216
  simp only [CollatzResearch.WordTrace]
  refine ⟨58648578178228047090751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78198104237637396121001 58648578178228047090751)
  ·
    refine ⟨87972867267342070636127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58648578178228047090751 87972867267342070636127)
    ·
      refine ⟨131959300901013105954191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87972867267342070636127 131959300901013105954191)
      ·
        refine ⟨197938951351519658931287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131959300901013105954191 197938951351519658931287)
        ·
          refine ⟨296908427027279488396931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197938951351519658931287 296908427027279488396931)
          ·
            refine ⟨445362640540919232595397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296908427027279488396931 445362640540919232595397)
            ·
              refine ⟨83505495101422356111637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 445362640540919232595397 83505495101422356111637)
              ·
                refine ⟨3914320082879172942733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83505495101422356111637 3914320082879172942733)
                ·
                  refine ⟨1467870031079689853525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3914320082879172942733 1467870031079689853525)
                  ·
                    rfl

theorem cell20_3216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 3].length) (baseStart_3216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3216 prefixEnd_3216 := by exact prefixLift 3216
  have htrace : WordTrace (prefixWord ++ tailWord_3216) baseStart_3216 baseEnd_3216 := by
    simpa [prefixWord, tailWord_3216, baseEnd_3216] using wordTrace_append hprefix tailTrace_3216
  have hstable : (prefixWord ++ tailWord_3216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216).length < 2 ^ (prefixWord ++ tailWord_3216).sum := by decide
  have hdescent : baseEnd_3216 < baseStart_3216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247 : List Nat := [1, 1, 2, 1, 2, 3, 6, 4]
def baseStart_3247 : Nat := 118140960795 + 3247 * 2 ^ 59
def prefixEnd_3247 : Nat := 4983230072969 + 3 ^ 40 * 3247 * 2
def baseEnd_3247 : Nat := 494006425260453273355

theorem tailTrace_3247 : CollatzResearch.WordTrace tailWord_3247 prefixEnd_3247 494006425260453273355 := by
  unfold tailWord_3247
  simp only [CollatzResearch.WordTrace]
  refine ⟨118427819244148388559995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78951879496098925706663 118427819244148388559995)
  ·
    refine ⟨177641728866222582839993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118427819244148388559995 177641728866222582839993)
    ·
      refine ⟨133231296649666937129995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177641728866222582839993 133231296649666937129995)
      ·
        refine ⟨199846944974500405694993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133231296649666937129995 199846944974500405694993)
        ·
          refine ⟨149885208730875304271245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199846944974500405694993 149885208730875304271245)
          ·
            refine ⟨56206953274078239101717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149885208730875304271245 56206953274078239101717)
            ·
              refine ⟨2634700934722417457893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56206953274078239101717 2634700934722417457893)
              ·
                refine ⟨494006425260453273355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2634700934722417457893 494006425260453273355)
                ·
                  rfl

theorem cell20_3247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 4].length) (baseStart_3247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3247 prefixEnd_3247 := by exact prefixLift 3247
  have htrace : WordTrace (prefixWord ++ tailWord_3247) baseStart_3247 baseEnd_3247 := by
    simpa [prefixWord, tailWord_3247, baseEnd_3247] using wordTrace_append hprefix tailTrace_3247
  have hstable : (prefixWord ++ tailWord_3247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247).length < 2 ^ (prefixWord ++ tailWord_3247).sum := by decide
  have hdescent : baseEnd_3247 < baseStart_3247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257 : List Nat := [1, 2, 1, 4, 1, 3, 3, 3, 2]
def baseStart_3257 : Nat := 118140960795 + 3257 * 2 ^ 59
def prefixEnd_3257 : Nat := 4983230072969 + 3 ^ 40 * 3257 * 2
def baseEnd_3257 : Nat := 1486583548265769486691

theorem tailTrace_3257 : CollatzResearch.WordTrace tailWord_3257 prefixEnd_3257 1486583548265769486691 := by
  unfold tailWord_3257
  simp only [CollatzResearch.WordTrace]
  refine ⟨118792549207920096424025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79195032805280064282683 118792549207920096424025)
  ·
    refine ⟨89094411905940072318019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118792549207920096424025 89094411905940072318019)
    ·
      refine ⟨133641617858910108477029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89094411905940072318019 133641617858910108477029)
      ·
        refine ⟨25057803348545645339443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133641617858910108477029 25057803348545645339443)
        ·
          refine ⟨37586705022818468009165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25057803348545645339443 37586705022818468009165)
          ·
            refine ⟨14095014383556925503437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37586705022818468009165 14095014383556925503437)
            ·
              refine ⟨5285630393833847063789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14095014383556925503437 5285630393833847063789)
              ·
                refine ⟨1982111397687692648921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5285630393833847063789 1982111397687692648921)
                ·
                  refine ⟨1486583548265769486691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1982111397687692648921 1486583548265769486691)
                  ·
                    rfl

theorem cell20_3257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 2].length) (baseStart_3257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3257 prefixEnd_3257 := by exact prefixLift 3257
  have htrace : WordTrace (prefixWord ++ tailWord_3257) baseStart_3257 baseEnd_3257 := by
    simpa [prefixWord, tailWord_3257, baseEnd_3257] using wordTrace_append hprefix tailTrace_3257
  have hstable : (prefixWord ++ tailWord_3257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257).length < 2 ^ (prefixWord ++ tailWord_3257).sum := by decide
  have hdescent : baseEnd_3257 < baseStart_3257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 6]
def baseStart_3261 : Nat := 118140960795 + 3261 * 2 ^ 59
def prefixEnd_3261 : Nat := 4983230072969 + 3 ^ 40 * 3261 * 2
def baseEnd_3261 : Nat := 1488409257259533353341

theorem tailTrace_3261 : CollatzResearch.WordTrace tailWord_3261 prefixEnd_3261 1488409257259533353341 := by
  unfold tailWord_3261
  simp only [CollatzResearch.WordTrace]
  refine ⟨118938441193428779569637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79292294128952519713091 118938441193428779569637)
  ·
    refine ⟨22300957723767896169307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118938441193428779569637 22300957723767896169307)
    ·
      refine ⟨33451436585651844253961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22300957723767896169307 33451436585651844253961)
      ·
        refine ⟨25088577439238883190471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33451436585651844253961 25088577439238883190471)
        ·
          refine ⟨37632866158858324785707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25088577439238883190471 37632866158858324785707)
          ·
            refine ⟨56449299238287487178561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37632866158858324785707 56449299238287487178561)
            ·
              refine ⟨42336974428715615383921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56449299238287487178561 42336974428715615383921)
              ·
                refine ⟨31752730821536711537941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42336974428715615383921 31752730821536711537941)
                ·
                  refine ⟨1488409257259533353341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31752730821536711537941 1488409257259533353341)
                  ·
                    rfl

theorem cell20_3261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_3261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3261 prefixEnd_3261 := by exact prefixLift 3261
  have htrace : WordTrace (prefixWord ++ tailWord_3261) baseStart_3261 baseEnd_3261 := by
    simpa [prefixWord, tailWord_3261, baseEnd_3261] using wordTrace_append hprefix tailTrace_3261
  have hstable : (prefixWord ++ tailWord_3261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261).length < 2 ^ (prefixWord ++ tailWord_3261).sum := by decide
  have hdescent : baseEnd_3261 < baseStart_3261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264 : List Nat := [2, 1, 1, 2, 7, 1, 6]
def baseStart_3264 : Nat := 118140960795 + 3264 * 2 ^ 59
def prefixEnd_3264 : Nat := 4983230072969 + 3 ^ 40 * 3264 * 2
def baseEnd_3264 : Nat := 165530948778317361481

theorem tailTrace_3264 : CollatzResearch.WordTrace tailWord_3264 prefixEnd_3264 165530948778317361481 := by
  unfold tailWord_3264
  simp only [CollatzResearch.WordTrace]
  refine ⟨59523930091280145964423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79365240121706861285897 59523930091280145964423)
  ·
    refine ⟨89285895136920218946635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59523930091280145964423 89285895136920218946635)
    ·
      refine ⟨133928842705380328419953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89285895136920218946635 133928842705380328419953)
      ·
        refine ⟨100446632029035246314965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133928842705380328419953 100446632029035246314965)
        ·
          refine ⟨2354217938180513585507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 100446632029035246314965 2354217938180513585507)
          ·
            refine ⟨3531326907270770378261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2354217938180513585507 3531326907270770378261)
            ·
              refine ⟨165530948778317361481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3531326907270770378261 165530948778317361481)
              ·
                rfl

theorem cell20_3264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 6].length) (baseStart_3264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3264 prefixEnd_3264 := by exact prefixLift 3264
  have htrace : WordTrace (prefixWord ++ tailWord_3264) baseStart_3264 baseEnd_3264 := by
    simpa [prefixWord, tailWord_3264, baseEnd_3264] using wordTrace_append hprefix tailTrace_3264
  have hstable : (prefixWord ++ tailWord_3264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264).length < 2 ^ (prefixWord ++ tailWord_3264).sum := by decide
  have hdescent : baseEnd_3264 < baseStart_3264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270 : List Nat := [6, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_3270 : Nat := 118140960795 + 3270 * 2 ^ 59
def prefixEnd_3270 : Nat := 4983230072969 + 3 ^ 40 * 3270 * 2
def baseEnd_3270 : Nat := 1492517102495502053305

theorem tailTrace_3270 : CollatzResearch.WordTrace tailWord_3270 prefixEnd_3270 1492517102495502053305 := by
  unfold tailWord_3270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3727084317525728645227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 79511132107215544431509 3727084317525728645227)
  ·
    refine ⟨5590626476288592967841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3727084317525728645227 5590626476288592967841)
    ·
      refine ⟨4192969857216444725881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5590626476288592967841 4192969857216444725881)
      ·
        refine ⟨3144727392912333544411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4192969857216444725881 3144727392912333544411)
        ·
          refine ⟨4717091089368500316617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3144727392912333544411 4717091089368500316617)
          ·
            refine ⟨3537818317026375237463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4717091089368500316617 3537818317026375237463)
            ·
              refine ⟨5306727475539562856195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3537818317026375237463 5306727475539562856195)
              ·
                refine ⟨7960091213309344284293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5306727475539562856195 7960091213309344284293)
                ·
                  refine ⟨1492517102495502053305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7960091213309344284293 1492517102495502053305)
                  ·
                    rfl

theorem cell20_3270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_3270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3270 prefixEnd_3270 := by exact prefixLift 3270
  have htrace : WordTrace (prefixWord ++ tailWord_3270) baseStart_3270 baseEnd_3270 := by
    simpa [prefixWord, tailWord_3270, baseEnd_3270] using wordTrace_append hprefix tailTrace_3270
  have hstable : (prefixWord ++ tailWord_3270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270).length < 2 ^ (prefixWord ++ tailWord_3270).sum := by decide
  have hdescent : baseEnd_3270 < baseStart_3270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274 : List Nat := [3, 1, 2, 1, 3, 3, 3, 2, 2]
def baseStart_3274 : Nat := 118140960795 + 3274 * 2 ^ 59
def prefixEnd_3274 : Nat := 4983230072969 + 3 ^ 40 * 3274 * 2
def baseEnd_3274 : Nat := 1494342811489265919955

theorem tailTrace_3274 : CollatzResearch.WordTrace tailWord_3274 prefixEnd_3274 1494342811489265919955 := by
  unfold tailWord_3274
  simp only [CollatzResearch.WordTrace]
  refine ⟨29853147536582999948219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79608393430887999861917 29853147536582999948219)
  ·
    refine ⟨44779721304874499922329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29853147536582999948219 44779721304874499922329)
    ·
      refine ⟨33584790978655874941747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44779721304874499922329 33584790978655874941747)
      ·
        refine ⟨50377186467983812412621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33584790978655874941747 50377186467983812412621)
        ·
          refine ⟨18891444925493929654733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50377186467983812412621 18891444925493929654733)
          ·
            refine ⟨7084291847060223620525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18891444925493929654733 7084291847060223620525)
            ·
              refine ⟨2656609442647583857697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7084291847060223620525 2656609442647583857697)
              ·
                refine ⟨1992457081985687893273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2656609442647583857697 1992457081985687893273)
                ·
                  refine ⟨1494342811489265919955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1992457081985687893273 1494342811489265919955)
                  ·
                    rfl

theorem cell20_3274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 2].length) (baseStart_3274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3274 prefixEnd_3274 := by exact prefixLift 3274
  have htrace : WordTrace (prefixWord ++ tailWord_3274) baseStart_3274 baseEnd_3274 := by
    simpa [prefixWord, tailWord_3274, baseEnd_3274] using wordTrace_append hprefix tailTrace_3274
  have hstable : (prefixWord ++ tailWord_3274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274).length < 2 ^ (prefixWord ++ tailWord_3274).sum := by decide
  have hdescent : baseEnd_3274 < baseStart_3274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284 : List Nat := [2, 4, 1, 4, 1, 2, 2, 1, 3]
def baseStart_3284 : Nat := 118140960795 + 3284 * 2 ^ 59
def prefixEnd_3284 : Nat := 4983230072969 + 3 ^ 40 * 3284 * 2
def baseEnd_3284 : Nat := 1498907083973675586581

theorem tailTrace_3284 : CollatzResearch.WordTrace tailWord_3284 prefixEnd_3284 1498907083973675586581 := by
  unfold tailWord_3284
  simp only [CollatzResearch.WordTrace]
  refine ⟨59888660055051853828453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79851546740069138437937 59888660055051853828453)
  ·
    refine ⟨11229123760322222592835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59888660055051853828453 11229123760322222592835)
    ·
      refine ⟨16843685640483333889253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11229123760322222592835 16843685640483333889253)
      ·
        refine ⟨3158191057590625104235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16843685640483333889253 3158191057590625104235)
        ·
          refine ⟨4737286586385937656353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3158191057590625104235 4737286586385937656353)
          ·
            refine ⟨3552964939789453242265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4737286586385937656353 3552964939789453242265)
            ·
              refine ⟨2664723704842089931699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3552964939789453242265 2664723704842089931699)
              ·
                refine ⟨3997085557263134897549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2664723704842089931699 3997085557263134897549)
                ·
                  refine ⟨1498907083973675586581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3997085557263134897549 1498907083973675586581)
                  ·
                    rfl

theorem cell20_3284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_3284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3284 prefixEnd_3284 := by exact prefixLift 3284
  have htrace : WordTrace (prefixWord ++ tailWord_3284) baseStart_3284 baseEnd_3284 := by
    simpa [prefixWord, tailWord_3284, baseEnd_3284] using wordTrace_append hprefix tailTrace_3284
  have hstable : (prefixWord ++ tailWord_3284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284).length < 2 ^ (prefixWord ++ tailWord_3284).sum := by decide
  have hdescent : baseEnd_3284 < baseStart_3284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285 : List Nat := [1, 3, 2, 4, 1, 1, 1, 7]
def baseStart_3285 : Nat := 118140960795 + 3285 * 2 ^ 59
def prefixEnd_3285 : Nat := 4983230072969 + 3 ^ 40 * 3285 * 2
def baseEnd_3285 : Nat := 499787837074038851081

theorem tailTrace_3285 : CollatzResearch.WordTrace tailWord_3285 prefixEnd_3285 499787837074038851081 := by
  unfold tailWord_3285
  simp only [CollatzResearch.WordTrace]
  refine ⟨119813793106480878443309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79875862070987252295539 119813793106480878443309)
  ·
    refine ⟨44930172414930329416241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119813793106480878443309 44930172414930329416241)
    ·
      refine ⟨33697629311197747062181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44930172414930329416241 33697629311197747062181)
      ·
        refine ⟨6318305495849577574159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33697629311197747062181 6318305495849577574159)
        ·
          refine ⟨9477458243774366361239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6318305495849577574159 9477458243774366361239)
          ·
            refine ⟨14216187365661549541859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9477458243774366361239 14216187365661549541859)
            ·
              refine ⟨21324281048492324312789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14216187365661549541859 21324281048492324312789)
              ·
                refine ⟨499787837074038851081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21324281048492324312789 499787837074038851081)
                ·
                  rfl

theorem cell20_3285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 7].length) (baseStart_3285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3285 prefixEnd_3285 := by exact prefixLift 3285
  have htrace : WordTrace (prefixWord ++ tailWord_3285) baseStart_3285 baseEnd_3285 := by
    simpa [prefixWord, tailWord_3285, baseEnd_3285] using wordTrace_append hprefix tailTrace_3285
  have hstable : (prefixWord ++ tailWord_3285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285).length < 2 ^ (prefixWord ++ tailWord_3285).sum := by decide
  have hdescent : baseEnd_3285 < baseStart_3285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326 : List Nat := [4, 2, 2, 1, 1, 3, 2, 2, 3]
def baseStart_3326 : Nat := 118140960795 + 3326 * 2 ^ 59
def prefixEnd_3326 : Nat := 4983230072969 + 3 ^ 40 * 3326 * 2
def baseEnd_3326 : Nat := 1518077028408196186409

theorem tailTrace_3326 : CollatzResearch.WordTrace tailWord_3326 prefixEnd_3326 1518077028408196186409 := by
  unfold tailWord_3326
  simp only [CollatzResearch.WordTrace]
  refine ⟨15163648244743110085729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80872790638629920457221 15163648244743110085729)
  ·
    refine ⟨11372736183557332564297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15163648244743110085729 11372736183557332564297)
    ·
      refine ⟨8529552137667999423223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11372736183557332564297 8529552137667999423223)
      ·
        refine ⟨12794328206501999134835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8529552137667999423223 12794328206501999134835)
        ·
          refine ⟨19191492309752998702253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12794328206501999134835 19191492309752998702253)
          ·
            refine ⟨7196809616157374513345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19191492309752998702253 7196809616157374513345)
            ·
              refine ⟨5397607212118030885009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7196809616157374513345 5397607212118030885009)
              ·
                refine ⟨4048205409088523163757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5397607212118030885009 4048205409088523163757)
                ·
                  refine ⟨1518077028408196186409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4048205409088523163757 1518077028408196186409)
                  ·
                    rfl

theorem cell20_3326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_3326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3326 prefixEnd_3326 := by exact prefixLift 3326
  have htrace : WordTrace (prefixWord ++ tailWord_3326) baseStart_3326 baseEnd_3326 := by
    simpa [prefixWord, tailWord_3326, baseEnd_3326] using wordTrace_append hprefix tailTrace_3326
  have hstable : (prefixWord ++ tailWord_3326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326).length < 2 ^ (prefixWord ++ tailWord_3326).sum := by decide
  have hdescent : baseEnd_3326 < baseStart_3326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337 : List Nat := [1, 2, 1, 1, 3, 3, 2, 3, 4]
def baseStart_3337 : Nat := 118140960795 + 3337 * 2 ^ 59
def prefixEnd_3337 : Nat := 4983230072969 + 3 ^ 40 * 3337 * 2
def baseEnd_3337 : Nat := 1523097728141046819697

theorem tailTrace_3337 : CollatzResearch.WordTrace tailWord_3337 prefixEnd_3337 1523097728141046819697 := by
  unfold tailWord_3337
  simp only [CollatzResearch.WordTrace]
  refine ⟨121710388918093759336265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81140259278729172890843 121710388918093759336265)
  ·
    refine ⟨91282791688570319502199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121710388918093759336265 91282791688570319502199)
    ·
      refine ⟨136924187532855479253299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91282791688570319502199 136924187532855479253299)
      ·
        refine ⟨205386281299283218879949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136924187532855479253299 205386281299283218879949)
        ·
          refine ⟨77019855487231207079981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205386281299283218879949 77019855487231207079981)
          ·
            refine ⟨28882445807711702654993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77019855487231207079981 28882445807711702654993)
            ·
              refine ⟨21661834355783776991245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28882445807711702654993 21661834355783776991245)
              ·
                refine ⟨8123187883418916371717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21661834355783776991245 8123187883418916371717)
                ·
                  refine ⟨1523097728141046819697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8123187883418916371717 1523097728141046819697)
                  ·
                    rfl

theorem cell20_3337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_3337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3337 prefixEnd_3337 := by exact prefixLift 3337
  have htrace : WordTrace (prefixWord ++ tailWord_3337) baseStart_3337 baseEnd_3337 := by
    simpa [prefixWord, tailWord_3337, baseEnd_3337] using wordTrace_append hprefix tailTrace_3337
  have hstable : (prefixWord ++ tailWord_3337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337).length < 2 ^ (prefixWord ++ tailWord_3337).sum := by decide
  have hdescent : baseEnd_3337 < baseStart_3337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354 : List Nat := [3, 1, 1, 3, 3, 2, 1, 2, 4]
def baseStart_3354 : Nat := 118140960795 + 3354 * 2 ^ 59
def prefixEnd_3354 : Nat := 4983230072969 + 3 ^ 40 * 3354 * 2
def baseEnd_3354 : Nat := 1530856991364543252961

theorem tailTrace_3354 : CollatzResearch.WordTrace tailWord_3354 prefixEnd_3354 1530856991364543252961 := by
  unfold tailWord_3354
  simp only [CollatzResearch.WordTrace]
  refine ⟨30582607464126415676279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81553619904337108470077 30582607464126415676279)
  ·
    refine ⟨45873911196189623514419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30582607464126415676279 45873911196189623514419)
    ·
      refine ⟨68810866794284435271629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45873911196189623514419 68810866794284435271629)
      ·
        refine ⟨25804075047856663226861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68810866794284435271629 25804075047856663226861)
        ·
          refine ⟨9676528142946248710073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25804075047856663226861 9676528142946248710073)
          ·
            refine ⟨7257396107209686532555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9676528142946248710073 7257396107209686532555)
            ·
              refine ⟨10886094160814529798833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7257396107209686532555 10886094160814529798833)
              ·
                refine ⟨8164570620610897349125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10886094160814529798833 8164570620610897349125)
                ·
                  refine ⟨1530856991364543252961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8164570620610897349125 1530856991364543252961)
                  ·
                    rfl

theorem cell20_3354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_3354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3354 prefixEnd_3354 := by exact prefixLift 3354
  have htrace : WordTrace (prefixWord ++ tailWord_3354) baseStart_3354 baseEnd_3354 := by
    simpa [prefixWord, tailWord_3354, baseEnd_3354] using wordTrace_append hprefix tailTrace_3354
  have hstable : (prefixWord ++ tailWord_3354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354).length < 2 ^ (prefixWord ++ tailWord_3354).sum := by decide
  have hdescent : baseEnd_3354 < baseStart_3354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 5]
def baseStart_3385 : Nat := 118140960795 + 3385 * 2 ^ 59
def prefixEnd_3385 : Nat := 4983230072969 + 3 ^ 40 * 3385 * 2
def baseEnd_3385 : Nat := 1545006236066213219501

theorem tailTrace_3385 : CollatzResearch.WordTrace tailWord_3385 prefixEnd_3385 1545006236066213219501 := by
  unfold tailWord_3385
  simp only [CollatzResearch.WordTrace]
  refine ⟨123461092744197957083609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82307395162798638055739 123461092744197957083609)
  ·
    refine ⟨92595819558148467812707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123461092744197957083609 92595819558148467812707)
    ·
      refine ⟨138893729337222701719061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92595819558148467812707 138893729337222701719061)
      ·
        refine ⟨6510643562682314143081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 138893729337222701719061 6510643562682314143081)
        ·
          refine ⟨4882982672011735607311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6510643562682314143081 4882982672011735607311)
          ·
            refine ⟨7324474008017603410967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4882982672011735607311 7324474008017603410967)
            ·
              refine ⟨10986711012026405116451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7324474008017603410967 10986711012026405116451)
              ·
                refine ⟨16480066518039607674677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10986711012026405116451 16480066518039607674677)
                ·
                  refine ⟨1545006236066213219501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16480066518039607674677 1545006236066213219501)
                  ·
                    rfl

theorem cell20_3385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 5].length) (baseStart_3385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3385 prefixEnd_3385 := by exact prefixLift 3385
  have htrace : WordTrace (prefixWord ++ tailWord_3385) baseStart_3385 baseEnd_3385 := by
    simpa [prefixWord, tailWord_3385, baseEnd_3385] using wordTrace_append hprefix tailTrace_3385
  have hstable : (prefixWord ++ tailWord_3385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385).length < 2 ^ (prefixWord ++ tailWord_3385).sum := by decide
  have hdescent : baseEnd_3385 < baseStart_3385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392 : List Nat := [2, 1, 1, 2, 2, 1, 3, 6, 2]
def baseStart_3392 : Nat := 118140960795 + 3392 * 2 ^ 59
def prefixEnd_3392 : Nat := 4983230072969 + 3 ^ 40 * 3392 * 2
def baseEnd_3392 : Nat := 1548201226805299986139

theorem tailTrace_3392 : CollatzResearch.WordTrace tailWord_3392 prefixEnd_3392 1548201226805299986139 := by
  unfold tailWord_3392
  simp only [CollatzResearch.WordTrace]
  refine ⟨61858201859419076294215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82477602479225435058953 61858201859419076294215)
  ·
    refine ⟨92787302789128614441323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61858201859419076294215 92787302789128614441323)
    ·
      refine ⟨139180954183692921661985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92787302789128614441323 139180954183692921661985)
      ·
        refine ⟨104385715637769691246489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139180954183692921661985 104385715637769691246489)
        ·
          refine ⟨78289286728327268434867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104385715637769691246489 78289286728327268434867)
          ·
            refine ⟨117433930092490902652301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78289286728327268434867 117433930092490902652301)
            ·
              refine ⟨44037723784684088494613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117433930092490902652301 44037723784684088494613)
              ·
                refine ⟨2064268302407066648185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44037723784684088494613 2064268302407066648185)
                ·
                  refine ⟨1548201226805299986139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2064268302407066648185 1548201226805299986139)
                  ·
                    rfl

theorem cell20_3392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 2].length) (baseStart_3392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3392 prefixEnd_3392 := by exact prefixLift 3392
  have htrace : WordTrace (prefixWord ++ tailWord_3392) baseStart_3392 baseEnd_3392 := by
    simpa [prefixWord, tailWord_3392, baseEnd_3392] using wordTrace_append hprefix tailTrace_3392
  have hstable : (prefixWord ++ tailWord_3392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392).length < 2 ^ (prefixWord ++ tailWord_3392).sum := by decide
  have hdescent : baseEnd_3392 < baseStart_3392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437 : List Nat := [1, 5, 1, 1, 1, 5, 6]
def baseStart_3437 : Nat := 118140960795 + 3437 * 2 ^ 59
def prefixEnd_3437 : Nat := 4983230072969 + 3 ^ 40 * 3437 * 2
def baseEnd_3437 : Nat := 174304494776127053995

theorem tailTrace_3437 : CollatzResearch.WordTrace tailWord_3437 prefixEnd_3437 174304494776127053995 := by
  unfold tailWord_3437
  simp only [CollatzResearch.WordTrace]
  refine ⟨125357688555810837976565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83571792370540558651043 125357688555810837976565)
  ·
    refine ⟨11752283302107266060303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125357688555810837976565 11752283302107266060303)
    ·
      refine ⟨17628424953160899090455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11752283302107266060303 17628424953160899090455)
      ·
        refine ⟨26442637429741348635683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17628424953160899090455 26442637429741348635683)
        ·
          refine ⟨39663956144612022953525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26442637429741348635683 39663956144612022953525)
          ·
            refine ⟨3718495888557377151893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39663956144612022953525 3718495888557377151893)
            ·
              refine ⟨174304494776127053995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3718495888557377151893 174304494776127053995)
              ·
                rfl

theorem cell20_3437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 6].length) (baseStart_3437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3437 prefixEnd_3437 := by exact prefixLift 3437
  have htrace : WordTrace (prefixWord ++ tailWord_3437) baseStart_3437 baseEnd_3437 := by
    simpa [prefixWord, tailWord_3437, baseEnd_3437] using wordTrace_append hprefix tailTrace_3437
  have hstable : (prefixWord ++ tailWord_3437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437).length < 2 ^ (prefixWord ++ tailWord_3437).sum := by decide
  have hdescent : baseEnd_3437 < baseStart_3437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447 : List Nat := [1, 1, 3, 1, 1, 2, 7, 2, 2]
def baseStart_3447 : Nat := 118140960795 + 3447 * 2 ^ 59
def prefixEnd_3447 : Nat := 4983230072969 + 3 ^ 40 * 3447 * 2
def baseEnd_3447 : Nat := 1573304725469553152581

theorem tailTrace_3447 : CollatzResearch.WordTrace tailWord_3447 prefixEnd_3447 1573304725469553152581 := by
  unfold tailWord_3447
  simp only [CollatzResearch.WordTrace]
  refine ⟨125722418519582545840595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83814945679721697227063 125722418519582545840595)
  ·
    refine ⟨188583627779373818760893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125722418519582545840595 188583627779373818760893)
    ·
      refine ⟨70718860417265182035335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188583627779373818760893 70718860417265182035335)
      ·
        refine ⟨106078290625897773053003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70718860417265182035335 106078290625897773053003)
        ·
          refine ⟨159117435938846659579505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106078290625897773053003 159117435938846659579505)
          ·
            refine ⟨119338076954134994684629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159117435938846659579505 119338076954134994684629)
            ·
              refine ⟨2796986178612538937921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 119338076954134994684629 2796986178612538937921)
              ·
                refine ⟨2097739633959404203441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2796986178612538937921 2097739633959404203441)
                ·
                  refine ⟨1573304725469553152581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2097739633959404203441 1573304725469553152581)
                  ·
                    rfl

theorem cell20_3447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 2].length) (baseStart_3447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3447 prefixEnd_3447 := by exact prefixLift 3447
  have htrace : WordTrace (prefixWord ++ tailWord_3447) baseStart_3447 baseEnd_3447 := by
    simpa [prefixWord, tailWord_3447, baseEnd_3447] using wordTrace_append hprefix tailTrace_3447
  have hstable : (prefixWord ++ tailWord_3447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447).length < 2 ^ (prefixWord ++ tailWord_3447).sum := by decide
  have hdescent : baseEnd_3447 < baseStart_3447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457 : List Nat := [1, 2, 4, 3, 2, 2, 2, 1, 3]
def baseStart_3457 : Nat := 118140960795 + 3457 * 2 ^ 59
def prefixEnd_3457 : Nat := 4983230072969 + 3 ^ 40 * 3457 * 2
def baseEnd_3457 : Nat := 1577868997953962819207

theorem tailTrace_3457 : CollatzResearch.WordTrace tailWord_3457 prefixEnd_3457 1577868997953962819207 := by
  unfold tailWord_3457
  simp only [CollatzResearch.WordTrace]
  refine ⟨126087148483354253704625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84058098988902835803083 126087148483354253704625)
  ·
    refine ⟨94565361362515690278469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126087148483354253704625 94565361362515690278469)
    ·
      refine ⟨17731005255471691927213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94565361362515690278469 17731005255471691927213)
      ·
        refine ⟨6649126970801884472705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17731005255471691927213 6649126970801884472705)
        ·
          refine ⟨4986845228101413354529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6649126970801884472705 4986845228101413354529)
          ·
            refine ⟨3740133921076060015897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4986845228101413354529 3740133921076060015897)
            ·
              refine ⟨2805100440807045011923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3740133921076060015897 2805100440807045011923)
              ·
                refine ⟨4207650661210567517885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2805100440807045011923 4207650661210567517885)
                ·
                  refine ⟨1577868997953962819207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4207650661210567517885 1577868997953962819207)
                  ·
                    rfl

theorem cell20_3457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 3].length) (baseStart_3457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3457 prefixEnd_3457 := by exact prefixLift 3457
  have htrace : WordTrace (prefixWord ++ tailWord_3457) baseStart_3457 baseEnd_3457 := by
    simpa [prefixWord, tailWord_3457, baseEnd_3457] using wordTrace_append hprefix tailTrace_3457
  have hstable : (prefixWord ++ tailWord_3457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457).length < 2 ^ (prefixWord ++ tailWord_3457).sum := by decide
  have hdescent : baseEnd_3457 < baseStart_3457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461 : List Nat := [1, 3, 1, 1, 3, 1, 6, 1, 3]
def baseStart_3461 : Nat := 118140960795 + 3461 * 2 ^ 59
def prefixEnd_3461 : Nat := 4983230072969 + 3 ^ 40 * 3461 * 2
def baseEnd_3461 : Nat := 1579694706947726685857

theorem tailTrace_3461 : CollatzResearch.WordTrace tailWord_3461 prefixEnd_3461 1579694706947726685857 := by
  unfold tailWord_3461
  simp only [CollatzResearch.WordTrace]
  refine ⟨126233040468862936850237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84155360312575291233491 126233040468862936850237)
  ·
    refine ⟨47337390175823601318839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126233040468862936850237 47337390175823601318839)
    ·
      refine ⟨71006085263735401978259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47337390175823601318839 71006085263735401978259)
      ·
        refine ⟨106509127895603102967389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71006085263735401978259 106509127895603102967389)
        ·
          refine ⟨39940922960851163612771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106509127895603102967389 39940922960851163612771)
          ·
            refine ⟨59911384441276745419157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39940922960851163612771 59911384441276745419157)
            ·
              refine ⟨2808346145684847441523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59911384441276745419157 2808346145684847441523)
              ·
                refine ⟨4212519218527271162285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2808346145684847441523 4212519218527271162285)
                ·
                  refine ⟨1579694706947726685857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4212519218527271162285 1579694706947726685857)
                  ·
                    rfl

theorem cell20_3461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_3461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3461 prefixEnd_3461 := by exact prefixLift 3461
  have htrace : WordTrace (prefixWord ++ tailWord_3461) baseStart_3461 baseEnd_3461 := by
    simpa [prefixWord, tailWord_3461, baseEnd_3461] using wordTrace_append hprefix tailTrace_3461
  have hstable : (prefixWord ++ tailWord_3461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461).length < 2 ^ (prefixWord ++ tailWord_3461).sum := by decide
  have hdescent : baseEnd_3461 < baseStart_3461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 5]
def baseStart_3503 : Nat := 118140960795 + 3503 * 2 ^ 59
def prefixEnd_3503 : Nat := 4983230072969 + 3 ^ 40 * 3503 * 2
def baseEnd_3503 : Nat := 1598864651382247285685

theorem tailTrace_3503 : CollatzResearch.WordTrace tailWord_3503 prefixEnd_3503 1598864651382247285685 := by
  unfold tailWord_3503
  simp only [CollatzResearch.WordTrace]
  refine ⟨127764906316704109879163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85176604211136073252775 127764906316704109879163)
  ·
    refine ⟨191647359475056164818745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127764906316704109879163 191647359475056164818745)
    ·
      refine ⟨143735519606292123614059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191647359475056164818745 143735519606292123614059)
      ·
        refine ⟨215603279409438185421089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143735519606292123614059 215603279409438185421089)
        ·
          refine ⟨161702459557078639065817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215603279409438185421089 161702459557078639065817)
          ·
            refine ⟨121276844667808979299363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161702459557078639065817 121276844667808979299363)
            ·
              refine ⟨181915267001713468949045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121276844667808979299363 181915267001713468949045)
              ·
                refine ⟨17054556281410637713973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181915267001713468949045 17054556281410637713973)
                ·
                  refine ⟨1598864651382247285685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17054556281410637713973 1598864651382247285685)
                  ·
                    rfl

theorem cell20_3503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_3503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3503 prefixEnd_3503 := by exact prefixLift 3503
  have htrace : WordTrace (prefixWord ++ tailWord_3503) baseStart_3503 baseEnd_3503 := by
    simpa [prefixWord, tailWord_3503, baseEnd_3503] using wordTrace_append hprefix tailTrace_3503
  have hstable : (prefixWord ++ tailWord_3503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503).length < 2 ^ (prefixWord ++ tailWord_3503).sum := by decide
  have hdescent : baseEnd_3503 < baseStart_3503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520 : List Nat := [2, 1, 1, 2, 3, 1, 4, 3, 3]
def baseStart_3520 : Nat := 118140960795 + 3520 * 2 ^ 59
def prefixEnd_3520 : Nat := 4983230072969 + 3 ^ 40 * 3520 * 2
def baseEnd_3520 : Nat := 1606623914605743718949

theorem tailTrace_3520 : CollatzResearch.WordTrace tailWord_3520 prefixEnd_3520 1606623914605743718949 := by
  unfold tailWord_3520
  simp only [CollatzResearch.WordTrace]
  refine ⟨64192473627558006624007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85589964836744008832009 64192473627558006624007)
  ·
    refine ⟨96288710441337009936011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64192473627558006624007 96288710441337009936011)
    ·
      refine ⟨144433065662005514904017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96288710441337009936011 144433065662005514904017)
      ·
        refine ⟨108324799246504136178013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144433065662005514904017 108324799246504136178013)
        ·
          refine ⟨40621799717439051066755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108324799246504136178013 40621799717439051066755)
          ·
            refine ⟨60932699576158576600133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40621799717439051066755 60932699576158576600133)
            ·
              refine ⟨11424881170529733112525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60932699576158576600133 11424881170529733112525)
              ·
                refine ⟨4284330438948649917197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11424881170529733112525 4284330438948649917197)
                ·
                  refine ⟨1606623914605743718949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4284330438948649917197 1606623914605743718949)
                  ·
                    rfl

theorem cell20_3520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 3].length) (baseStart_3520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3520 prefixEnd_3520 := by exact prefixLift 3520
  have htrace : WordTrace (prefixWord ++ tailWord_3520) baseStart_3520 baseEnd_3520 := by
    simpa [prefixWord, tailWord_3520, baseEnd_3520] using wordTrace_append hprefix tailTrace_3520
  have hstable : (prefixWord ++ tailWord_3520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520).length < 2 ^ (prefixWord ++ tailWord_3520).sum := by decide
  have hdescent : baseEnd_3520 < baseStart_3520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3527 : List Nat := [1, 1, 4, 1, 1, 3, 3, 2, 4]
def baseStart_3527 : Nat := 118140960795 + 3527 * 2 ^ 59
def prefixEnd_3527 : Nat := 4983230072969 + 3 ^ 40 * 3527 * 2
def baseEnd_3527 : Nat := 1609818905344830485587

theorem tailTrace_3527 : CollatzResearch.WordTrace tailWord_3527 prefixEnd_3527 1609818905344830485587 := by
  unfold tailWord_3527
  simp only [CollatzResearch.WordTrace]
  refine ⟨128640258229756208752835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85760172153170805835223 128640258229756208752835)
  ·
    refine ⟨192960387344634313129253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128640258229756208752835 192960387344634313129253)
    ·
      refine ⟨36180072627118933711735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192960387344634313129253 36180072627118933711735)
      ·
        refine ⟨54270108940678400567603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36180072627118933711735 54270108940678400567603)
        ·
          refine ⟨81405163411017600851405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54270108940678400567603 81405163411017600851405)
          ·
            refine ⟨30526936279131600319277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81405163411017600851405 30526936279131600319277)
            ·
              refine ⟨11447601104674350119729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30526936279131600319277 11447601104674350119729)
              ·
                refine ⟨8585700828505762589797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11447601104674350119729 8585700828505762589797)
                ·
                  refine ⟨1609818905344830485587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8585700828505762589797 1609818905344830485587)
                  ·
                    rfl

theorem cell20_3527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 4].length) (baseStart_3527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3527 prefixEnd_3527 := by exact prefixLift 3527
  have htrace : WordTrace (prefixWord ++ tailWord_3527) baseStart_3527 baseEnd_3527 := by
    simpa [prefixWord, tailWord_3527, baseEnd_3527] using wordTrace_append hprefix tailTrace_3527
  have hstable : (prefixWord ++ tailWord_3527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3527).length < 2 ^ (prefixWord ++ tailWord_3527).sum := by decide
  have hdescent : baseEnd_3527 < baseStart_3527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534 : List Nat := [4, 1, 1, 1, 2, 1, 2, 8]
def baseStart_3534 : Nat := 118140960795 + 3534 * 2 ^ 59
def prefixEnd_3534 : Nat := 4983230072969 + 3 ^ 40 * 3534 * 2
def baseEnd_3534 : Nat := 537671298694639084075

theorem tailTrace_3534 : CollatzResearch.WordTrace tailWord_3534 prefixEnd_3534 537671298694639084075 := by
  unfold tailWord_3534
  simp only [CollatzResearch.WordTrace]
  refine ⟨16111946150549550532207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85930379469597602838437 16111946150549550532207)
  ·
    refine ⟨24167919225824325798311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16111946150549550532207 24167919225824325798311)
    ·
      refine ⟨36251878838736488697467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24167919225824325798311 36251878838736488697467)
      ·
        refine ⟨54377818258104733046201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36251878838736488697467 54377818258104733046201)
        ·
          refine ⟨40783363693578549784651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54377818258104733046201 40783363693578549784651)
          ·
            refine ⟨61175045540367824676977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40783363693578549784651 61175045540367824676977)
            ·
              refine ⟨45881284155275868507733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61175045540367824676977 45881284155275868507733)
              ·
                refine ⟨537671298694639084075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 45881284155275868507733 537671298694639084075)
                ·
                  rfl

theorem cell20_3534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_3534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3534 prefixEnd_3534 := by exact prefixLift 3534
  have htrace : WordTrace (prefixWord ++ tailWord_3534) baseStart_3534 baseEnd_3534 := by
    simpa [prefixWord, tailWord_3534, baseEnd_3534] using wordTrace_append hprefix tailTrace_3534
  have hstable : (prefixWord ++ tailWord_3534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534).length < 2 ^ (prefixWord ++ tailWord_3534).sum := by decide
  have hdescent : baseEnd_3534 < baseStart_3534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540 : List Nat := [2, 4, 1, 2, 3, 1, 2, 3, 2]
def baseStart_3540 : Nat := 118140960795 + 3540 * 2 ^ 59
def prefixEnd_3540 : Nat := 4983230072969 + 3 ^ 40 * 3540 * 2
def baseEnd_3540 : Nat := 1615752459574563052201

theorem tailTrace_3540 : CollatzResearch.WordTrace tailWord_3540 prefixEnd_3540 1615752459574563052201 := by
  unfold tailWord_3540
  simp only [CollatzResearch.WordTrace]
  refine ⟨64557203591329714488037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86076271455106285984049 64557203591329714488037)
  ·
    refine ⟨12104475673374321466507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64557203591329714488037 12104475673374321466507)
    ·
      refine ⟨18156713510061482199761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12104475673374321466507 18156713510061482199761)
      ·
        refine ⟨13617535132546111649821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18156713510061482199761 13617535132546111649821)
        ·
          refine ⟨5106575674704791868683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13617535132546111649821 5106575674704791868683)
          ·
            refine ⟨7659863512057187803025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5106575674704791868683 7659863512057187803025)
            ·
              refine ⟨5744897634042890852269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7659863512057187803025 5744897634042890852269)
              ·
                refine ⟨2154336612766084069601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5744897634042890852269 2154336612766084069601)
                ·
                  refine ⟨1615752459574563052201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2154336612766084069601 1615752459574563052201)
                  ·
                    rfl

theorem cell20_3540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_3540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3540 prefixEnd_3540 := by exact prefixLift 3540
  have htrace : WordTrace (prefixWord ++ tailWord_3540) baseStart_3540 baseEnd_3540 := by
    simpa [prefixWord, tailWord_3540, baseEnd_3540] using wordTrace_append hprefix tailTrace_3540
  have hstable : (prefixWord ++ tailWord_3540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540).length < 2 ^ (prefixWord ++ tailWord_3540).sum := by decide
  have hdescent : baseEnd_3540 < baseStart_3540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544 : List Nat := [2, 1, 2, 2, 2, 1, 3, 5, 2]
def baseStart_3544 : Nat := 118140960795 + 3544 * 2 ^ 59
def prefixEnd_3544 : Nat := 4983230072969 + 3 ^ 40 * 3544 * 2
def baseEnd_3544 : Nat := 1617578168568326918851

theorem tailTrace_3544 : CollatzResearch.WordTrace tailWord_3544 prefixEnd_3544 1617578168568326918851 := by
  unfold tailWord_3544
  simp only [CollatzResearch.WordTrace]
  refine ⟨64630149584084056060843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86173532778778741414457 64630149584084056060843)
  ·
    refine ⟨96945224376126084091265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64630149584084056060843 96945224376126084091265)
    ·
      refine ⟨72708918282094563068449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96945224376126084091265 72708918282094563068449)
      ·
        refine ⟨54531688711570922301337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72708918282094563068449 54531688711570922301337)
        ·
          refine ⟨40898766533678191726003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54531688711570922301337 40898766533678191726003)
          ·
            refine ⟨61348149800517287589005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40898766533678191726003 61348149800517287589005)
            ·
              refine ⟨23005556175193982845877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61348149800517287589005 23005556175193982845877)
              ·
                refine ⟨2156770891424435891801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23005556175193982845877 2156770891424435891801)
                ·
                  refine ⟨1617578168568326918851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2156770891424435891801 1617578168568326918851)
                  ·
                    rfl

theorem cell20_3544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 2].length) (baseStart_3544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3544 prefixEnd_3544 := by exact prefixLift 3544
  have htrace : WordTrace (prefixWord ++ tailWord_3544) baseStart_3544 baseEnd_3544 := by
    simpa [prefixWord, tailWord_3544, baseEnd_3544] using wordTrace_append hprefix tailTrace_3544
  have hstable : (prefixWord ++ tailWord_3544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544).length < 2 ^ (prefixWord ++ tailWord_3544).sum := by decide
  have hdescent : baseEnd_3544 < baseStart_3544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585 : List Nat := [1, 2, 4, 1, 5, 1, 2, 4]
def baseStart_3585 : Nat := 118140960795 + 3585 * 2 ^ 59
def prefixEnd_3585 : Nat := 4983230072969 + 3 ^ 40 * 3585 * 2
def baseEnd_3585 : Nat := 545430561918135517339

theorem tailTrace_3585 : CollatzResearch.WordTrace tailWord_3585 prefixEnd_3585 545430561918135517339 := by
  unfold tailWord_3585
  simp only [CollatzResearch.WordTrace]
  refine ⟨130755692019632114364209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87170461346421409576139 130755692019632114364209)
  ·
    refine ⟨98066769014724085773157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130755692019632114364209 98066769014724085773157)
    ·
      refine ⟨18387519190260766082467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98066769014724085773157 18387519190260766082467)
      ·
        refine ⟨27581278785391149123701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18387519190260766082467 27581278785391149123701)
        ·
          refine ⟨2585744886130420230347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27581278785391149123701 2585744886130420230347)
          ·
            refine ⟨3878617329195630345521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2585744886130420230347 3878617329195630345521)
            ·
              refine ⟨2908962996896722759141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3878617329195630345521 2908962996896722759141)
              ·
                refine ⟨545430561918135517339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2908962996896722759141 545430561918135517339)
                ·
                  rfl

theorem cell20_3585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 4].length) (baseStart_3585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3585 prefixEnd_3585 := by exact prefixLift 3585
  have htrace : WordTrace (prefixWord ++ tailWord_3585) baseStart_3585 baseEnd_3585 := by
    simpa [prefixWord, tailWord_3585, baseEnd_3585] using wordTrace_append hprefix tailTrace_3585
  have hstable : (prefixWord ++ tailWord_3585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585).length < 2 ^ (prefixWord ++ tailWord_3585).sum := by decide
  have hdescent : baseEnd_3585 < baseStart_3585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616 : List Nat := [2, 1, 1, 6, 1, 2, 3, 2, 2]
def baseStart_3616 : Nat := 118140960795 + 3616 * 2 ^ 59
def prefixEnd_3616 : Nat := 4983230072969 + 3 ^ 40 * 3616 * 2
def baseEnd_3616 : Nat := 1650440930456076518557

theorem tailTrace_3616 : CollatzResearch.WordTrace tailWord_3616 prefixEnd_3616 1650440930456076518557 := by
  unfold tailWord_3616
  simp only [CollatzResearch.WordTrace]
  refine ⟨65943177453662204371351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87924236604882939161801 65943177453662204371351)
  ·
    refine ⟨98914766180493306557027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65943177453662204371351 98914766180493306557027)
    ·
      refine ⟨148372149270739959835541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98914766180493306557027 148372149270739959835541)
      ·
        refine ⟨6954944497065935617291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 148372149270739959835541 6954944497065935617291)
        ·
          refine ⟨10432416745598903425937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6954944497065935617291 10432416745598903425937)
          ·
            refine ⟨7824312559199177569453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10432416745598903425937 7824312559199177569453)
            ·
              refine ⟨2934117209699691588545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7824312559199177569453 2934117209699691588545)
              ·
                refine ⟨2200587907274768691409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2934117209699691588545 2200587907274768691409)
                ·
                  refine ⟨1650440930456076518557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2200587907274768691409 1650440930456076518557)
                  ·
                    rfl

theorem cell20_3616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 2].length) (baseStart_3616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3616 prefixEnd_3616 := by exact prefixLift 3616
  have htrace : WordTrace (prefixWord ++ tailWord_3616) baseStart_3616 baseEnd_3616 := by
    simpa [prefixWord, tailWord_3616, baseEnd_3616] using wordTrace_append hprefix tailTrace_3616
  have hstable : (prefixWord ++ tailWord_3616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616).length < 2 ^ (prefixWord ++ tailWord_3616).sum := by decide
  have hdescent : baseEnd_3616 < baseStart_3616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630 : List Nat := [4, 1, 3, 1, 2, 1, 4, 1, 3]
def baseStart_3630 : Nat := 118140960795 + 3630 * 2 ^ 59
def prefixEnd_3630 : Nat := 4983230072969 + 3 ^ 40 * 3630 * 2
def baseEnd_3630 : Nat := 1656830911934250051833

theorem tailTrace_3630 : CollatzResearch.WordTrace tailWord_3630 prefixEnd_3630 1656830911934250051833 := by
  unfold tailWord_3630
  simp only [CollatzResearch.WordTrace]
  refine ⟨16549622107075599969043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88264651237736533168229 16549622107075599969043)
  ·
    refine ⟨24824433160613399953565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16549622107075599969043 24824433160613399953565)
    ·
      refine ⟨9309162435230024982587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24824433160613399953565 9309162435230024982587)
      ·
        refine ⟨13963743652845037473881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9309162435230024982587 13963743652845037473881)
        ·
          refine ⟨10472807739633778105411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13963743652845037473881 10472807739633778105411)
          ·
            refine ⟨15709211609450667158117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10472807739633778105411 15709211609450667158117)
            ·
              refine ⟨2945477176772000092147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15709211609450667158117 2945477176772000092147)
              ·
                refine ⟨4418215765158000138221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2945477176772000092147 4418215765158000138221)
                ·
                  refine ⟨1656830911934250051833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4418215765158000138221 1656830911934250051833)
                  ·
                    rfl

theorem cell20_3630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_3630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3630 prefixEnd_3630 := by exact prefixLift 3630
  have htrace : WordTrace (prefixWord ++ tailWord_3630) baseStart_3630 baseEnd_3630 := by
    simpa [prefixWord, tailWord_3630, baseEnd_3630] using wordTrace_append hprefix tailTrace_3630
  have hstable : (prefixWord ++ tailWord_3630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630).length < 2 ^ (prefixWord ++ tailWord_3630).sum := by decide
  have hdescent : baseEnd_3630 < baseStart_3630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658 : List Nat := [3, 1, 2, 1, 1, 3, 2, 5, 2]
def baseStart_3658 : Nat := 118140960795 + 3658 * 2 ^ 59
def prefixEnd_3658 : Nat := 4983230072969 + 3 ^ 40 * 3658 * 2
def baseEnd_3658 : Nat := 1669610874890597118385

theorem tailTrace_3658 : CollatzResearch.WordTrace tailWord_3658 prefixEnd_3658 1669610874890597118385 := by
  unfold tailWord_3658
  simp only [CollatzResearch.WordTrace]
  refine ⟨33354555188791395442907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88945480503443721181085 33354555188791395442907)
  ·
    refine ⟨50031832783187093164361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33354555188791395442907 50031832783187093164361)
    ·
      refine ⟨37523874587390319873271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50031832783187093164361 37523874587390319873271)
      ·
        refine ⟨56285811881085479809907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37523874587390319873271 56285811881085479809907)
        ·
          refine ⟨84428717821628219714861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56285811881085479809907 84428717821628219714861)
          ·
            refine ⟨31660769183110582393073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84428717821628219714861 31660769183110582393073)
            ·
              refine ⟨23745576887332936794805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31660769183110582393073 23745576887332936794805)
              ·
                refine ⟨2226147833187462824513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23745576887332936794805 2226147833187462824513)
                ·
                  refine ⟨1669610874890597118385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2226147833187462824513 1669610874890597118385)
                  ·
                    rfl

theorem cell20_3658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 2].length) (baseStart_3658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3658 prefixEnd_3658 := by exact prefixLift 3658
  have htrace : WordTrace (prefixWord ++ tailWord_3658) baseStart_3658 baseEnd_3658 := by
    simpa [prefixWord, tailWord_3658, baseEnd_3658] using wordTrace_append hprefix tailTrace_3658
  have hstable : (prefixWord ++ tailWord_3658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658).length < 2 ^ (prefixWord ++ tailWord_3658).sum := by decide
  have hdescent : baseEnd_3658 < baseStart_3658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713 : List Nat := [1, 2, 4, 2, 1, 3, 2, 3, 2]
def baseStart_3713 : Nat := 118140960795 + 3713 * 2 ^ 59
def prefixEnd_3713 : Nat := 4983230072969 + 3 ^ 40 * 3713 * 2
def baseEnd_3713 : Nat := 1694714373554850284827

theorem tailTrace_3713 : CollatzResearch.WordTrace tailWord_3713 prefixEnd_3713 1694714373554850284827 := by
  unfold tailWord_3713
  simp only [CollatzResearch.WordTrace]
  refine ⟨135424235555909975023793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90282823703939983349195 135424235555909975023793)
  ·
    refine ⟨101568176666932481267845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135424235555909975023793 101568176666932481267845)
    ·
      refine ⟨19044033125049840237721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101568176666932481267845 19044033125049840237721)
      ·
        refine ⟨14283024843787380178291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19044033125049840237721 14283024843787380178291)
        ·
          refine ⟨21424537265681070267437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14283024843787380178291 21424537265681070267437)
          ·
            refine ⟨8034201474630401350289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21424537265681070267437 8034201474630401350289)
            ·
              refine ⟨6025651105972801012717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8034201474630401350289 6025651105972801012717)
              ·
                refine ⟨2259619164739800379769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6025651105972801012717 2259619164739800379769)
                ·
                  refine ⟨1694714373554850284827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2259619164739800379769 1694714373554850284827)
                  ·
                    rfl

theorem cell20_3713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 2].length) (baseStart_3713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3713 prefixEnd_3713 := by exact prefixLift 3713
  have htrace : WordTrace (prefixWord ++ tailWord_3713) baseStart_3713 baseEnd_3713 := by
    simpa [prefixWord, tailWord_3713, baseEnd_3713] using wordTrace_append hprefix tailTrace_3713
  have hstable : (prefixWord ++ tailWord_3713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713).length < 2 ^ (prefixWord ++ tailWord_3713).sum := by decide
  have hdescent : baseEnd_3713 < baseStart_3713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758 : List Nat := [4, 1, 4, 1, 2, 1, 1, 6]
def baseStart_3758 : Nat := 118140960795 + 3758 * 2 ^ 59
def prefixEnd_3758 : Nat := 4983230072969 + 3 ^ 40 * 3758 * 2
def baseEnd_3758 : Nat := 571751199911564594881

theorem tailTrace_3758 : CollatzResearch.WordTrace tailWord_3758 prefixEnd_3758 571751199911564594881 := by
  unfold tailWord_3758
  simp only [CollatzResearch.WordTrace]
  refine ⟨17133190049110332551491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91377013595255106941285 17133190049110332551491)
  ·
    refine ⟨25699785073665498827237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17133190049110332551491 25699785073665498827237)
    ·
      refine ⟨4818709701312281030107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25699785073665498827237 4818709701312281030107)
      ·
        refine ⟨7228064551968421545161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4818709701312281030107 7228064551968421545161)
        ·
          refine ⟨5421048413976316158871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7228064551968421545161 5421048413976316158871)
          ·
            refine ⟨8131572620964474238307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5421048413976316158871 8131572620964474238307)
            ·
              refine ⟨12197358931446711357461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8131572620964474238307 12197358931446711357461)
              ·
                refine ⟨571751199911564594881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12197358931446711357461 571751199911564594881)
                ·
                  rfl

theorem cell20_3758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_3758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3758 prefixEnd_3758 := by exact prefixLift 3758
  have htrace : WordTrace (prefixWord ++ tailWord_3758) baseStart_3758 baseEnd_3758 := by
    simpa [prefixWord, tailWord_3758, baseEnd_3758] using wordTrace_append hprefix tailTrace_3758
  have hstable : (prefixWord ++ tailWord_3758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758).length < 2 ^ (prefixWord ++ tailWord_3758).sum := by decide
  have hdescent : baseEnd_3758 < baseStart_3758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 5]
def baseStart_3769 : Nat := 118140960795 + 3769 * 2 ^ 59
def prefixEnd_3769 : Nat := 4983230072969 + 3 ^ 40 * 3769 * 2
def baseEnd_3769 : Nat := 1720274299467544417931

theorem tailTrace_3769 : CollatzResearch.WordTrace tailWord_3769 prefixEnd_3769 1720274299467544417931 := by
  unfold tailWord_3769
  simp only [CollatzResearch.WordTrace]
  refine ⟨137466723353031539062361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91644482235354359374907 137466723353031539062361)
  ·
    refine ⟨103100042514773654296771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137466723353031539062361 103100042514773654296771)
    ·
      refine ⟨154650063772160481445157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103100042514773654296771 154650063772160481445157)
      ·
        refine ⟨28996886957280090270967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154650063772160481445157 28996886957280090270967)
        ·
          refine ⟨43495330435920135406451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28996886957280090270967 43495330435920135406451)
          ·
            refine ⟨65242995653880203109677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43495330435920135406451 65242995653880203109677)
            ·
              refine ⟨24466123370205076166129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65242995653880203109677 24466123370205076166129)
              ·
                refine ⟨18349592527653807124597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24466123370205076166129 18349592527653807124597)
                ·
                  refine ⟨1720274299467544417931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18349592527653807124597 1720274299467544417931)
                  ·
                    rfl

theorem cell20_3769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_3769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3769 prefixEnd_3769 := by exact prefixLift 3769
  have htrace : WordTrace (prefixWord ++ tailWord_3769) baseStart_3769 baseEnd_3769 := by
    simpa [prefixWord, tailWord_3769, baseEnd_3769] using wordTrace_append hprefix tailTrace_3769
  have hstable : (prefixWord ++ tailWord_3769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769).length < 2 ^ (prefixWord ++ tailWord_3769).sum := by decide
  have hdescent : baseEnd_3769 < baseStart_3769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_3782 : Nat := 118140960795 + 3782 * 2 ^ 59
def prefixEnd_3782 : Nat := 4983230072969 + 3 ^ 40 * 3782 * 2
def baseEnd_3782 : Nat := 1726207853697276984545

theorem tailTrace_3782 : CollatzResearch.WordTrace tailWord_3782 prefixEnd_3782 1726207853697276984545 := by
  unfold tailWord_3782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4310652259560461227675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 91960581537289839523733 4310652259560461227675)
  ·
    refine ⟨6465978389340691841513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4310652259560461227675 6465978389340691841513)
    ·
      refine ⟨4849483792005518881135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6465978389340691841513 4849483792005518881135)
      ·
        refine ⟨7274225688008278321703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4849483792005518881135 7274225688008278321703)
        ·
          refine ⟨10911338532012417482555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7274225688008278321703 10911338532012417482555)
          ·
            refine ⟨16367007798018626223833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10911338532012417482555 16367007798018626223833)
            ·
              refine ⟨12275255848513969667875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16367007798018626223833 12275255848513969667875)
              ·
                refine ⟨18412883772770954501813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12275255848513969667875 18412883772770954501813)
                ·
                  refine ⟨1726207853697276984545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18412883772770954501813 1726207853697276984545)
                  ·
                    rfl

theorem cell20_3782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_3782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3782 prefixEnd_3782 := by exact prefixLift 3782
  have htrace : WordTrace (prefixWord ++ tailWord_3782) baseStart_3782 baseEnd_3782 := by
    simpa [prefixWord, tailWord_3782, baseEnd_3782] using wordTrace_append hprefix tailTrace_3782
  have hstable : (prefixWord ++ tailWord_3782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782).length < 2 ^ (prefixWord ++ tailWord_3782).sum := by decide
  have hdescent : baseEnd_3782 < baseStart_3782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789 : List Nat := [1, 6, 2, 1, 1, 1, 3, 1, 4]
def baseStart_3789 : Nat := 118140960795 + 3789 * 2 ^ 59
def prefixEnd_3789 : Nat := 4983230072969 + 3 ^ 40 * 3789 * 2
def baseEnd_3789 : Nat := 1729402844436363751183

theorem tailTrace_3789 : CollatzResearch.WordTrace tailWord_3789 prefixEnd_3789 1729402844436363751183 := by
  unfold tailWord_3789
  simp only [CollatzResearch.WordTrace]
  refine ⟨138196183280574954790421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92130788853716636526947 138196183280574954790421)
  ·
    refine ⟨6477946091276951005801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 138196183280574954790421 6477946091276951005801)
    ·
      refine ⟨4858459568457713254351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6477946091276951005801 4858459568457713254351)
      ·
        refine ⟨7287689352686569881527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4858459568457713254351 7287689352686569881527)
        ·
          refine ⟨10931534029029854822291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7287689352686569881527 10931534029029854822291)
          ·
            refine ⟨16397301043544782233437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10931534029029854822291 16397301043544782233437)
            ·
              refine ⟨6148987891329293337539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16397301043544782233437 6148987891329293337539)
              ·
                refine ⟨9223481836993940006309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6148987891329293337539 9223481836993940006309)
                ·
                  refine ⟨1729402844436363751183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9223481836993940006309 1729402844436363751183)
                  ·
                    rfl

theorem cell20_3789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_3789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3789 prefixEnd_3789 := by exact prefixLift 3789
  have htrace : WordTrace (prefixWord ++ tailWord_3789) baseStart_3789 baseEnd_3789 := by
    simpa [prefixWord, tailWord_3789, baseEnd_3789] using wordTrace_append hprefix tailTrace_3789
  have hstable : (prefixWord ++ tailWord_3789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789).length < 2 ^ (prefixWord ++ tailWord_3789).sum := by decide
  have hdescent : baseEnd_3789 < baseStart_3789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793 : List Nat := [1, 2, 2, 1, 2, 4, 3, 1, 4]
def baseStart_3793 : Nat := 118140960795 + 3793 * 2 ^ 59
def prefixEnd_3793 : Nat := 4983230072969 + 3 ^ 40 * 3793 * 2
def baseEnd_3793 : Nat := 1731228553430127617833

theorem tailTrace_3793 : CollatzResearch.WordTrace tailWord_3793 prefixEnd_3793 1731228553430127617833 := by
  unfold tailWord_3793
  simp only [CollatzResearch.WordTrace]
  refine ⟨138342075266083637936033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92228050177389091957355 138342075266083637936033)
  ·
    refine ⟨103756556449562728452025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138342075266083637936033 103756556449562728452025)
    ·
      refine ⟨77817417337172046339019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103756556449562728452025 77817417337172046339019)
      ·
        refine ⟨116726126005758069508529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77817417337172046339019 116726126005758069508529)
        ·
          refine ⟨87544594504318552131397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116726126005758069508529 87544594504318552131397)
          ·
            refine ⟨16414611469559728524637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87544594504318552131397 16414611469559728524637)
            ·
              refine ⟨6155479301084898196739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16414611469559728524637 6155479301084898196739)
              ·
                refine ⟨9233218951627347295109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6155479301084898196739 9233218951627347295109)
                ·
                  refine ⟨1731228553430127617833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9233218951627347295109 1731228553430127617833)
                  ·
                    rfl

theorem cell20_3793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_3793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3793 prefixEnd_3793 := by exact prefixLift 3793
  have htrace : WordTrace (prefixWord ++ tailWord_3793) baseStart_3793 baseEnd_3793 := by
    simpa [prefixWord, tailWord_3793, baseEnd_3793] using wordTrace_append hprefix tailTrace_3793
  have hstable : (prefixWord ++ tailWord_3793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793).length < 2 ^ (prefixWord ++ tailWord_3793).sum := by decide
  have hdescent : baseEnd_3793 < baseStart_3793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800 : List Nat := [2, 1, 2, 2, 3, 1, 4, 5]
def baseStart_3800 : Nat := 118140960795 + 3800 * 2 ^ 59
def prefixEnd_3800 : Nat := 4983230072969 + 3 ^ 40 * 3800 * 2
def baseEnd_3800 : Nat := 578141181389738128157

theorem tailTrace_3800 : CollatzResearch.WordTrace tailWord_3800 prefixEnd_3800 578141181389738128157 := by
  unfold tailWord_3800
  simp only [CollatzResearch.WordTrace]
  refine ⟨69298693120361916720427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92398257493815888960569 69298693120361916720427)
  ·
    refine ⟨103948039680542875080641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69298693120361916720427 103948039680542875080641)
    ·
      refine ⟨77961029760407156310481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103948039680542875080641 77961029760407156310481)
      ·
        refine ⟨58470772320305367232861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77961029760407156310481 58470772320305367232861)
        ·
          refine ⟨21926539620114512712323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58470772320305367232861 21926539620114512712323)
          ·
            refine ⟨32889809430171769068485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21926539620114512712323 32889809430171769068485)
            ·
              refine ⟨6166839268157206700341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32889809430171769068485 6166839268157206700341)
              ·
                refine ⟨578141181389738128157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6166839268157206700341 578141181389738128157)
                ·
                  rfl

theorem cell20_3800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_3800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3800 prefixEnd_3800 := by exact prefixLift 3800
  have htrace : WordTrace (prefixWord ++ tailWord_3800) baseStart_3800 baseEnd_3800 := by
    simpa [prefixWord, tailWord_3800, baseEnd_3800] using wordTrace_append hprefix tailTrace_3800
  have hstable : (prefixWord ++ tailWord_3800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800).length < 2 ^ (prefixWord ++ tailWord_3800).sum := by decide
  have hdescent : baseEnd_3800 < baseStart_3800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838 : List Nat := [4, 2, 2, 1, 11]
def baseStart_3838 : Nat := 118140960795 + 3838 * 2 ^ 59
def prefixEnd_3838 : Nat := 4983230072969 + 3 ^ 40 * 3838 * 2
def baseEnd_3838 : Nat := 21626762711234211329

theorem tailTrace_3838 : CollatzResearch.WordTrace tailWord_3838 prefixEnd_3838 21626762711234211329 := by
  unfold tailWord_3838
  simp only [CollatzResearch.WordTrace]
  refine ⟨17497920012882040415521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93322240068704215549445 17497920012882040415521)
  ·
    refine ⟨13123440009661530311641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17497920012882040415521 13123440009661530311641)
    ·
      refine ⟨9842580007246147733731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13123440009661530311641 9842580007246147733731)
      ·
        refine ⟨14763870010869221600597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9842580007246147733731 14763870010869221600597)
        ·
          refine ⟨21626762711234211329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 14763870010869221600597 21626762711234211329)
          ·
            rfl

theorem cell20_3838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 11].length) (baseStart_3838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3838 prefixEnd_3838 := by exact prefixLift 3838
  have htrace : WordTrace (prefixWord ++ tailWord_3838) baseStart_3838 baseEnd_3838 := by
    simpa [prefixWord, tailWord_3838, baseEnd_3838] using wordTrace_append hprefix tailTrace_3838
  have hstable : (prefixWord ++ tailWord_3838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838).length < 2 ^ (prefixWord ++ tailWord_3838).sum := by decide
  have hdescent : baseEnd_3838 < baseStart_3838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844 : List Nat := [2, 3, 2, 2, 1, 4, 2, 2, 2]
def baseStart_3844 : Nat := 118140960795 + 3844 * 2 ^ 59
def prefixEnd_3844 : Nat := 4983230072969 + 3 ^ 40 * 3844 * 2
def baseEnd_3844 : Nat := 1754506343100616917625

theorem tailTrace_3844 : CollatzResearch.WordTrace tailWord_3844 prefixEnd_3844 1754506343100616917625 := by
  unfold tailWord_3844
  simp only [CollatzResearch.WordTrace]
  refine ⟨70101099040659674021293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93468132054212898695057 70101099040659674021293)
  ·
    refine ⟨26287912140247377757985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70101099040659674021293 26287912140247377757985)
    ·
      refine ⟨19715934105185533318489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26287912140247377757985 19715934105185533318489)
      ·
        refine ⟨14786950578889149988867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19715934105185533318489 14786950578889149988867)
        ·
          refine ⟨22180425868333724983301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14786950578889149988867 22180425868333724983301)
          ·
            refine ⟨4158829850312573434369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22180425868333724983301 4158829850312573434369)
            ·
              refine ⟨3119122387734430075777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4158829850312573434369 3119122387734430075777)
              ·
                refine ⟨2339341790800822556833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3119122387734430075777 2339341790800822556833)
                ·
                  refine ⟨1754506343100616917625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2339341790800822556833 1754506343100616917625)
                  ·
                    rfl

theorem cell20_3844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_3844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3844 prefixEnd_3844 := by exact prefixLift 3844
  have htrace : WordTrace (prefixWord ++ tailWord_3844) baseStart_3844 baseEnd_3844 := by
    simpa [prefixWord, tailWord_3844, baseEnd_3844] using wordTrace_append hprefix tailTrace_3844
  have hstable : (prefixWord ++ tailWord_3844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844).length < 2 ^ (prefixWord ++ tailWord_3844).sum := by decide
  have hdescent : baseEnd_3844 < baseStart_3844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848 : List Nat := [2, 1, 3, 2, 2, 1, 3, 4, 2]
def baseStart_3848 : Nat := 118140960795 + 3848 * 2 ^ 59
def prefixEnd_3848 : Nat := 4983230072969 + 3 ^ 40 * 3848 * 2
def baseEnd_3848 : Nat := 1756332052094380784275

theorem tailTrace_3848 : CollatzResearch.WordTrace tailWord_3848 prefixEnd_3848 1756332052094380784275 := by
  unfold tailWord_3848
  simp only [CollatzResearch.WordTrace]
  refine ⟨70174045033414015594099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93565393377885354125465 70174045033414015594099)
  ·
    refine ⟨105261067550121023391149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70174045033414015594099 105261067550121023391149)
    ·
      refine ⟨39472900331295383771681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105261067550121023391149 39472900331295383771681)
      ·
        refine ⟨29604675248471537828761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39472900331295383771681 29604675248471537828761)
        ·
          refine ⟨22203506436353653371571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29604675248471537828761 22203506436353653371571)
          ·
            refine ⟨33305259654530480057357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22203506436353653371571 33305259654530480057357)
            ·
              refine ⟨12489472370448930021509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33305259654530480057357 12489472370448930021509)
              ·
                refine ⟨2341776069459174379033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12489472370448930021509 2341776069459174379033)
                ·
                  refine ⟨1756332052094380784275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2341776069459174379033 1756332052094380784275)
                  ·
                    rfl

theorem cell20_3848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 2].length) (baseStart_3848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3848 prefixEnd_3848 := by exact prefixLift 3848
  have htrace : WordTrace (prefixWord ++ tailWord_3848) baseStart_3848 baseEnd_3848 := by
    simpa [prefixWord, tailWord_3848, baseEnd_3848] using wordTrace_append hprefix tailTrace_3848
  have hstable : (prefixWord ++ tailWord_3848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848).length < 2 ^ (prefixWord ++ tailWord_3848).sum := by decide
  have hdescent : baseEnd_3848 < baseStart_3848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859 : List Nat := [1, 1, 1, 2, 1, 3, 2, 9]
def baseStart_3859 : Nat := 118140960795 + 3859 * 2 ^ 59
def prefixEnd_3859 : Nat := 4983230072969 + 3 ^ 40 * 3859 * 2
def baseEnd_3859 : Nat := 587117583942410472521

theorem tailTrace_3859 : CollatzResearch.WordTrace tailWord_3859 prefixEnd_3859 587117583942410472521 := by
  unfold tailWord_3859
  simp only [CollatzResearch.WordTrace]
  refine ⟨140749293026976909838631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93832862017984606559087 140749293026976909838631)
  ·
    refine ⟨211123939540465364757947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140749293026976909838631 211123939540465364757947)
    ·
      refine ⟨316685909310698047136921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211123939540465364757947 316685909310698047136921)
      ·
        refine ⟨237514431983023535352691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316685909310698047136921 237514431983023535352691)
        ·
          refine ⟨356271647974535303029037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237514431983023535352691 356271647974535303029037)
          ·
            refine ⟨133601867990450738635889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356271647974535303029037 133601867990450738635889)
            ·
              refine ⟨100201400992838053976917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133601867990450738635889 100201400992838053976917)
              ·
                refine ⟨587117583942410472521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 100201400992838053976917 587117583942410472521)
                ·
                  rfl

theorem cell20_3859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 9].length) (baseStart_3859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3859 prefixEnd_3859 := by exact prefixLift 3859
  have htrace : WordTrace (prefixWord ++ tailWord_3859) baseStart_3859 baseEnd_3859 := by
    simpa [prefixWord, tailWord_3859, baseEnd_3859] using wordTrace_append hprefix tailTrace_3859
  have hstable : (prefixWord ++ tailWord_3859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859).length < 2 ^ (prefixWord ++ tailWord_3859).sum := by decide
  have hdescent : baseEnd_3859 < baseStart_3859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900 : List Nat := [2, 2, 2, 2, 1, 1, 5, 2, 3]
def baseStart_3900 : Nat := 118140960795 + 3900 * 2 ^ 59
def prefixEnd_3900 : Nat := 4983230072969 + 3 ^ 40 * 3900 * 2
def baseEnd_3900 : Nat := 1780066269013311050729

theorem tailTrace_3900 : CollatzResearch.WordTrace tailWord_3900 prefixEnd_3900 1780066269013311050729 := by
  unfold tailWord_3900
  simp only [CollatzResearch.WordTrace]
  refine ⟨71122342939220456040577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94829790585627274720769 71122342939220456040577)
  ·
    refine ⟨53341757204415342030433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71122342939220456040577 53341757204415342030433)
    ·
      refine ⟨40006317903311506522825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53341757204415342030433 40006317903311506522825)
      ·
        refine ⟨30004738427483629892119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40006317903311506522825 30004738427483629892119)
        ·
          refine ⟨45007107641225444838179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30004738427483629892119 45007107641225444838179)
          ·
            refine ⟨67510661461838167257269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45007107641225444838179 67510661461838167257269)
            ·
              refine ⟨6329124512047328180369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67510661461838167257269 6329124512047328180369)
              ·
                refine ⟨4746843384035496135277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6329124512047328180369 4746843384035496135277)
                ·
                  refine ⟨1780066269013311050729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4746843384035496135277 1780066269013311050729)
                  ·
                    rfl

theorem cell20_3900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_3900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3900 prefixEnd_3900 := by exact prefixLift 3900
  have htrace : WordTrace (prefixWord ++ tailWord_3900) baseStart_3900 baseEnd_3900 := by
    simpa [prefixWord, tailWord_3900, baseEnd_3900] using wordTrace_append hprefix tailTrace_3900
  have hstable : (prefixWord ++ tailWord_3900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900).length < 2 ^ (prefixWord ++ tailWord_3900).sum := by decide
  have hdescent : baseEnd_3900 < baseStart_3900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907 : List Nat := [1, 1, 1, 3, 1, 6, 2, 1, 4]
def baseStart_3907 : Nat := 118140960795 + 3907 * 2 ^ 59
def prefixEnd_3907 : Nat := 4983230072969 + 3 ^ 40 * 3907 * 2
def baseEnd_3907 : Nat := 1783261259752397817367

theorem tailTrace_3907 : CollatzResearch.WordTrace tailWord_3907 prefixEnd_3907 1783261259752397817367 := by
  unfold tailWord_3907
  simp only [CollatzResearch.WordTrace]
  refine ⟨142499996853081107585975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94999997902054071723983 142499996853081107585975)
  ·
    refine ⟨213749995279621661378963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142499996853081107585975 213749995279621661378963)
    ·
      refine ⟨320624992919432492068445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213749995279621661378963 320624992919432492068445)
      ·
        refine ⟨120234372344787184525667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320624992919432492068445 120234372344787184525667)
        ·
          refine ⟨180351558517180776788501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120234372344787184525667 180351558517180776788501)
          ·
            refine ⟨8453979305492848911961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 180351558517180776788501 8453979305492848911961)
            ·
              refine ⟨6340484479119636683971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8453979305492848911961 6340484479119636683971)
              ·
                refine ⟨9510726718679455025957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6340484479119636683971 9510726718679455025957)
                ·
                  refine ⟨1783261259752397817367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9510726718679455025957 1783261259752397817367)
                  ·
                    rfl

theorem cell20_3907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 4].length) (baseStart_3907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3907 prefixEnd_3907 := by exact prefixLift 3907
  have htrace : WordTrace (prefixWord ++ tailWord_3907) baseStart_3907 baseEnd_3907 := by
    simpa [prefixWord, tailWord_3907, baseEnd_3907] using wordTrace_append hprefix tailTrace_3907
  have hstable : (prefixWord ++ tailWord_3907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907).length < 2 ^ (prefixWord ++ tailWord_3907).sum := by decide
  have hdescent : baseEnd_3907 < baseStart_3907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 5]
def baseStart_3938 : Nat := 118140960795 + 3938 * 2 ^ 59
def prefixEnd_3938 : Nat := 4983230072969 + 3 ^ 40 * 3938 * 2
def baseEnd_3938 : Nat := 1797410504454067783907

theorem tailTrace_3938 : CollatzResearch.WordTrace tailWord_3938 prefixEnd_3938 1797410504454067783907 := by
  unfold tailWord_3938
  simp only [CollatzResearch.WordTrace]
  refine ⟨35907664935193350491117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95753773160515601309645 35907664935193350491117)
  ·
    refine ⟨13465374350697506434169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35907664935193350491117 13465374350697506434169)
    ·
      refine ⟨10099030763023129825627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13465374350697506434169 10099030763023129825627)
      ·
        refine ⟨15148546144534694738441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10099030763023129825627 15148546144534694738441)
        ·
          refine ⟨11361409608401021053831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15148546144534694738441 11361409608401021053831)
          ·
            refine ⟨17042114412601531580747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11361409608401021053831 17042114412601531580747)
            ·
              refine ⟨25563171618902297371121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17042114412601531580747 25563171618902297371121)
              ·
                refine ⟨19172378714176723028341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25563171618902297371121 19172378714176723028341)
                ·
                  refine ⟨1797410504454067783907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19172378714176723028341 1797410504454067783907)
                  ·
                    rfl

theorem cell20_3938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_3938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3938 prefixEnd_3938 := by exact prefixLift 3938
  have htrace : WordTrace (prefixWord ++ tailWord_3938) baseStart_3938 baseEnd_3938 := by
    simpa [prefixWord, tailWord_3938, baseEnd_3938] using wordTrace_append hprefix tailTrace_3938
  have hstable : (prefixWord ++ tailWord_3938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938).length < 2 ^ (prefixWord ++ tailWord_3938).sum := by decide
  have hdescent : baseEnd_3938 < baseStart_3938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958 : List Nat := [5, 1, 1, 3, 3, 1, 1, 1, 4]
def baseStart_3958 : Nat := 118140960795 + 3958 * 2 ^ 59
def prefixEnd_3958 : Nat := 4983230072969 + 3 ^ 40 * 3958 * 2
def baseEnd_3958 : Nat := 1806539049422887117159

theorem tailTrace_3958 : CollatzResearch.WordTrace tailWord_3958 prefixEnd_3958 1806539049422887117159 := by
  unfold tailWord_3958
  simp only [CollatzResearch.WordTrace]
  refine ⟨9022507479269801105783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96240079778877878461685 9022507479269801105783)
  ·
    refine ⟨13533761218904701658675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9022507479269801105783 13533761218904701658675)
    ·
      refine ⟨20300641828357052488013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13533761218904701658675 20300641828357052488013)
      ·
        refine ⟨7612740685633894683005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20300641828357052488013 7612740685633894683005)
        ·
          refine ⟨2854777757112710506127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7612740685633894683005 2854777757112710506127)
          ·
            refine ⟨4282166635669065759191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854777757112710506127 4282166635669065759191)
            ·
              refine ⟨6423249953503598638787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4282166635669065759191 6423249953503598638787)
              ·
                refine ⟨9634874930255397958181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6423249953503598638787 9634874930255397958181)
                ·
                  refine ⟨1806539049422887117159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9634874930255397958181 1806539049422887117159)
                  ·
                    rfl

theorem cell20_3958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_3958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_3958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_3958 prefixEnd_3958 := by exact prefixLift 3958
  have htrace : WordTrace (prefixWord ++ tailWord_3958) baseStart_3958 baseEnd_3958 := by
    simpa [prefixWord, tailWord_3958, baseEnd_3958] using wordTrace_append hprefix tailTrace_3958
  have hstable : (prefixWord ++ tailWord_3958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958).length < 2 ^ (prefixWord ++ tailWord_3958).sum := by decide
  have hdescent : baseEnd_3958 < baseStart_3958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017 : List Nat := [1, 2, 2, 4, 2, 1, 4, 2, 2]
def baseStart_4017 : Nat := 118140960795 + 4017 * 2 ^ 59
def prefixEnd_4017 : Nat := 4983230072969 + 3 ^ 40 * 4017 * 2
def baseEnd_4017 : Nat := 1833468257080904150251

theorem tailTrace_4017 : CollatzResearch.WordTrace tailWord_4017 prefixEnd_4017 1833468257080904150251 := by
  unfold tailWord_4017
  simp only [CollatzResearch.WordTrace]
  refine ⟨146512026454569894090305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97674684303046596060203 146512026454569894090305)
  ·
    refine ⟨109884019840927420567729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146512026454569894090305 109884019840927420567729)
    ·
      refine ⟨82413014880695565425797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109884019840927420567729 82413014880695565425797)
      ·
        refine ⟨15452440290130418517337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82413014880695565425797 15452440290130418517337)
        ·
          refine ⟨11589330217597813888003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15452440290130418517337 11589330217597813888003)
          ·
            refine ⟨17383995326396720832005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11589330217597813888003 17383995326396720832005)
            ·
              refine ⟨3259499123699385156001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17383995326396720832005 3259499123699385156001)
              ·
                refine ⟨2444624342774538867001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3259499123699385156001 2444624342774538867001)
                ·
                  refine ⟨1833468257080904150251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2444624342774538867001 1833468257080904150251)
                  ·
                    rfl

theorem cell20_4017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 2].length) (baseStart_4017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4017 prefixEnd_4017 := by exact prefixLift 4017
  have htrace : WordTrace (prefixWord ++ tailWord_4017) baseStart_4017 baseEnd_4017 := by
    simpa [prefixWord, tailWord_4017, baseEnd_4017] using wordTrace_append hprefix tailTrace_4017
  have hstable : (prefixWord ++ tailWord_4017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017).length < 2 ^ (prefixWord ++ tailWord_4017).sum := by decide
  have hdescent : baseEnd_4017 < baseStart_4017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 6]
def baseStart_4042 : Nat := 118140960795 + 4042 * 2 ^ 59
def prefixEnd_4042 : Nat := 4983230072969 + 3 ^ 40 * 4042 * 2
def baseEnd_4042 : Nat := 1844878938291928316815

theorem tailTrace_4042 : CollatzResearch.WordTrace tailWord_4042 prefixEnd_4042 1844878938291928316815 := by
  unfold tailWord_4042
  simp only [CollatzResearch.WordTrace]
  refine ⟨36855962840999790937595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98282567575999442500253 36855962840999790937595)
  ·
    refine ⟨55283944261499686406393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36855962840999790937595 55283944261499686406393)
    ·
      refine ⟨41462958196124764804795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55283944261499686406393 41462958196124764804795)
      ·
        refine ⟨62194437294187147207193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41462958196124764804795 62194437294187147207193)
        ·
          refine ⟨46645827970640360405395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62194437294187147207193 46645827970640360405395)
          ·
            refine ⟨69968741955960540608093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46645827970640360405395 69968741955960540608093)
            ·
              refine ⟨26238278233485202728035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69968741955960540608093 26238278233485202728035)
              ·
                refine ⟨39357417350227804092053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26238278233485202728035 39357417350227804092053)
                ·
                  refine ⟨1844878938291928316815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39357417350227804092053 1844878938291928316815)
                  ·
                    rfl

theorem cell20_4042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_4042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4042 prefixEnd_4042 := by exact prefixLift 4042
  have htrace : WordTrace (prefixWord ++ tailWord_4042) baseStart_4042 baseEnd_4042 := by
    simpa [prefixWord, tailWord_4042, baseEnd_4042] using wordTrace_append hprefix tailTrace_4042
  have hstable : (prefixWord ++ tailWord_4042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042).length < 2 ^ (prefixWord ++ tailWord_4042).sum := by decide
  have hdescent : baseEnd_4042 < baseStart_4042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080 : List Nat := [2, 1, 1, 1, 3, 2, 3, 3, 4]
def baseStart_4080 : Nat := 118140960795 + 4080 * 2 ^ 59
def prefixEnd_4080 : Nat := 4983230072969 + 3 ^ 40 * 4080 * 2
def baseEnd_4080 : Nat := 1862223173732685049993

theorem tailTrace_4080 : CollatzResearch.WordTrace tailWord_4080 prefixEnd_4080 1862223173732685049993 := by
  unfold tailWord_4080
  simp only [CollatzResearch.WordTrace]
  refine ⟨74404912613165826816847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99206550150887769089129 74404912613165826816847)
  ·
    refine ⟨111607368919748740225271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74404912613165826816847 111607368919748740225271)
    ·
      refine ⟨167411053379623110337907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111607368919748740225271 167411053379623110337907)
      ·
        refine ⟨251116580069434665506861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167411053379623110337907 251116580069434665506861)
        ·
          refine ⟨94168717526037999565073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251116580069434665506861 94168717526037999565073)
          ·
            refine ⟨70626538144528499673805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94168717526037999565073 70626538144528499673805)
            ·
              refine ⟨26484951804198187377677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70626538144528499673805 26484951804198187377677)
              ·
                refine ⟨9931856926574320266629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26484951804198187377677 9931856926574320266629)
                ·
                  refine ⟨1862223173732685049993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9931856926574320266629 1862223173732685049993)
                  ·
                    rfl

theorem cell20_4080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_4080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4080 prefixEnd_4080 := by exact prefixLift 4080
  have htrace : WordTrace (prefixWord ++ tailWord_4080) baseStart_4080 baseEnd_4080 := by
    simpa [prefixWord, tailWord_4080, baseEnd_4080] using wordTrace_append hprefix tailTrace_4080
  have hstable : (prefixWord ++ tailWord_4080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080).length < 2 ^ (prefixWord ++ tailWord_4080).sum := by decide
  have hdescent : baseEnd_4080 < baseStart_4080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086 : List Nat := [5, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_4086 : Nat := 118140960795 + 4086 * 2 ^ 59
def prefixEnd_4086 : Nat := 4983230072969 + 3 ^ 40 * 4086 * 2
def baseEnd_4086 : Nat := 1864961737223330849969

theorem tailTrace_4086 : CollatzResearch.WordTrace tailWord_4086 prefixEnd_4086 1864961737223330849969 := by
  unfold tailWord_4086
  simp only [CollatzResearch.WordTrace]
  refine ⟨9314291450287167397007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99352442136396452234741 9314291450287167397007)
  ·
    refine ⟨13971437175430751095511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9314291450287167397007 13971437175430751095511)
    ·
      refine ⟨20957155763146126643267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13971437175430751095511 20957155763146126643267)
      ·
        refine ⟨31435733644719189964901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20957155763146126643267 31435733644719189964901)
        ·
          refine ⟨5894200058384848118419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31435733644719189964901 5894200058384848118419)
          ·
            refine ⟨8841300087577272177629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5894200058384848118419 8841300087577272177629)
            ·
              refine ⟨3315487532841477066611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8841300087577272177629 3315487532841477066611)
              ·
                refine ⟨4973231299262215599917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3315487532841477066611 4973231299262215599917)
                ·
                  refine ⟨1864961737223330849969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4973231299262215599917 1864961737223330849969)
                  ·
                    rfl

theorem cell20_4086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_4086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4086 prefixEnd_4086 := by exact prefixLift 4086
  have htrace : WordTrace (prefixWord ++ tailWord_4086) baseStart_4086 baseEnd_4086 := by
    simpa [prefixWord, tailWord_4086, baseEnd_4086] using wordTrace_append hprefix tailTrace_4086
  have hstable : (prefixWord ++ tailWord_4086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086).length < 2 ^ (prefixWord ++ tailWord_4086).sum := by decide
  have hdescent : baseEnd_4086 < baseStart_4086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142 : List Nat := [4, 1, 3, 1, 1, 2, 1, 7]
def baseStart_4142 : Nat := 118140960795 + 4142 * 2 ^ 59
def prefixEnd_4142 : Nat := 4983230072969 + 3 ^ 40 * 4142 * 2
def baseEnd_4142 : Nat := 630173887712008327691

theorem tailTrace_4142 : CollatzResearch.WordTrace tailWord_4142 prefixEnd_4142 630173887712008327691 := by
  unfold tailWord_4142
  simp only [CollatzResearch.WordTrace]
  refine ⟨18883893875214530298835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100714100667810828260453 18883893875214530298835)
  ·
    refine ⟨28325840812821795448253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18883893875214530298835 28325840812821795448253)
    ·
      refine ⟨10622190304808173293095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28325840812821795448253 10622190304808173293095)
      ·
        refine ⟨15933285457212259939643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10622190304808173293095 15933285457212259939643)
        ·
          refine ⟨23899928185818389909465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15933285457212259939643 23899928185818389909465)
          ·
            refine ⟨17924946139363792432099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23899928185818389909465 17924946139363792432099)
            ·
              refine ⟨26887419209045688648149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17924946139363792432099 26887419209045688648149)
              ·
                refine ⟨630173887712008327691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26887419209045688648149 630173887712008327691)
                ·
                  rfl

theorem cell20_4142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_4142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4142 prefixEnd_4142 := by exact prefixLift 4142
  have htrace : WordTrace (prefixWord ++ tailWord_4142) baseStart_4142 baseEnd_4142 := by
    simpa [prefixWord, tailWord_4142, baseEnd_4142] using wordTrace_append hprefix tailTrace_4142
  have hstable : (prefixWord ++ tailWord_4142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142).length < 2 ^ (prefixWord ++ tailWord_4142).sum := by decide
  have hdescent : baseEnd_4142 < baseStart_4142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145 : List Nat := [1, 2, 2, 3, 1, 5, 2, 1, 3]
def baseStart_4145 : Nat := 118140960795 + 4145 * 2 ^ 59
def prefixEnd_4145 : Nat := 4983230072969 + 3 ^ 40 * 4145 * 2
def baseEnd_4145 : Nat := 1891890944881347883061

theorem tailTrace_4145 : CollatzResearch.WordTrace tailWord_4145 prefixEnd_4145 1891890944881347883061 := by
  unfold tailWord_4145
  simp only [CollatzResearch.WordTrace]
  refine ⟨151180569990847754749889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100787046660565169833259 151180569990847754749889)
  ·
    refine ⟨113385427493135816062417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151180569990847754749889 113385427493135816062417)
    ·
      refine ⟨85039070619851862046813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113385427493135816062417 85039070619851862046813)
      ·
        refine ⟨31889651482444448267555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85039070619851862046813 31889651482444448267555)
        ·
          refine ⟨47834477223666672401333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31889651482444448267555 47834477223666672401333)
          ·
            refine ⟨4484482239718750537625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47834477223666672401333 4484482239718750537625)
            ·
              refine ⟨3363361679789062903219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4484482239718750537625 3363361679789062903219)
              ·
                refine ⟨5045042519683594354829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3363361679789062903219 5045042519683594354829)
                ·
                  refine ⟨1891890944881347883061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5045042519683594354829 1891890944881347883061)
                  ·
                    rfl

theorem cell20_4145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 3].length) (baseStart_4145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4145 prefixEnd_4145 := by exact prefixLift 4145
  have htrace : WordTrace (prefixWord ++ tailWord_4145) baseStart_4145 baseEnd_4145 := by
    simpa [prefixWord, tailWord_4145, baseEnd_4145] using wordTrace_append hprefix tailTrace_4145
  have hstable : (prefixWord ++ tailWord_4145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145).length < 2 ^ (prefixWord ++ tailWord_4145).sum := by decide
  have hdescent : baseEnd_4145 < baseStart_4145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 6]
def baseStart_4156 : Nat := 118140960795 + 4156 * 2 ^ 59
def prefixEnd_4156 : Nat := 4983230072969 + 3 ^ 40 * 4156 * 2
def baseEnd_4156 : Nat := 1896911644614198516349

theorem tailTrace_4156 : CollatzResearch.WordTrace tailWord_4156 prefixEnd_4156 1896911644614198516349 := by
  unfold tailWord_4156
  simp only [CollatzResearch.WordTrace]
  refine ⟨75790886475498316700161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101054515300664422266881 75790886475498316700161)
  ·
    refine ⟨56843164856623737525121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75790886475498316700161 56843164856623737525121)
    ·
      refine ⟨42632373642467803143841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56843164856623737525121 42632373642467803143841)
      ·
        refine ⟨31974280231850852357881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42632373642467803143841 31974280231850852357881)
        ·
          refine ⟨23980710173888139268411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31974280231850852357881 23980710173888139268411)
          ·
            refine ⟨35971065260832208902617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23980710173888139268411 35971065260832208902617)
            ·
              refine ⟨26978298945624156676963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35971065260832208902617 26978298945624156676963)
              ·
                refine ⟨40467448418436235015445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26978298945624156676963 40467448418436235015445)
                ·
                  refine ⟨1896911644614198516349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40467448418436235015445 1896911644614198516349)
                  ·
                    rfl

theorem cell20_4156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_4156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4156 prefixEnd_4156 := by exact prefixLift 4156
  have htrace : WordTrace (prefixWord ++ tailWord_4156) baseStart_4156 baseEnd_4156 := by
    simpa [prefixWord, tailWord_4156, baseEnd_4156] using wordTrace_append hprefix tailTrace_4156
  have hstable : (prefixWord ++ tailWord_4156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156).length < 2 ^ (prefixWord ++ tailWord_4156).sum := by decide
  have hdescent : baseEnd_4156 < baseStart_4156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228 : List Nat := [2, 3, 2, 1, 2, 1, 4, 3, 2]
def baseStart_4228 : Nat := 118140960795 + 4228 * 2 ^ 59
def prefixEnd_4228 : Nat := 4983230072969 + 3 ^ 40 * 4228 * 2
def baseEnd_4228 : Nat := 1929774406501948116055

theorem tailTrace_4228 : CollatzResearch.WordTrace tailWord_4228 prefixEnd_4228 1929774406501948116055 := by
  unfold tailWord_4228
  simp only [CollatzResearch.WordTrace]
  refine ⟨77103914345076465010669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102805219126768620014225 77103914345076465010669)
  ·
    refine ⟨28913967879403674379001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77103914345076465010669 28913967879403674379001)
    ·
      refine ⟨21685475909552755784251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28913967879403674379001 21685475909552755784251)
      ·
        refine ⟨32528213864329133676377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21685475909552755784251 32528213864329133676377)
        ·
          refine ⟨24396160398246850257283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32528213864329133676377 24396160398246850257283)
          ·
            refine ⟨36594240597370275385925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24396160398246850257283 36594240597370275385925)
            ·
              refine ⟨6861420112006926634861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36594240597370275385925 6861420112006926634861)
              ·
                refine ⟨2573032542002597488073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6861420112006926634861 2573032542002597488073)
                ·
                  refine ⟨1929774406501948116055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2573032542002597488073 1929774406501948116055)
                  ·
                    rfl

theorem cell20_4228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_4228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4228 prefixEnd_4228 := by exact prefixLift 4228
  have htrace : WordTrace (prefixWord ++ tailWord_4228) baseStart_4228 baseEnd_4228 := by
    simpa [prefixWord, tailWord_4228, baseEnd_4228] using wordTrace_append hprefix tailTrace_4228
  have hstable : (prefixWord ++ tailWord_4228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228).length < 2 ^ (prefixWord ++ tailWord_4228).sum := by decide
  have hdescent : baseEnd_4228 < baseStart_4228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238 : List Nat := [4, 1, 1, 3, 4, 1, 1, 2, 3]
def baseStart_4238 : Nat := 118140960795 + 4238 * 2 ^ 59
def prefixEnd_4238 : Nat := 4983230072969 + 3 ^ 40 * 4238 * 2
def baseEnd_4238 : Nat := 1934338678986357782681

theorem tailTrace_4238 : CollatzResearch.WordTrace tailWord_4238 prefixEnd_4238 1934338678986357782681 := by
  unfold tailWord_4238
  simp only [CollatzResearch.WordTrace]
  refine ⟨19321569831740579735671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103048372435949758590245 19321569831740579735671)
  ·
    refine ⟨28982354747610869603507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19321569831740579735671 28982354747610869603507)
    ·
      refine ⟨43473532121416304405261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28982354747610869603507 43473532121416304405261)
      ·
        refine ⟨16302574545531114151973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43473532121416304405261 16302574545531114151973)
        ·
          refine ⟨3056732727287083903495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16302574545531114151973 3056732727287083903495)
          ·
            refine ⟨4585099090930625855243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3056732727287083903495 4585099090930625855243)
            ·
              refine ⟨6877648636395938782865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4585099090930625855243 6877648636395938782865)
              ·
                refine ⟨5158236477296954087149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6877648636395938782865 5158236477296954087149)
                ·
                  refine ⟨1934338678986357782681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5158236477296954087149 1934338678986357782681)
                  ·
                    rfl

theorem cell20_4238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_4238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4238 prefixEnd_4238 := by exact prefixLift 4238
  have htrace : WordTrace (prefixWord ++ tailWord_4238) baseStart_4238 baseEnd_4238 := by
    simpa [prefixWord, tailWord_4238, baseEnd_4238] using wordTrace_append hprefix tailTrace_4238
  have hstable : (prefixWord ++ tailWord_4238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238).length < 2 ^ (prefixWord ++ tailWord_4238).sum := by decide
  have hdescent : baseEnd_4238 < baseStart_4238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290 : List Nat := [3, 5, 1, 1, 1, 3, 6]
def baseStart_4290 : Nat := 118140960795 + 4290 * 2 ^ 59
def prefixEnd_4290 : Nat := 4983230072969 + 3 ^ 40 * 4290 * 2
def baseEnd_4290 : Nat := 217563655100587561015

theorem tailTrace_4290 : CollatzResearch.WordTrace tailWord_4290 prefixEnd_4290 217563655100587561015 := by
  unfold tailWord_4290
  simp only [CollatzResearch.WordTrace]
  refine ⟨39117288616384379694581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104312769643691679185549 39117288616384379694581)
  ·
    refine ⟨3667245807786035596367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39117288616384379694581 3667245807786035596367)
    ·
      refine ⟨5500868711679053394551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3667245807786035596367 5500868711679053394551)
      ·
        refine ⟨8251303067518580091827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5500868711679053394551 8251303067518580091827)
        ·
          refine ⟨12376954601277870137741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8251303067518580091827 12376954601277870137741)
          ·
            refine ⟨4641357975479201301653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12376954601277870137741 4641357975479201301653)
            ·
              refine ⟨217563655100587561015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4641357975479201301653 217563655100587561015)
              ·
                rfl

theorem cell20_4290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 6].length) (baseStart_4290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4290 prefixEnd_4290 := by exact prefixLift 4290
  have htrace : WordTrace (prefixWord ++ tailWord_4290) baseStart_4290 baseEnd_4290 := by
    simpa [prefixWord, tailWord_4290, baseEnd_4290] using wordTrace_append hprefix tailTrace_4290
  have hstable : (prefixWord ++ tailWord_4290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290).length < 2 ^ (prefixWord ++ tailWord_4290).sum := by decide
  have hdescent : baseEnd_4290 < baseStart_4290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300 : List Nat := [2, 2, 1, 6, 1, 1, 3, 2, 2]
def baseStart_4300 : Nat := 118140960795 + 4300 * 2 ^ 59
def prefixEnd_4300 : Nat := 4983230072969 + 3 ^ 40 * 4300 * 2
def baseEnd_4300 : Nat := 1962637168389697715761

theorem tailTrace_4300 : CollatzResearch.WordTrace tailWord_4300 prefixEnd_4300 1962637168389697715761 := by
  unfold tailWord_4300
  simp only [CollatzResearch.WordTrace]
  refine ⟨78416942214654613321177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104555922952872817761569 78416942214654613321177)
  ·
    refine ⟨58812706660990959990883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78416942214654613321177 58812706660990959990883)
    ·
      refine ⟨88219059991486439986325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58812706660990959990883 88219059991486439986325)
      ·
        refine ⟨4135268437100926874359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 88219059991486439986325 4135268437100926874359)
        ·
          refine ⟨6202902655651390311539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4135268437100926874359 6202902655651390311539)
          ·
            refine ⟨9304353983477085467309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6202902655651390311539 9304353983477085467309)
            ·
              refine ⟨3489132743803907050241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9304353983477085467309 3489132743803907050241)
              ·
                refine ⟨2616849557852930287681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3489132743803907050241 2616849557852930287681)
                ·
                  refine ⟨1962637168389697715761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2616849557852930287681 1962637168389697715761)
                  ·
                    rfl

theorem cell20_4300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 2].length) (baseStart_4300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4300 prefixEnd_4300 := by exact prefixLift 4300
  have htrace : WordTrace (prefixWord ++ tailWord_4300) baseStart_4300 baseEnd_4300 := by
    simpa [prefixWord, tailWord_4300, baseEnd_4300] using wordTrace_append hprefix tailTrace_4300
  have hstable : (prefixWord ++ tailWord_4300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300).length < 2 ^ (prefixWord ++ tailWord_4300).sum := by decide
  have hdescent : baseEnd_4300 < baseStart_4300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359 : List Nat := [1, 1, 4, 5, 1, 1, 1, 4, 2]
def baseStart_4359 : Nat := 118140960795 + 4359 * 2 ^ 59
def prefixEnd_4359 : Nat := 4983230072969 + 3 ^ 40 * 4359 * 2
def baseEnd_4359 : Nat := 1989566376047714748853

theorem tailTrace_4359 : CollatzResearch.WordTrace tailWord_4359 prefixEnd_4359 1989566376047714748853 := by
  unfold tailWord_4359
  simp only [CollatzResearch.WordTrace]
  refine ⟨158985791215562303040131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105990527477041535360087 158985791215562303040131)
  ·
    refine ⟨238478686823343454560197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158985791215562303040131 238478686823343454560197)
    ·
      refine ⟨44714753779376897730037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 238478686823343454560197 44714753779376897730037)
      ·
        refine ⟨4192008166816584162191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44714753779376897730037 4192008166816584162191)
        ·
          refine ⟨6288012250224876243287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4192008166816584162191 6288012250224876243287)
          ·
            refine ⟨9432018375337314364931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6288012250224876243287 9432018375337314364931)
            ·
              refine ⟨14148027563005971547397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9432018375337314364931 14148027563005971547397)
              ·
                refine ⟨2652755168063619665137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14148027563005971547397 2652755168063619665137)
                ·
                  refine ⟨1989566376047714748853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2652755168063619665137 1989566376047714748853)
                  ·
                    rfl

theorem cell20_4359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 2].length) (baseStart_4359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4359 prefixEnd_4359 := by exact prefixLift 4359
  have htrace : WordTrace (prefixWord ++ tailWord_4359) baseStart_4359 baseEnd_4359 := by
    simpa [prefixWord, tailWord_4359, baseEnd_4359] using wordTrace_append hprefix tailTrace_4359
  have hstable : (prefixWord ++ tailWord_4359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359).length < 2 ^ (prefixWord ++ tailWord_4359).sum := by decide
  have hdescent : baseEnd_4359 < baseStart_4359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363 : List Nat := [1, 1, 1, 1, 5, 2, 3, 4, 2]
def baseStart_4363 : Nat := 118140960795 + 4363 * 2 ^ 59
def prefixEnd_4363 : Nat := 4983230072969 + 3 ^ 40 * 4363 * 2
def baseEnd_4363 : Nat := 1991392085041478615503

theorem tailTrace_4363 : CollatzResearch.WordTrace tailWord_4363 prefixEnd_4363 1991392085041478615503 := by
  unfold tailWord_4363
  simp only [CollatzResearch.WordTrace]
  refine ⟨159131683201070986185743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106087788800713990790495 159131683201070986185743)
  ·
    refine ⟨238697524801606479278615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159131683201070986185743 238697524801606479278615)
    ·
      refine ⟨358046287202409718917923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238697524801606479278615 358046287202409718917923)
      ·
        refine ⟨537069430803614578376885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358046287202409718917923 537069430803614578376885)
        ·
          refine ⟨50350259137838866722833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 537069430803614578376885 50350259137838866722833)
          ·
            refine ⟨37762694353379150042125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50350259137838866722833 37762694353379150042125)
            ·
              refine ⟨14161010382517181265797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37762694353379150042125 14161010382517181265797)
              ·
                refine ⟨2655189446721971487337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14161010382517181265797 2655189446721971487337)
                ·
                  refine ⟨1991392085041478615503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2655189446721971487337 1991392085041478615503)
                  ·
                    rfl

theorem cell20_4363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 2].length) (baseStart_4363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4363 prefixEnd_4363 := by exact prefixLift 4363
  have htrace : WordTrace (prefixWord ++ tailWord_4363) baseStart_4363 baseEnd_4363 := by
    simpa [prefixWord, tailWord_4363, baseEnd_4363] using wordTrace_append hprefix tailTrace_4363
  have hstable : (prefixWord ++ tailWord_4363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363).length < 2 ^ (prefixWord ++ tailWord_4363).sum := by decide
  have hdescent : baseEnd_4363 < baseStart_4363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 8]
def baseStart_4367 : Nat := 118140960795 + 4367 * 2 ^ 59
def prefixEnd_4367 : Nat := 4983230072969 + 3 ^ 40 * 4367 * 2
def baseEnd_4367 : Nat := 1993217794035242482153

theorem tailTrace_4367 : CollatzResearch.WordTrace tailWord_4367 prefixEnd_4367 1993217794035242482153 := by
  unfold tailWord_4367
  simp only [CollatzResearch.WordTrace]
  refine ⟨159277575186579669331355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106185050124386446220903 159277575186579669331355)
  ·
    refine ⟨238916362779869503997033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159277575186579669331355 238916362779869503997033)
    ·
      refine ⟨179187272084902127997775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238916362779869503997033 179187272084902127997775)
      ·
        refine ⟨268780908127353191996663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179187272084902127997775 268780908127353191996663)
        ·
          refine ⟨403171362191029787994995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268780908127353191996663 403171362191029787994995)
          ·
            refine ⟨604757043286544681992493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403171362191029787994995 604757043286544681992493)
            ·
              refine ⟨226783891232454255747185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 604757043286544681992493 226783891232454255747185)
              ·
                refine ⟨170087918424340691810389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226783891232454255747185 170087918424340691810389)
                ·
                  refine ⟨1993217794035242482153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 170087918424340691810389 1993217794035242482153)
                  ·
                    rfl

theorem cell20_4367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_4367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4367 prefixEnd_4367 := by exact prefixLift 4367
  have htrace : WordTrace (prefixWord ++ tailWord_4367) baseStart_4367 baseEnd_4367 := by
    simpa [prefixWord, tailWord_4367, baseEnd_4367] using wordTrace_append hprefix tailTrace_4367
  have hstable : (prefixWord ++ tailWord_4367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367).length < 2 ^ (prefixWord ++ tailWord_4367).sum := by decide
  have hdescent : baseEnd_4367 < baseStart_4367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 6]
def baseStart_4384 : Nat := 118140960795 + 4384 * 2 ^ 59
def prefixEnd_4384 : Nat := 4983230072969 + 3 ^ 40 * 4384 * 2
def baseEnd_4384 : Nat := 2000977057258738915417

theorem tailTrace_4384 : CollatzResearch.WordTrace tailWord_4384 prefixEnd_4384 2000977057258738915417 := by
  unfold tailWord_4384
  simp only [CollatzResearch.WordTrace]
  refine ⟨79948808062495786350103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106598410749994381800137 79948808062495786350103)
  ·
    refine ⟨119923212093743679525155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79948808062495786350103 119923212093743679525155)
    ·
      refine ⟨179884818140615519287733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119923212093743679525155 179884818140615519287733)
      ·
        refine ⟨16864201700682704933225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 179884818140615519287733 16864201700682704933225)
        ·
          refine ⟨12648151275512028699919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16864201700682704933225 12648151275512028699919)
          ·
            refine ⟨18972226913268043049879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12648151275512028699919 18972226913268043049879)
            ·
              refine ⟨28458340369902064574819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18972226913268043049879 28458340369902064574819)
              ·
                refine ⟨42687510554853096862229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28458340369902064574819 42687510554853096862229)
                ·
                  refine ⟨2000977057258738915417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42687510554853096862229 2000977057258738915417)
                  ·
                    rfl

theorem cell20_4384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_4384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4384 prefixEnd_4384 := by exact prefixLift 4384
  have htrace : WordTrace (prefixWord ++ tailWord_4384) baseStart_4384 baseEnd_4384 := by
    simpa [prefixWord, tailWord_4384, baseEnd_4384] using wordTrace_append hprefix tailTrace_4384
  have hstable : (prefixWord ++ tailWord_4384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384).length < 2 ^ (prefixWord ++ tailWord_4384).sum := by decide
  have hdescent : baseEnd_4384 < baseStart_4384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432 : List Nat := [2, 1, 1, 1, 1, 7, 3, 1, 3]
def baseStart_4432 : Nat := 118140960795 + 4432 * 2 ^ 59
def prefixEnd_4432 : Nat := 4983230072969 + 3 ^ 40 * 4432 * 2
def baseEnd_4432 : Nat := 2022885565183905315221

theorem tailTrace_4432 : CollatzResearch.WordTrace tailWord_4432 prefixEnd_4432 2022885565183905315221 := by
  unfold tailWord_4432
  simp only [CollatzResearch.WordTrace]
  refine ⟨80824159975547885223775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107765546634063846965033 80824159975547885223775)
  ·
    refine ⟨121236239963321827835663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80824159975547885223775 121236239963321827835663)
    ·
      refine ⟨181854359944982741753495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121236239963321827835663 181854359944982741753495)
      ·
        refine ⟨272781539917474112630243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181854359944982741753495 272781539917474112630243)
        ·
          refine ⟨409172309876211168945365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272781539917474112630243 409172309876211168945365)
          ·
            refine ⟨9589976012723699272157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 409172309876211168945365 9589976012723699272157)
            ·
              refine ⟨3596241004771387227059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9589976012723699272157 3596241004771387227059)
              ·
                refine ⟨5394361507157080840589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3596241004771387227059 5394361507157080840589)
                ·
                  refine ⟨2022885565183905315221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5394361507157080840589 2022885565183905315221)
                  ·
                    rfl

theorem cell20_4432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 3].length) (baseStart_4432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4432 prefixEnd_4432 := by exact prefixLift 4432
  have htrace : WordTrace (prefixWord ++ tailWord_4432) baseStart_4432 baseEnd_4432 := by
    simpa [prefixWord, tailWord_4432, baseEnd_4432] using wordTrace_append hprefix tailTrace_4432
  have hstable : (prefixWord ++ tailWord_4432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432).length < 2 ^ (prefixWord ++ tailWord_4432).sum := by decide
  have hdescent : baseEnd_4432 < baseStart_4432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4456 : List Nat := [2, 1, 4, 2, 2, 1, 3, 3, 2]
def baseStart_4456 : Nat := 118140960795 + 4456 * 2 ^ 59
def prefixEnd_4456 : Nat := 4983230072969 + 3 ^ 40 * 4456 * 2
def baseEnd_4456 : Nat := 2033839819146488515123

theorem tailTrace_4456 : CollatzResearch.WordTrace tailWord_4456 prefixEnd_4456 2033839819146488515123 := by
  unfold tailWord_4456
  simp only [CollatzResearch.WordTrace]
  refine ⟨81261835932073934660611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108349114576098579547481 81261835932073934660611)
  ·
    refine ⟨121892753898110901990917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81261835932073934660611 121892753898110901990917)
    ·
      refine ⟨22854891355895794123297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121892753898110901990917 22854891355895794123297)
      ·
        refine ⟨17141168516921845592473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22854891355895794123297 17141168516921845592473)
        ·
          refine ⟨12855876387691384194355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17141168516921845592473 12855876387691384194355)
          ·
            refine ⟨19283814581537076291533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12855876387691384194355 19283814581537076291533)
            ·
              refine ⟨7231430468076403609325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19283814581537076291533 7231430468076403609325)
              ·
                refine ⟨2711786425528651353497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7231430468076403609325 2711786425528651353497)
                ·
                  refine ⟨2033839819146488515123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2711786425528651353497 2033839819146488515123)
                  ·
                    rfl

theorem cell20_4456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 2].length) (baseStart_4456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4456 prefixEnd_4456 := by exact prefixLift 4456
  have htrace : WordTrace (prefixWord ++ tailWord_4456) baseStart_4456 baseEnd_4456 := by
    simpa [prefixWord, tailWord_4456, baseEnd_4456] using wordTrace_append hprefix tailTrace_4456
  have hstable : (prefixWord ++ tailWord_4456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4456).length < 2 ^ (prefixWord ++ tailWord_4456).sum := by decide
  have hdescent : baseEnd_4456 < baseStart_4456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477 : List Nat := [1, 4, 1, 1, 2, 5, 1, 1, 4]
def baseStart_4477 : Nat := 118140960795 + 4477 * 2 ^ 59
def prefixEnd_4477 : Nat := 4983230072969 + 3 ^ 40 * 4477 * 2
def baseEnd_4477 : Nat := 2043424791363748815037

theorem tailTrace_4477 : CollatzResearch.WordTrace tailWord_4477 prefixEnd_4477 2043424791363748815037 := by
  unfold tailWord_4477
  simp only [CollatzResearch.WordTrace]
  refine ⟨163289604788068455835685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108859736525378970557123 163289604788068455835685)
  ·
    refine ⟨30616800897762835469191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163289604788068455835685 30616800897762835469191)
    ·
      refine ⟨45925201346644253203787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30616800897762835469191 45925201346644253203787)
      ·
        refine ⟨68887802019966379805681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45925201346644253203787 68887802019966379805681)
        ·
          refine ⟨51665851514974784854261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68887802019966379805681 51665851514974784854261)
          ·
            refine ⟨4843673579528886080087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51665851514974784854261 4843673579528886080087)
            ·
              refine ⟨7265510369293329120131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4843673579528886080087 7265510369293329120131)
              ·
                refine ⟨10898265553939993680197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7265510369293329120131 10898265553939993680197)
                ·
                  refine ⟨2043424791363748815037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10898265553939993680197 2043424791363748815037)
                  ·
                    rfl

theorem cell20_4477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_4477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4477 prefixEnd_4477 := by exact prefixLift 4477
  have htrace : WordTrace (prefixWord ++ tailWord_4477) baseStart_4477 baseEnd_4477 := by
    simpa [prefixWord, tailWord_4477, baseEnd_4477] using wordTrace_append hprefix tailTrace_4477
  have hstable : (prefixWord ++ tailWord_4477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477).length < 2 ^ (prefixWord ++ tailWord_4477).sum := by decide
  have hdescent : baseEnd_4477 < baseStart_4477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491 : List Nat := [1, 1, 1, 1, 4, 5, 1, 3, 3]
def baseStart_4491 : Nat := 118140960795 + 4491 * 2 ^ 59
def prefixEnd_4491 : Nat := 4983230072969 + 3 ^ 40 * 4491 * 2
def baseEnd_4491 : Nat := 2049814772841922348313

theorem tailTrace_4491 : CollatzResearch.WordTrace tailWord_4491 prefixEnd_4491 2049814772841922348313 := by
  unfold tailWord_4491
  simp only [CollatzResearch.WordTrace]
  refine ⟨163800226737348846845327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109200151158232564563551 163800226737348846845327)
  ·
    refine ⟨245700340106023270267991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163800226737348846845327 245700340106023270267991)
    ·
      refine ⟨368550510159034905401987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245700340106023270267991 368550510159034905401987)
      ·
        refine ⟨552825765238552358102981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368550510159034905401987 552825765238552358102981)
        ·
          refine ⟨103654830982228567144309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 552825765238552358102981 103654830982228567144309)
          ·
            refine ⟨9717640404583928169779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103654830982228567144309 9717640404583928169779)
            ·
              refine ⟨14576460606875892254669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9717640404583928169779 14576460606875892254669)
              ·
                refine ⟨5466172727578459595501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14576460606875892254669 5466172727578459595501)
                ·
                  refine ⟨2049814772841922348313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5466172727578459595501 2049814772841922348313)
                  ·
                    rfl

theorem cell20_4491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 3].length) (baseStart_4491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4491 prefixEnd_4491 := by exact prefixLift 4491
  have htrace : WordTrace (prefixWord ++ tailWord_4491) baseStart_4491 baseEnd_4491 := by
    simpa [prefixWord, tailWord_4491, baseEnd_4491] using wordTrace_append hprefix tailTrace_4491
  have hstable : (prefixWord ++ tailWord_4491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491).length < 2 ^ (prefixWord ++ tailWord_4491).sum := by decide
  have hdescent : baseEnd_4491 < baseStart_4491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525 : List Nat := [1, 5, 2, 2, 2, 1, 2, 2, 3]
def baseStart_4525 : Nat := 118140960795 + 4525 * 2 ^ 59
def prefixEnd_4525 : Nat := 4983230072969 + 3 ^ 40 * 4525 * 2
def baseEnd_4525 : Nat := 2065333299288915214841

theorem tailTrace_4525 : CollatzResearch.WordTrace tailWord_4525 prefixEnd_4525 2065333299288915214841 := by
  unfold tailWord_4525
  simp only [CollatzResearch.WordTrace]
  refine ⟨165040308614172653583029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110026872409448435722019 165040308614172653583029)
  ·
    refine ⟨15472528932578686273409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 165040308614172653583029 15472528932578686273409)
    ·
      refine ⟨11604396699434014705057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15472528932578686273409 11604396699434014705057)
      ·
        refine ⟨8703297524575511028793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11604396699434014705057 8703297524575511028793)
        ·
          refine ⟨6527473143431633271595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8703297524575511028793 6527473143431633271595)
          ·
            refine ⟨9791209715147449907393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6527473143431633271595 9791209715147449907393)
            ·
              refine ⟨7343407286360587430545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9791209715147449907393 7343407286360587430545)
              ·
                refine ⟨5507555464770440572909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7343407286360587430545 5507555464770440572909)
                ·
                  refine ⟨2065333299288915214841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5507555464770440572909 2065333299288915214841)
                  ·
                    rfl

theorem cell20_4525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_4525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4525 prefixEnd_4525 := by exact prefixLift 4525
  have htrace : WordTrace (prefixWord ++ tailWord_4525) baseStart_4525 baseEnd_4525 := by
    simpa [prefixWord, tailWord_4525, baseEnd_4525] using wordTrace_append hprefix tailTrace_4525
  have hstable : (prefixWord ++ tailWord_4525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525).length < 2 ^ (prefixWord ++ tailWord_4525).sum := by decide
  have hdescent : baseEnd_4525 < baseStart_4525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529 : List Nat := [1, 2, 2, 4, 1, 2, 1, 4, 3]
def baseStart_4529 : Nat := 118140960795 + 4529 * 2 ^ 59
def prefixEnd_4529 : Nat := 4983230072969 + 3 ^ 40 * 4529 * 2
def baseEnd_4529 : Nat := 2067159008282679081491

theorem tailTrace_4529 : CollatzResearch.WordTrace tailWord_4529 prefixEnd_4529 2067159008282679081491 := by
  unfold tailWord_4529
  simp only [CollatzResearch.WordTrace]
  refine ⟨165186200599681336728641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110124133733120891152427 165186200599681336728641)
  ·
    refine ⟨123889650449761002546481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165186200599681336728641 123889650449761002546481)
    ·
      refine ⟨92917237837320751909861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123889650449761002546481 92917237837320751909861)
      ·
        refine ⟨17421982094497640983099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92917237837320751909861 17421982094497640983099)
        ·
          refine ⟨26132973141746461474649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17421982094497640983099 26132973141746461474649)
          ·
            refine ⟨19599729856309846105987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26132973141746461474649 19599729856309846105987)
            ·
              refine ⟨29399594784464769158981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19599729856309846105987 29399594784464769158981)
              ·
                refine ⟨5512424022087144217309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29399594784464769158981 5512424022087144217309)
                ·
                  refine ⟨2067159008282679081491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5512424022087144217309 2067159008282679081491)
                  ·
                    rfl

theorem cell20_4529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 3].length) (baseStart_4529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4529 prefixEnd_4529 := by exact prefixLift 4529
  have htrace : WordTrace (prefixWord ++ tailWord_4529) baseStart_4529 baseEnd_4529 := by
    simpa [prefixWord, tailWord_4529, baseEnd_4529] using wordTrace_append hprefix tailTrace_4529
  have hstable : (prefixWord ++ tailWord_4529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529).length < 2 ^ (prefixWord ++ tailWord_4529).sum := by decide
  have hdescent : baseEnd_4529 < baseStart_4529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584 : List Nat := [2, 1, 4, 1, 1, 5, 1, 2, 3]
def baseStart_4584 : Nat := 118140960795 + 4584 * 2 ^ 59
def prefixEnd_4584 : Nat := 4983230072969 + 3 ^ 40 * 4584 * 2
def baseEnd_4584 : Nat := 2092262506946932247933

theorem tailTrace_4584 : CollatzResearch.WordTrace tailWord_4584 prefixEnd_4584 2092262506946932247933 := by
  unfold tailWord_4584
  simp only [CollatzResearch.WordTrace]
  refine ⟨83596107700212864990403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111461476933617153320537 83596107700212864990403)
  ·
    refine ⟨125394161550319297485605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83596107700212864990403 125394161550319297485605)
    ·
      refine ⟨23511405290684868278551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125394161550319297485605 23511405290684868278551)
      ·
        refine ⟨35267107936027302417827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23511405290684868278551 35267107936027302417827)
        ·
          refine ⟨52900661904040953626741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35267107936027302417827 52900661904040953626741)
          ·
            refine ⟨4959437053503839402507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52900661904040953626741 4959437053503839402507)
            ·
              refine ⟨7439155580255759103761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4959437053503839402507 7439155580255759103761)
              ·
                refine ⟨5579366685191819327821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7439155580255759103761 5579366685191819327821)
                ·
                  refine ⟨2092262506946932247933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5579366685191819327821 2092262506946932247933)
                  ·
                    rfl

theorem cell20_4584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 3].length) (baseStart_4584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4584 prefixEnd_4584 := by exact prefixLift 4584
  have htrace : WordTrace (prefixWord ++ tailWord_4584) baseStart_4584 baseEnd_4584 := by
    simpa [prefixWord, tailWord_4584, baseEnd_4584] using wordTrace_append hprefix tailTrace_4584
  have hstable : (prefixWord ++ tailWord_4584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584).length < 2 ^ (prefixWord ++ tailWord_4584).sum := by decide
  have hdescent : baseEnd_4584 < baseStart_4584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 5]
def baseStart_4588 : Nat := 118140960795 + 4588 * 2 ^ 59
def prefixEnd_4588 : Nat := 4983230072969 + 3 ^ 40 * 4588 * 2
def baseEnd_4588 : Nat := 2094088215940696114583

theorem tailTrace_4588 : CollatzResearch.WordTrace tailWord_4588 prefixEnd_4588 2094088215940696114583 := by
  unfold tailWord_4588
  simp only [CollatzResearch.WordTrace]
  refine ⟨83669053692967206563209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111558738257289608750945 83669053692967206563209)
  ·
    refine ⟨62751790269725404922407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83669053692967206563209 62751790269725404922407)
    ·
      refine ⟨94127685404588107383611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62751790269725404922407 94127685404588107383611)
      ·
        refine ⟨141191528106882161075417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94127685404588107383611 141191528106882161075417)
        ·
          refine ⟨105893646080161620806563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141191528106882161075417 105893646080161620806563)
          ·
            refine ⟨158840469120242431209845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105893646080161620806563 158840469120242431209845)
            ·
              refine ⟨14891293980022727925923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 158840469120242431209845 14891293980022727925923)
              ·
                refine ⟨22336940970034091888885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14891293980022727925923 22336940970034091888885)
                ·
                  refine ⟨2094088215940696114583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22336940970034091888885 2094088215940696114583)
                  ·
                    rfl

theorem cell20_4588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_4588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4588 prefixEnd_4588 := by exact prefixLift 4588
  have htrace : WordTrace (prefixWord ++ tailWord_4588) baseStart_4588 baseEnd_4588 := by
    simpa [prefixWord, tailWord_4588, baseEnd_4588] using wordTrace_append hprefix tailTrace_4588
  have hstable : (prefixWord ++ tailWord_4588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588).length < 2 ^ (prefixWord ++ tailWord_4588).sum := by decide
  have hdescent : baseEnd_4588 < baseStart_4588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4615 : List Nat := [1, 1, 4, 3, 3, 2, 2, 4]
def baseStart_4615 : Nat := 118140960795 + 4615 * 2 ^ 59
def prefixEnd_4615 : Nat := 4983230072969 + 3 ^ 40 * 4615 * 2
def baseEnd_4615 : Nat := 702137250549534071491

theorem tailTrace_4615 : CollatzResearch.WordTrace tailWord_4615 prefixEnd_4615 702137250549534071491 := by
  unfold tailWord_4615
  simp only [CollatzResearch.WordTrace]
  refine ⟨168322878288118024359299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112215252192078682906199 168322878288118024359299)
  ·
    refine ⟨252484317432177036538949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168322878288118024359299 252484317432177036538949)
    ·
      refine ⟨47340809518533194351053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 252484317432177036538949 47340809518533194351053)
      ·
        refine ⟨17752803569449947881645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47340809518533194351053 17752803569449947881645)
        ·
          refine ⟨6657301338543730455617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17752803569449947881645 6657301338543730455617)
          ·
            refine ⟨4992976003907797841713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6657301338543730455617 4992976003907797841713)
            ·
              refine ⟨3744732002930848381285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4992976003907797841713 3744732002930848381285)
              ·
                refine ⟨702137250549534071491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3744732002930848381285 702137250549534071491)
                ·
                  rfl

theorem cell20_4615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 4].length) (baseStart_4615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4615 prefixEnd_4615 := by exact prefixLift 4615
  have htrace : WordTrace (prefixWord ++ tailWord_4615) baseStart_4615 baseEnd_4615 := by
    simpa [prefixWord, tailWord_4615, baseEnd_4615] using wordTrace_append hprefix tailTrace_4615
  have hstable : (prefixWord ++ tailWord_4615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4615).length < 2 ^ (prefixWord ++ tailWord_4615).sum := by decide
  have hdescent : baseEnd_4615 < baseStart_4615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4619 : List Nat := [1, 1, 1, 1, 7, 2, 1, 6]
def baseStart_4619 : Nat := 118140960795 + 4619 * 2 ^ 59
def prefixEnd_4619 : Nat := 4983230072969 + 3 ^ 40 * 4619 * 2
def baseEnd_4619 : Nat := 702745820214122027041

theorem tailTrace_4619 : CollatzResearch.WordTrace tailWord_4619 prefixEnd_4619 702745820214122027041 := by
  unfold tailWord_4619
  simp only [CollatzResearch.WordTrace]
  refine ⟨168468770273626707504911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112312513515751138336607 168468770273626707504911)
  ·
    refine ⟨252703155410440061257367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168468770273626707504911 252703155410440061257367)
    ·
      refine ⟨379054733115660091886051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252703155410440061257367 379054733115660091886051)
      ·
        refine ⟨568582099673490137829077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379054733115660091886051 568582099673490137829077)
        ·
          refine ⟨13326142961097425105369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 568582099673490137829077 13326142961097425105369)
          ·
            refine ⟨9994607220823068829027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13326142961097425105369 9994607220823068829027)
            ·
              refine ⟨14991910831234603243541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9994607220823068829027 14991910831234603243541)
              ·
                refine ⟨702745820214122027041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14991910831234603243541 702745820214122027041)
                ·
                  rfl

theorem cell20_4619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 6].length) (baseStart_4619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4619 prefixEnd_4619 := by exact prefixLift 4619
  have htrace : WordTrace (prefixWord ++ tailWord_4619) baseStart_4619 baseEnd_4619 := by
    simpa [prefixWord, tailWord_4619, baseEnd_4619] using wordTrace_append hprefix tailTrace_4619
  have hstable : (prefixWord ++ tailWord_4619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4619).length < 2 ^ (prefixWord ++ tailWord_4619).sum := by decide
  have hdescent : baseEnd_4619 < baseStart_4619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 6]
def baseStart_4671 : Nat := 118140960795 + 4671 * 2 ^ 59
def prefixEnd_4671 : Nat := 4983230072969 + 3 ^ 40 * 4671 * 2
def baseEnd_4671 : Nat := 2131971677561296347577

theorem tailTrace_4671 : CollatzResearch.WordTrace tailWord_4671 prefixEnd_4671 2131971677561296347577 := by
  unfold tailWord_4671
  simp only [CollatzResearch.WordTrace]
  refine ⟨170365366085239588397867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113576910723493058931911 170365366085239588397867)
  ·
    refine ⟨255548049127859382596801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170365366085239588397867 255548049127859382596801)
    ·
      refine ⟨191661036845894536947601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255548049127859382596801 191661036845894536947601)
      ·
        refine ⟨143745777634420902710701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191661036845894536947601 143745777634420902710701)
        ·
          refine ⟨53904666612907838516513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143745777634420902710701 53904666612907838516513)
          ·
            refine ⟨40428499959680878887385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53904666612907838516513 40428499959680878887385)
            ·
              refine ⟨30321374969760659165539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40428499959680878887385 30321374969760659165539)
              ·
                refine ⟨45482062454640988748309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30321374969760659165539 45482062454640988748309)
                ·
                  refine ⟨2131971677561296347577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45482062454640988748309 2131971677561296347577)
                  ·
                    rfl

theorem cell20_4671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_4671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4671 prefixEnd_4671 := by exact prefixLift 4671
  have htrace : WordTrace (prefixWord ++ tailWord_4671) baseStart_4671 baseEnd_4671 := by
    simpa [prefixWord, tailWord_4671, baseEnd_4671] using wordTrace_append hprefix tailTrace_4671
  have hstable : (prefixWord ++ tailWord_4671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671).length < 2 ^ (prefixWord ++ tailWord_4671).sum := by decide
  have hdescent : baseEnd_4671 < baseStart_4671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4705 : List Nat := [1, 2, 3, 1, 1, 5, 1, 4, 2]
def baseStart_4705 : Nat := 118140960795 + 4705 * 2 ^ 59
def prefixEnd_4705 : Nat := 4983230072969 + 3 ^ 40 * 4705 * 2
def baseEnd_4705 : Nat := 2147490204008289214105

theorem tailTrace_4705 : CollatzResearch.WordTrace tailWord_4705 prefixEnd_4705 2147490204008289214105 := by
  unfold tailWord_4705
  simp only [CollatzResearch.WordTrace]
  refine ⟨171605447962063395135569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114403631974708930090379 171605447962063395135569)
  ·
    refine ⟨128704085971547546351677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171605447962063395135569 128704085971547546351677)
    ·
      refine ⟨48264032239330329881879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128704085971547546351677 48264032239330329881879)
      ·
        refine ⟨72396048358995494822819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48264032239330329881879 72396048358995494822819)
        ·
          refine ⟨108594072538493242234229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72396048358995494822819 108594072538493242234229)
          ·
            refine ⟨10180694300483741459459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 108594072538493242234229 10180694300483741459459)
            ·
              refine ⟨15271041450725612189189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10180694300483741459459 15271041450725612189189)
              ·
                refine ⟨2863320272011052285473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15271041450725612189189 2863320272011052285473)
                ·
                  refine ⟨2147490204008289214105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2863320272011052285473 2147490204008289214105)
                  ·
                    rfl

theorem cell20_4705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 2].length) (baseStart_4705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4705 prefixEnd_4705 := by exact prefixLift 4705
  have htrace : WordTrace (prefixWord ++ tailWord_4705) baseStart_4705 baseEnd_4705 := by
    simpa [prefixWord, tailWord_4705, baseEnd_4705] using wordTrace_append hprefix tailTrace_4705
  have hstable : (prefixWord ++ tailWord_4705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4705).length < 2 ^ (prefixWord ++ tailWord_4705).sum := by decide
  have hdescent : baseEnd_4705 < baseStart_4705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743 : List Nat := [1, 1, 4, 2, 1, 2, 4, 3, 2]
def baseStart_4743 : Nat := 118140960795 + 4743 * 2 ^ 59
def prefixEnd_4743 : Nat := 4983230072969 + 3 ^ 40 * 4743 * 2
def baseEnd_4743 : Nat := 2164834439449045947283

theorem tailTrace_4743 : CollatzResearch.WordTrace tailWord_4743 prefixEnd_4743 2164834439449045947283 := by
  unfold tailWord_4743
  simp only [CollatzResearch.WordTrace]
  refine ⟨172991421824395885018883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115327614549597256679255 172991421824395885018883)
  ·
    refine ⟨259487132736593827528325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172991421824395885018883 259487132736593827528325)
    ·
      refine ⟨48653837388111342661561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 259487132736593827528325 48653837388111342661561)
      ·
        refine ⟨36490378041083506996171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48653837388111342661561 36490378041083506996171)
        ·
          refine ⟨54735567061625260494257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36490378041083506996171 54735567061625260494257)
          ·
            refine ⟨41051675296218945370693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54735567061625260494257 41051675296218945370693)
            ·
              refine ⟨7697189118041052257005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41051675296218945370693 7697189118041052257005)
              ·
                refine ⟨2886445919265394596377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7697189118041052257005 2886445919265394596377)
                ·
                  refine ⟨2164834439449045947283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2886445919265394596377 2164834439449045947283)
                  ·
                    rfl

theorem cell20_4743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 2].length) (baseStart_4743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4743 prefixEnd_4743 := by exact prefixLift 4743
  have htrace : WordTrace (prefixWord ++ tailWord_4743) baseStart_4743 baseEnd_4743 := by
    simpa [prefixWord, tailWord_4743, baseEnd_4743] using wordTrace_append hprefix tailTrace_4743
  have hstable : (prefixWord ++ tailWord_4743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743).length < 2 ^ (prefixWord ++ tailWord_4743).sum := by decide
  have hdescent : baseEnd_4743 < baseStart_4743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4764 : List Nat := [2, 2, 3, 2, 2, 1, 1, 3, 4]
def baseStart_4764 : Nat := 118140960795 + 4764 * 2 ^ 59
def prefixEnd_4764 : Nat := 4983230072969 + 3 ^ 40 * 4764 * 2
def baseEnd_4764 : Nat := 2174419411666306247197

theorem tailTrace_4764 : CollatzResearch.WordTrace tailWord_4764 prefixEnd_4764 2174419411666306247197 := by
  unfold tailWord_4764
  simp only [CollatzResearch.WordTrace]
  refine ⟨86878677374158235766673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115838236498877647688897 86878677374158235766673)
  ·
    refine ⟨65159008030618676825005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86878677374158235766673 65159008030618676825005)
    ·
      refine ⟨24434628011482003809377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65159008030618676825005 24434628011482003809377)
      ·
        refine ⟨18325971008611502857033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24434628011482003809377 18325971008611502857033)
        ·
          refine ⟨13744478256458627142775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18325971008611502857033 13744478256458627142775)
          ·
            refine ⟨20616717384687940714163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13744478256458627142775 20616717384687940714163)
            ·
              refine ⟨30925076077031911071245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20616717384687940714163 30925076077031911071245)
              ·
                refine ⟨11596903528886966651717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30925076077031911071245 11596903528886966651717)
                ·
                  refine ⟨2174419411666306247197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11596903528886966651717 2174419411666306247197)
                  ·
                    rfl

theorem cell20_4764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_4764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4764 prefixEnd_4764 := by exact prefixLift 4764
  have htrace : WordTrace (prefixWord ++ tailWord_4764) baseStart_4764 baseEnd_4764 := by
    simpa [prefixWord, tailWord_4764, baseEnd_4764] using wordTrace_append hprefix tailTrace_4764
  have hstable : (prefixWord ++ tailWord_4764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4764).length < 2 ^ (prefixWord ++ tailWord_4764).sum := by decide
  have hdescent : baseEnd_4764 < baseStart_4764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833 : List Nat := [1, 2, 3, 1, 4, 2, 1, 3, 3]
def baseStart_4833 : Nat := 118140960795 + 4833 * 2 ^ 59
def prefixEnd_4833 : Nat := 4983230072969 + 3 ^ 40 * 4833 * 2
def baseEnd_4833 : Nat := 2205912891808732946915

theorem tailTrace_4833 : CollatzResearch.WordTrace tailWord_4833 prefixEnd_4833 2205912891808732946915 := by
  unfold tailWord_4833
  simp only [CollatzResearch.WordTrace]
  refine ⟨176273991498341255795153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117515994332227503863435 176273991498341255795153)
  ·
    refine ⟨132205493623755941846365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176273991498341255795153 132205493623755941846365)
    ·
      refine ⟨49577060108908478192387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132205493623755941846365 49577060108908478192387)
      ·
        refine ⟨74365590163362717288581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49577060108908478192387 74365590163362717288581)
        ·
          refine ⟨13943548155630509491609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74365590163362717288581 13943548155630509491609)
          ·
            refine ⟨10457661116722882118707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13943548155630509491609 10457661116722882118707)
            ·
              refine ⟨15686491675084323178061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10457661116722882118707 15686491675084323178061)
              ·
                refine ⟨5882434378156621191773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15686491675084323178061 5882434378156621191773)
                ·
                  refine ⟨2205912891808732946915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5882434378156621191773 2205912891808732946915)
                  ·
                    rfl

theorem cell20_4833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 3].length) (baseStart_4833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4833 prefixEnd_4833 := by exact prefixLift 4833
  have htrace : WordTrace (prefixWord ++ tailWord_4833) baseStart_4833 baseEnd_4833 := by
    simpa [prefixWord, tailWord_4833, baseEnd_4833] using wordTrace_append hprefix tailTrace_4833
  have hstable : (prefixWord ++ tailWord_4833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833).length < 2 ^ (prefixWord ++ tailWord_4833).sum := by decide
  have hdescent : baseEnd_4833 < baseStart_4833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871 : List Nat := [1, 1, 4, 4, 1, 1, 1, 4, 3]
def baseStart_4871 : Nat := 118140960795 + 4871 * 2 ^ 59
def prefixEnd_4871 : Nat := 4983230072969 + 3 ^ 40 * 4871 * 2
def baseEnd_4871 : Nat := 2223257127249489680093

theorem tailTrace_4871 : CollatzResearch.WordTrace tailWord_4871 prefixEnd_4871 2223257127249489680093 := by
  unfold tailWord_4871
  simp only [CollatzResearch.WordTrace]
  refine ⟨177659965360673745678467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118439976907115830452311 177659965360673745678467)
  ·
    refine ⟨266489948041010618517701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177659965360673745678467 266489948041010618517701)
    ·
      refine ⟨49966865257689490972069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 266489948041010618517701 49966865257689490972069)
      ·
        refine ⟨9368787235816779557263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49966865257689490972069 9368787235816779557263)
        ·
          refine ⟨14053180853725169335895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9368787235816779557263 14053180853725169335895)
          ·
            refine ⟨21079771280587754003843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14053180853725169335895 21079771280587754003843)
            ·
              refine ⟨31619656920881631005765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21079771280587754003843 31619656920881631005765)
              ·
                refine ⟨5928685672665305813581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31619656920881631005765 5928685672665305813581)
                ·
                  refine ⟨2223257127249489680093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5928685672665305813581 2223257127249489680093)
                  ·
                    rfl

theorem cell20_4871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 3].length) (baseStart_4871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4871 prefixEnd_4871 := by exact prefixLift 4871
  have htrace : WordTrace (prefixWord ++ tailWord_4871) baseStart_4871 baseEnd_4871 := by
    simpa [prefixWord, tailWord_4871, baseEnd_4871] using wordTrace_append hprefix tailTrace_4871
  have hstable : (prefixWord ++ tailWord_4871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871).length < 2 ^ (prefixWord ++ tailWord_4871).sum := by decide
  have hdescent : baseEnd_4871 < baseStart_4871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937 : List Nat := [1, 2, 1, 1, 2, 5, 1, 3, 4]
def baseStart_4937 : Nat := 118140960795 + 4937 * 2 ^ 59
def prefixEnd_4937 : Nat := 4983230072969 + 3 ^ 40 * 4937 * 2
def baseEnd_4937 : Nat := 2253381325646593479823

theorem tailTrace_4937 : CollatzResearch.WordTrace tailWord_4937 prefixEnd_4937 2253381325646593479823 := by
  unfold tailWord_4937
  simp only [CollatzResearch.WordTrace]
  refine ⟨180067183121567017581065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120044788747711345054043 180067183121567017581065)
  ·
    refine ⟨135050387341175263185799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180067183121567017581065 135050387341175263185799)
    ·
      refine ⟨202575581011762894778699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135050387341175263185799 202575581011762894778699)
      ·
        refine ⟨303863371517644342168049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202575581011762894778699 303863371517644342168049)
        ·
          refine ⟨227897528638233256626037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303863371517644342168049 227897528638233256626037)
          ·
            refine ⟨21365393309834367808691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 227897528638233256626037 21365393309834367808691)
            ·
              refine ⟨32048089964751551713037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21365393309834367808691 32048089964751551713037)
              ·
                refine ⟨12018033736781831892389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32048089964751551713037 12018033736781831892389)
                ·
                  refine ⟨2253381325646593479823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12018033736781831892389 2253381325646593479823)
                  ·
                    rfl

theorem cell20_4937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_4937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4937 prefixEnd_4937 := by exact prefixLift 4937
  have htrace : WordTrace (prefixWord ++ tailWord_4937) baseStart_4937 baseEnd_4937 := by
    simpa [prefixWord, tailWord_4937, baseEnd_4937] using wordTrace_append hprefix tailTrace_4937
  have hstable : (prefixWord ++ tailWord_4937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937).length < 2 ^ (prefixWord ++ tailWord_4937).sum := by decide
  have hdescent : baseEnd_4937 < baseStart_4937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 5]
def baseStart_4968 : Nat := 118140960795 + 4968 * 2 ^ 59
def prefixEnd_4968 : Nat := 4983230072969 + 3 ^ 40 * 4968 * 2
def baseEnd_4968 : Nat := 2267530570348263446363

theorem tailTrace_4968 : CollatzResearch.WordTrace tailWord_4968 prefixEnd_4968 2267530570348263446363 := by
  unfold tailWord_4968
  simp only [CollatzResearch.WordTrace]
  refine ⟨90598923004629655979779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120798564006172874639705 90598923004629655979779)
  ·
    refine ⟨135898384506944483969669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90598923004629655979779 135898384506944483969669)
    ·
      refine ⟨25480947095052090744313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135898384506944483969669 25480947095052090744313)
      ·
        refine ⟨19110710321289068058235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25480947095052090744313 19110710321289068058235)
        ·
          refine ⟨28666065481933602087353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19110710321289068058235 28666065481933602087353)
          ·
            refine ⟨21499549111450201565515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28666065481933602087353 21499549111450201565515)
            ·
              refine ⟨32249323667175302348273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21499549111450201565515 32249323667175302348273)
              ·
                refine ⟨24186992750381476761205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32249323667175302348273 24186992750381476761205)
                ·
                  refine ⟨2267530570348263446363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24186992750381476761205 2267530570348263446363)
                  ·
                    rfl

theorem cell20_4968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_4968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4968 prefixEnd_4968 := by exact prefixLift 4968
  have htrace : WordTrace (prefixWord ++ tailWord_4968) baseStart_4968 baseEnd_4968 := by
    simpa [prefixWord, tailWord_4968, baseEnd_4968] using wordTrace_append hprefix tailTrace_4968
  have hstable : (prefixWord ++ tailWord_4968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968).length < 2 ^ (prefixWord ++ tailWord_4968).sum := by decide
  have hdescent : baseEnd_4968 < baseStart_4968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999 : List Nat := [1, 1, 4, 2, 3, 2, 2, 5]
def baseStart_4999 : Nat := 118140960795 + 4999 * 2 ^ 59
def prefixEnd_4999 : Nat := 4983230072969 + 3 ^ 40 * 4999 * 2
def baseEnd_4999 : Nat := 760559938349977804301

theorem tailTrace_4999 : CollatzResearch.WordTrace tailWord_4999 prefixEnd_4999 760559938349977804301 := by
  unfold tailWord_4999
  simp only [CollatzResearch.WordTrace]
  refine ⟨182328508896951606338051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121552339264634404225367 182328508896951606338051)
  ·
    refine ⟨273492763345427409507077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182328508896951606338051 273492763345427409507077)
    ·
      refine ⟨51279893127267639282577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 273492763345427409507077 51279893127267639282577)
      ·
        refine ⟨38459919845450729461933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51279893127267639282577 38459919845450729461933)
        ·
          refine ⟨14422469942044023548225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38459919845450729461933 14422469942044023548225)
          ·
            refine ⟨10816852456533017661169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14422469942044023548225 10816852456533017661169)
            ·
              refine ⟨8112639342399763245877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10816852456533017661169 8112639342399763245877)
              ·
                refine ⟨760559938349977804301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8112639342399763245877 760559938349977804301)
                ·
                  rfl

theorem cell20_4999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 5].length) (baseStart_4999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_4999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_4999 prefixEnd_4999 := by exact prefixLift 4999
  have htrace : WordTrace (prefixWord ++ tailWord_4999) baseStart_4999 baseEnd_4999 := by
    simpa [prefixWord, tailWord_4999, baseEnd_4999] using wordTrace_append hprefix tailTrace_4999
  have hstable : (prefixWord ++ tailWord_4999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999).length < 2 ^ (prefixWord ++ tailWord_4999).sum := by decide
  have hdescent : baseEnd_4999 < baseStart_4999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002 : List Nat := [3, 1, 2, 4, 1, 1, 4, 1, 3]
def baseStart_5002 : Nat := 118140960795 + 5002 * 2 ^ 59
def prefixEnd_5002 : Nat := 4983230072969 + 3 ^ 40 * 5002 * 2
def baseEnd_5002 : Nat := 2283049096795256312891

theorem tailTrace_5002 : CollatzResearch.WordTrace tailWord_5002 prefixEnd_5002 2283049096795256312891 := by
  unfold tailWord_5002
  simp only [CollatzResearch.WordTrace]
  refine ⟨45609481971520779674315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121625285257388745798173 45609481971520779674315)
  ·
    refine ⟨68414222957281169511473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45609481971520779674315 68414222957281169511473)
    ·
      refine ⟨51310667217960877133605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68414222957281169511473 51310667217960877133605)
      ·
        refine ⟨9620750103367664462551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51310667217960877133605 9620750103367664462551)
        ·
          refine ⟨14431125155051496693827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9620750103367664462551 14431125155051496693827)
          ·
            refine ⟨21646687732577245040741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14431125155051496693827 21646687732577245040741)
            ·
              refine ⟨4058753949858233445139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21646687732577245040741 4058753949858233445139)
              ·
                refine ⟨6088130924787350167709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4058753949858233445139 6088130924787350167709)
                ·
                  refine ⟨2283049096795256312891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6088130924787350167709 2283049096795256312891)
                  ·
                    rfl

theorem cell20_5002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_5002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5002 prefixEnd_5002 := by exact prefixLift 5002
  have htrace : WordTrace (prefixWord ++ tailWord_5002) baseStart_5002 baseEnd_5002 := by
    simpa [prefixWord, tailWord_5002, baseEnd_5002] using wordTrace_append hprefix tailTrace_5002
  have hstable : (prefixWord ++ tailWord_5002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002).length < 2 ^ (prefixWord ++ tailWord_5002).sum := by decide
  have hdescent : baseEnd_5002 < baseStart_5002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 7]
def baseStart_5027 : Nat := 118140960795 + 5027 * 2 ^ 59
def prefixEnd_5027 : Nat := 4983230072969 + 3 ^ 40 * 5027 * 2
def baseEnd_5027 : Nat := 2294459778006280479455

theorem tailTrace_5027 : CollatzResearch.WordTrace tailWord_5027 prefixEnd_5027 2294459778006280479455 := by
  unfold tailWord_5027
  simp only [CollatzResearch.WordTrace]
  refine ⟨183349752795512388357335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122233168530341592238223 183349752795512388357335)
  ·
    refine ⟨275024629193268582536003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183349752795512388357335 275024629193268582536003)
    ·
      refine ⟨412536943789902873804005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275024629193268582536003 412536943789902873804005)
      ·
        refine ⟨77350676960606788838251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 412536943789902873804005 77350676960606788838251)
        ·
          refine ⟨116026015440910183257377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77350676960606788838251 116026015440910183257377)
          ·
            refine ⟨87019511580682637443033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116026015440910183257377 87019511580682637443033)
            ·
              refine ⟨65264633685511978082275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87019511580682637443033 65264633685511978082275)
              ·
                refine ⟨97896950528267967123413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65264633685511978082275 97896950528267967123413)
                ·
                  refine ⟨2294459778006280479455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 97896950528267967123413 2294459778006280479455)
                  ·
                    rfl

theorem cell20_5027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_5027 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5027 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5027 prefixEnd_5027 := by exact prefixLift 5027
  have htrace : WordTrace (prefixWord ++ tailWord_5027) baseStart_5027 baseEnd_5027 := by
    simpa [prefixWord, tailWord_5027, baseEnd_5027] using wordTrace_append hprefix tailTrace_5027
  have hstable : (prefixWord ++ tailWord_5027).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027).length < 2 ^ (prefixWord ++ tailWord_5027).sum := by decide
  have hdescent : baseEnd_5027 < baseStart_5027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037 : List Nat := [1, 5, 2, 3, 9]
def baseStart_5037 : Nat := 118140960795 + 5037 * 2 ^ 59
def prefixEnd_5037 : Nat := 4983230072969 + 3 ^ 40 * 5037 * 2
def baseEnd_5037 : Nat := 28383012969020866001

theorem tailTrace_5037 : CollatzResearch.WordTrace tailWord_5037 prefixEnd_5037 28383012969020866001 := by
  unfold tailWord_5037
  simp only [CollatzResearch.WordTrace]
  refine ⟨183714482759284096221365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122476321839522730814243 183714482759284096221365)
  ·
    refine ⟨17223232758682884020753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 183714482759284096221365 17223232758682884020753)
    ·
      refine ⟨12917424569012163015565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17223232758682884020753 12917424569012163015565)
      ·
        refine ⟨4844034213379561130837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12917424569012163015565 4844034213379561130837)
        ·
          refine ⟨28383012969020866001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 4844034213379561130837 28383012969020866001)
          ·
            rfl

theorem cell20_5037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 9].length) (baseStart_5037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5037 prefixEnd_5037 := by exact prefixLift 5037
  have htrace : WordTrace (prefixWord ++ tailWord_5037) baseStart_5037 baseEnd_5037 := by
    simpa [prefixWord, tailWord_5037, baseEnd_5037] using wordTrace_append hprefix tailTrace_5037
  have hstable : (prefixWord ++ tailWord_5037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037).length < 2 ^ (prefixWord ++ tailWord_5037).sum := by decide
  have hdescent : baseEnd_5037 < baseStart_5037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047 : List Nat := [1, 1, 3, 1, 3, 1, 6, 2, 2]
def baseStart_5047 : Nat := 118140960795 + 5047 * 2 ^ 59
def prefixEnd_5047 : Nat := 4983230072969 + 3 ^ 40 * 5047 * 2
def baseEnd_5047 : Nat := 2303588322975099812707

theorem tailTrace_5047 : CollatzResearch.WordTrace tailWord_5047 prefixEnd_5047 2303588322975099812707 := by
  unfold tailWord_5047
  simp only [CollatzResearch.WordTrace]
  refine ⟨184079212723055804085395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122719475148703869390263 184079212723055804085395)
  ·
    refine ⟨276118819084583706128093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184079212723055804085395 276118819084583706128093)
    ·
      refine ⟨103544557156718889798035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276118819084583706128093 103544557156718889798035)
      ·
        refine ⟨155316835735078334697053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103544557156718889798035 155316835735078334697053)
        ·
          refine ⟨58243813400654375511395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155316835735078334697053 58243813400654375511395)
          ·
            refine ⟨87365720100981563267093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58243813400654375511395 87365720100981563267093)
            ·
              refine ⟨4095268129733510778145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87365720100981563267093 4095268129733510778145)
              ·
                refine ⟨3071451097300133083609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4095268129733510778145 3071451097300133083609)
                ·
                  refine ⟨2303588322975099812707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3071451097300133083609 2303588322975099812707)
                  ·
                    rfl

theorem cell20_5047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 2].length) (baseStart_5047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5047 prefixEnd_5047 := by exact prefixLift 5047
  have htrace : WordTrace (prefixWord ++ tailWord_5047) baseStart_5047 baseEnd_5047 := by
    simpa [prefixWord, tailWord_5047, baseEnd_5047] using wordTrace_append hprefix tailTrace_5047
  have hstable : (prefixWord ++ tailWord_5047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047).length < 2 ^ (prefixWord ++ tailWord_5047).sum := by decide
  have hdescent : baseEnd_5047 < baseStart_5047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085 : List Nat := [1, 4, 3, 1, 2, 1, 1, 5, 2]
def baseStart_5085 : Nat := 118140960795 + 5085 * 2 ^ 59
def prefixEnd_5085 : Nat := 4983230072969 + 3 ^ 40 * 5085 * 2
def baseEnd_5085 : Nat := 2320932558415856545885

theorem tailTrace_5085 : CollatzResearch.WordTrace tailWord_5085 prefixEnd_5085 2320932558415856545885 := by
  unfold tailWord_5085
  simp only [CollatzResearch.WordTrace]
  refine ⟨185465186585388293968709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123643457723592195979139 185465186585388293968709)
  ·
    refine ⟨34774722484760305119133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185465186585388293968709 34774722484760305119133)
    ·
      refine ⟨13040520931785114419675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34774722484760305119133 13040520931785114419675)
      ·
        refine ⟨19560781397677671629513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13040520931785114419675 19560781397677671629513)
        ·
          refine ⟨14670586048258253722135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19560781397677671629513 14670586048258253722135)
          ·
            refine ⟨22005879072387380583203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14670586048258253722135 22005879072387380583203)
            ·
              refine ⟨33008818608581070874805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22005879072387380583203 33008818608581070874805)
              ·
                refine ⟨3094576744554475394513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33008818608581070874805 3094576744554475394513)
                ·
                  refine ⟨2320932558415856545885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3094576744554475394513 2320932558415856545885)
                  ·
                    rfl

theorem cell20_5085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_5085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5085 prefixEnd_5085 := by exact prefixLift 5085
  have htrace : WordTrace (prefixWord ++ tailWord_5085) baseStart_5085 baseEnd_5085 := by
    simpa [prefixWord, tailWord_5085, baseEnd_5085] using wordTrace_append hprefix tailTrace_5085
  have hstable : (prefixWord ++ tailWord_5085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085).length < 2 ^ (prefixWord ++ tailWord_5085).sum := by decide
  have hdescent : baseEnd_5085 < baseStart_5085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5127 : List Nat := [1, 1, 4, 3, 1, 1, 1, 4, 4]
def baseStart_5127 : Nat := 118140960795 + 5127 * 2 ^ 59
def prefixEnd_5127 : Nat := 4983230072969 + 3 ^ 40 * 5127 * 2
def baseEnd_5127 : Nat := 2340102502850377145713

theorem tailTrace_5127 : CollatzResearch.WordTrace tailWord_5127 prefixEnd_5127 2340102502850377145713 := by
  unfold tailWord_5127
  simp only [CollatzResearch.WordTrace]
  refine ⟨186997052433229466997635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124664701622152977998423 186997052433229466997635)
  ·
    refine ⟨280495578649844200496453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186997052433229466997635 280495578649844200496453)
    ·
      refine ⟨52592920996845787593085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 280495578649844200496453 52592920996845787593085)
      ·
        refine ⟨19722345373817170347407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52592920996845787593085 19722345373817170347407)
        ·
          refine ⟨29583518060725755521111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19722345373817170347407 29583518060725755521111)
          ·
            refine ⟨44375277091088633281667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29583518060725755521111 44375277091088633281667)
            ·
              refine ⟨66562915636632949922501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44375277091088633281667 66562915636632949922501)
              ·
                refine ⟨12480546681868678110469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66562915636632949922501 12480546681868678110469)
                ·
                  refine ⟨2340102502850377145713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12480546681868678110469 2340102502850377145713)
                  ·
                    rfl

theorem cell20_5127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 4].length) (baseStart_5127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5127 prefixEnd_5127 := by exact prefixLift 5127
  have htrace : WordTrace (prefixWord ++ tailWord_5127) baseStart_5127 baseEnd_5127 := by
    simpa [prefixWord, tailWord_5127, baseEnd_5127] using wordTrace_append hprefix tailTrace_5127
  have hstable : (prefixWord ++ tailWord_5127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5127).length < 2 ^ (prefixWord ++ tailWord_5127).sum := by decide
  have hdescent : baseEnd_5127 < baseStart_5127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5130 : List Nat := [3, 1, 2, 2, 3, 3, 2, 4]
def baseStart_5130 : Nat := 118140960795 + 5130 * 2 ^ 59
def prefixEnd_5130 : Nat := 4983230072969 + 3 ^ 40 * 5130 * 2
def baseEnd_5130 : Nat := 780490594865233348567

theorem tailTrace_5130 : CollatzResearch.WordTrace tailWord_5130 prefixEnd_5130 780490594865233348567 := by
  unfold tailWord_5130
  simp only [CollatzResearch.WordTrace]
  refine ⟨46776617855590244839211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124737647614907319571229 46776617855590244839211)
  ·
    refine ⟨70164926783385367258817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46776617855590244839211 70164926783385367258817)
    ·
      refine ⟨52623695087539025444113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70164926783385367258817 52623695087539025444113)
      ·
        refine ⟨39467771315654269083085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52623695087539025444113 39467771315654269083085)
        ·
          refine ⟨14800414243370350906157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39467771315654269083085 14800414243370350906157)
          ·
            refine ⟨5550155341263881589809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14800414243370350906157 5550155341263881589809)
            ·
              refine ⟨4162616505947911192357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5550155341263881589809 4162616505947911192357)
              ·
                refine ⟨780490594865233348567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4162616505947911192357 780490594865233348567)
                ·
                  rfl

theorem cell20_5130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_5130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5130 prefixEnd_5130 := by exact prefixLift 5130
  have htrace : WordTrace (prefixWord ++ tailWord_5130) baseStart_5130 baseEnd_5130 := by
    simpa [prefixWord, tailWord_5130, baseEnd_5130] using wordTrace_append hprefix tailTrace_5130
  have hstable : (prefixWord ++ tailWord_5130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5130).length < 2 ^ (prefixWord ++ tailWord_5130).sum := by decide
  have hdescent : baseEnd_5130 < baseStart_5130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5206 : List Nat := [5, 2, 2, 1, 2, 8]
def baseStart_5206 : Nat := 118140960795 + 5206 * 2 ^ 59
def prefixEnd_5206 : Nat := 4983230072969 + 3 ^ 40 * 5206 * 2
def baseEnd_5206 : Nat := 88005935388044944891

theorem tailTrace_5206 : CollatzResearch.WordTrace tailWord_5206 prefixEnd_5206 88005935388044944891 := by
  unfold tailWord_5206
  simp only [CollatzResearch.WordTrace]
  refine ⟨11867401196689122445217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126585612764683972748981 11867401196689122445217)
  ·
    refine ⟨8900550897516841833913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11867401196689122445217 8900550897516841833913)
    ·
      refine ⟨6675413173137631375435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8900550897516841833913 6675413173137631375435)
      ·
        refine ⟨10013119759706447063153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6675413173137631375435 10013119759706447063153)
        ·
          refine ⟨7509839819779835297365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10013119759706447063153 7509839819779835297365)
          ·
            refine ⟨88005935388044944891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 7509839819779835297365 88005935388044944891)
            ·
              rfl

theorem cell20_5206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 8].length) (baseStart_5206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5206 prefixEnd_5206 := by exact prefixLift 5206
  have htrace : WordTrace (prefixWord ++ tailWord_5206) baseStart_5206 baseEnd_5206 := by
    simpa [prefixWord, tailWord_5206, baseEnd_5206] using wordTrace_append hprefix tailTrace_5206
  have hstable : (prefixWord ++ tailWord_5206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5206).length < 2 ^ (prefixWord ++ tailWord_5206).sum := by decide
  have hdescent : baseEnd_5206 < baseStart_5206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5217 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 5]
def baseStart_5217 : Nat := 118140960795 + 5217 * 2 ^ 59
def prefixEnd_5217 : Nat := 4983230072969 + 3 ^ 40 * 5217 * 2
def baseEnd_5217 : Nat := 2381180955210064145345

theorem tailTrace_5217 : CollatzResearch.WordTrace tailWord_5217 prefixEnd_5217 2381180955210064145345 := by
  unfold tailWord_5217
  simp only [CollatzResearch.WordTrace]
  refine ⟨190279622107174837773905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126853081404783225182603 190279622107174837773905)
  ·
    refine ⟨142709716580381128330429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190279622107174837773905 142709716580381128330429)
    ·
      refine ⟨53516143717642923123911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142709716580381128330429 53516143717642923123911)
      ·
        refine ⟨80274215576464384685867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53516143717642923123911 80274215576464384685867)
        ·
          refine ⟨120411323364696577028801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80274215576464384685867 120411323364696577028801)
          ·
            refine ⟨90308492523522432771601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120411323364696577028801 90308492523522432771601)
            ·
              refine ⟨67731369392641824578701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90308492523522432771601 67731369392641824578701)
              ·
                refine ⟨25399263522240684217013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67731369392641824578701 25399263522240684217013)
                ·
                  refine ⟨2381180955210064145345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25399263522240684217013 2381180955210064145345)
                  ·
                    rfl

theorem cell20_5217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_5217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5217 prefixEnd_5217 := by exact prefixLift 5217
  have htrace : WordTrace (prefixWord ++ tailWord_5217) baseStart_5217 baseEnd_5217 := by
    simpa [prefixWord, tailWord_5217, baseEnd_5217] using wordTrace_append hprefix tailTrace_5217
  have hstable : (prefixWord ++ tailWord_5217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5217).length < 2 ^ (prefixWord ++ tailWord_5217).sum := by decide
  have hdescent : baseEnd_5217 < baseStart_5217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234 : List Nat := [3, 2, 1, 2, 2, 1, 1, 5, 3]
def baseStart_5234 : Nat := 118140960795 + 5234 * 2 ^ 59
def prefixEnd_5234 : Nat := 4983230072969 + 3 ^ 40 * 5234 * 2
def baseEnd_5234 : Nat := 2388940218433560578609

theorem tailTrace_5234 : CollatzResearch.WordTrace tailWord_5234 prefixEnd_5234 2388940218433560578609 := by
  unfold tailWord_5234
  simp only [CollatzResearch.WordTrace]
  refine ⟨47724915761396685285689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127266442030391160761837 47724915761396685285689)
  ·
    refine ⟨35793686821047513964267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47724915761396685285689 35793686821047513964267)
    ·
      refine ⟨53690530231571270946401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35793686821047513964267 53690530231571270946401)
      ·
        refine ⟨40267897673678453209801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53690530231571270946401 40267897673678453209801)
        ·
          refine ⟨30200923255258839907351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40267897673678453209801 30200923255258839907351)
          ·
            refine ⟨45301384882888259861027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30200923255258839907351 45301384882888259861027)
            ·
              refine ⟨67952077324332389791541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45301384882888259861027 67952077324332389791541)
              ·
                refine ⟨6370507249156161542957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67952077324332389791541 6370507249156161542957)
                ·
                  refine ⟨2388940218433560578609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6370507249156161542957 2388940218433560578609)
                  ·
                    rfl

theorem cell20_5234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_5234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5234 prefixEnd_5234 := by exact prefixLift 5234
  have htrace : WordTrace (prefixWord ++ tailWord_5234) baseStart_5234 baseEnd_5234 := by
    simpa [prefixWord, tailWord_5234, baseEnd_5234] using wordTrace_append hprefix tailTrace_5234
  have hstable : (prefixWord ++ tailWord_5234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234).length < 2 ^ (prefixWord ++ tailWord_5234).sum := by decide
  have hdescent : baseEnd_5234 < baseStart_5234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237 : List Nat := [1, 3, 4, 3, 1, 1, 1, 2, 4]
def baseStart_5237 : Nat := 118140960795 + 5237 * 2 ^ 59
def prefixEnd_5237 : Nat := 4983230072969 + 3 ^ 40 * 5237 * 2
def baseEnd_5237 : Nat := 2390309500178883478597

theorem tailTrace_5237 : CollatzResearch.WordTrace tailWord_5237 prefixEnd_5237 2390309500178883478597 := by
  unfold tailWord_5237
  simp only [CollatzResearch.WordTrace]
  refine ⟨191009082034718253501965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127339388023145502334643 191009082034718253501965)
  ·
    refine ⟨71628405763019345063237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191009082034718253501965 71628405763019345063237)
    ·
      refine ⟨13430326080566127199357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71628405763019345063237 13430326080566127199357)
      ·
        refine ⟨5036372280212297699759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13430326080566127199357 5036372280212297699759)
        ·
          refine ⟨7554558420318446549639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5036372280212297699759 7554558420318446549639)
          ·
            refine ⟨11331837630477669824459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7554558420318446549639 11331837630477669824459)
            ·
              refine ⟨16997756445716504736689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11331837630477669824459 16997756445716504736689)
              ·
                refine ⟨12748317334287378552517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16997756445716504736689 12748317334287378552517)
                ·
                  refine ⟨2390309500178883478597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12748317334287378552517 2390309500178883478597)
                  ·
                    rfl

theorem cell20_5237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_5237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5237 prefixEnd_5237 := by exact prefixLift 5237
  have htrace : WordTrace (prefixWord ++ tailWord_5237) baseStart_5237 baseEnd_5237 := by
    simpa [prefixWord, tailWord_5237, baseEnd_5237] using wordTrace_append hprefix tailTrace_5237
  have hstable : (prefixWord ++ tailWord_5237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237).length < 2 ^ (prefixWord ++ tailWord_5237).sum := by decide
  have hdescent : baseEnd_5237 < baseStart_5237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 5]
def baseStart_5255 : Nat := 118140960795 + 5255 * 2 ^ 59
def prefixEnd_5255 : Nat := 4983230072969 + 3 ^ 40 * 5255 * 2
def baseEnd_5255 : Nat := 2398525190650820878523

theorem tailTrace_5255 : CollatzResearch.WordTrace tailWord_5255 prefixEnd_5255 2398525190650820878523 := by
  unfold tailWord_5255
  simp only [CollatzResearch.WordTrace]
  refine ⟨191665595969507327657219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127777063979671551771479 191665595969507327657219)
  ·
    refine ⟨287498393954260991485829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191665595969507327657219 287498393954260991485829)
    ·
      refine ⟨53905948866423935903593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 287498393954260991485829 53905948866423935903593)
      ·
        refine ⟨40429461649817951927695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53905948866423935903593 40429461649817951927695)
        ·
          refine ⟨60644192474726927891543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40429461649817951927695 60644192474726927891543)
          ·
            refine ⟨90966288712090391837315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60644192474726927891543 90966288712090391837315)
            ·
              refine ⟨136449433068135587755973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90966288712090391837315 136449433068135587755973)
              ·
                refine ⟨25584268700275422704245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136449433068135587755973 25584268700275422704245)
                ·
                  refine ⟨2398525190650820878523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25584268700275422704245 2398525190650820878523)
                  ·
                    rfl

theorem cell20_5255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_5255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5255 prefixEnd_5255 := by exact prefixLift 5255
  have htrace : WordTrace (prefixWord ++ tailWord_5255) baseStart_5255 baseEnd_5255 := by
    simpa [prefixWord, tailWord_5255, baseEnd_5255] using wordTrace_append hprefix tailTrace_5255
  have hstable : (prefixWord ++ tailWord_5255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255).length < 2 ^ (prefixWord ++ tailWord_5255).sum := by decide
  have hdescent : baseEnd_5255 < baseStart_5255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 5]
def baseStart_5272 : Nat := 118140960795 + 5272 * 2 ^ 59
def prefixEnd_5272 : Nat := 4983230072969 + 3 ^ 40 * 5272 * 2
def baseEnd_5272 : Nat := 2406284453874317311787

theorem tailTrace_5272 : CollatzResearch.WordTrace tailWord_5272 prefixEnd_5272 2406284453874317311787 := by
  unfold tailWord_5272
  simp only [CollatzResearch.WordTrace]
  refine ⟨96142818453959615513035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128190424605279487350713 96142818453959615513035)
  ·
    refine ⟨144214227680939423269553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96142818453959615513035 144214227680939423269553)
    ·
      refine ⟨108160670760704567452165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144214227680939423269553 108160670760704567452165)
      ·
        refine ⟨20280125767632106397281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108160670760704567452165 20280125767632106397281)
        ·
          refine ⟨15210094325724079797961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20280125767632106397281 15210094325724079797961)
          ·
            refine ⟨11407570744293059848471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15210094325724079797961 11407570744293059848471)
            ·
              refine ⟨17111356116439589772707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11407570744293059848471 17111356116439589772707)
              ·
                refine ⟨25667034174659384659061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17111356116439589772707 25667034174659384659061)
                ·
                  refine ⟨2406284453874317311787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25667034174659384659061 2406284453874317311787)
                  ·
                    rfl

theorem cell20_5272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_5272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5272 prefixEnd_5272 := by exact prefixLift 5272
  have htrace : WordTrace (prefixWord ++ tailWord_5272) baseStart_5272 baseEnd_5272 := by
    simpa [prefixWord, tailWord_5272, baseEnd_5272] using wordTrace_append hprefix tailTrace_5272
  have hstable : (prefixWord ++ tailWord_5272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272).length < 2 ^ (prefixWord ++ tailWord_5272).sum := by decide
  have hdescent : baseEnd_5272 < baseStart_5272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_5310 : Nat := 118140960795 + 5310 * 2 ^ 59
def prefixEnd_5310 : Nat := 4983230072969 + 3 ^ 40 * 5310 * 2
def baseEnd_5310 : Nat := 2423628689315074044965

theorem tailTrace_5310 : CollatzResearch.WordTrace tailWord_5310 prefixEnd_5310 2423628689315074044965 := by
  unfold tailWord_5310
  simp only [CollatzResearch.WordTrace]
  refine ⟨24208951346281465113673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129114407180167813939589 24208951346281465113673)
  ·
    refine ⟨18156713509711098835255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24208951346281465113673 18156713509711098835255)
    ·
      refine ⟨27235070264566648252883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18156713509711098835255 27235070264566648252883)
      ·
        refine ⟨40852605396849972379325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27235070264566648252883 40852605396849972379325)
        ·
          refine ⟨15319727023818739642247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40852605396849972379325 15319727023818739642247)
          ·
            refine ⟨22979590535728109463371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15319727023818739642247 22979590535728109463371)
            ·
              refine ⟨34469385803592164195057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22979590535728109463371 34469385803592164195057)
              ·
                refine ⟨25852039352694123146293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34469385803592164195057 25852039352694123146293)
                ·
                  refine ⟨2423628689315074044965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25852039352694123146293 2423628689315074044965)
                  ·
                    rfl

theorem cell20_5310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_5310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5310 prefixEnd_5310 := by exact prefixLift 5310
  have htrace : WordTrace (prefixWord ++ tailWord_5310) baseStart_5310 baseEnd_5310 := by
    simpa [prefixWord, tailWord_5310, baseEnd_5310] using wordTrace_append hprefix tailTrace_5310
  have hstable : (prefixWord ++ tailWord_5310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310).length < 2 ^ (prefixWord ++ tailWord_5310).sum := by decide
  have hdescent : baseEnd_5310 < baseStart_5310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383 : List Nat := [1, 1, 4, 14]
def baseStart_5383 : Nat := 118140960795 + 5383 * 2 ^ 59
def prefixEnd_5383 : Nat := 4983230072969 + 3 ^ 40 * 5383 * 2
def baseEnd_5383 : Nat := 10110896619141006631

theorem tailTrace_5383 : CollatzResearch.WordTrace tailWord_5383 prefixEnd_5383 10110896619141006631 := by
  unfold tailWord_5383
  simp only [CollatzResearch.WordTrace]
  refine ⟨196334139505785188316803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130889426337190125544535 196334139505785188316803)
  ·
    refine ⟨294501209258677782475205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196334139505785188316803 294501209258677782475205)
    ·
      refine ⟨55218976736002084214101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 294501209258677782475205 55218976736002084214101)
      ·
        refine ⟨10110896619141006631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 55218976736002084214101 10110896619141006631)
        ·
          rfl

theorem cell20_5383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 14].length) (baseStart_5383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5383 prefixEnd_5383 := by exact prefixLift 5383
  have htrace : WordTrace (prefixWord ++ tailWord_5383) baseStart_5383 baseEnd_5383 := by
    simpa [prefixWord, tailWord_5383, baseEnd_5383] using wordTrace_append hprefix tailTrace_5383
  have hstable : (prefixWord ++ tailWord_5383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383).length < 2 ^ (prefixWord ++ tailWord_5383).sum := by decide
  have hdescent : baseEnd_5383 < baseStart_5383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400 : List Nat := [2, 1, 2, 3, 1, 3, 3, 5]
def baseStart_5400 : Nat := 118140960795 + 5400 * 2 ^ 59
def prefixEnd_5400 : Nat := 4983230072969 + 3 ^ 40 * 5400 * 2
def baseEnd_5400 : Nat := 821569047224920348199

theorem tailTrace_5400 : CollatzResearch.WordTrace tailWord_5400 prefixEnd_5400 821569047224920348199 := by
  unfold tailWord_5400
  simp only [CollatzResearch.WordTrace]
  refine ⟨98477090222098545842827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131302786962798061123769 98477090222098545842827)
  ·
    refine ⟨147715635333147818764241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98477090222098545842827 147715635333147818764241)
    ·
      refine ⟨110786726499860864073181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147715635333147818764241 110786726499860864073181)
      ·
        refine ⟨41545022437447824027443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110786726499860864073181 41545022437447824027443)
        ·
          refine ⟨62317533656171736041165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41545022437447824027443 62317533656171736041165)
          ·
            refine ⟨23369075121064401015437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62317533656171736041165 23369075121064401015437)
            ·
              refine ⟨8763403170399150380789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23369075121064401015437 8763403170399150380789)
              ·
                refine ⟨821569047224920348199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8763403170399150380789 821569047224920348199)
                ·
                  rfl

theorem cell20_5400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_5400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5400 prefixEnd_5400 := by exact prefixLift 5400
  have htrace : WordTrace (prefixWord ++ tailWord_5400) baseStart_5400 baseEnd_5400 := by
    simpa [prefixWord, tailWord_5400, baseEnd_5400] using wordTrace_append hprefix tailTrace_5400
  have hstable : (prefixWord ++ tailWord_5400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400).length < 2 ^ (prefixWord ++ tailWord_5400).sum := by decide
  have hdescent : baseEnd_5400 < baseStart_5400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5410 : List Nat := [3, 3, 1, 1, 4, 1, 1, 2, 4]
def baseStart_5410 : Nat := 118140960795 + 5410 * 2 ^ 59
def prefixEnd_5410 : Nat := 4983230072969 + 3 ^ 40 * 5410 * 2
def baseEnd_5410 : Nat := 2469271414159170711223

theorem tailTrace_5410 : CollatzResearch.WordTrace tailWord_5410 prefixEnd_5410 2469271414159170711223 := by
  unfold tailWord_5410
  simp only [CollatzResearch.WordTrace]
  refine ⟨49329727601992199887421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131545940271979199699789 49329727601992199887421)
  ·
    refine ⟨18498647850747074957783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49329727601992199887421 18498647850747074957783)
    ·
      refine ⟨27747971776120612436675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18498647850747074957783 27747971776120612436675)
      ·
        refine ⟨41621957664180918655013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27747971776120612436675 41621957664180918655013)
        ·
          refine ⟨7804117062033922247815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41621957664180918655013 7804117062033922247815)
          ·
            refine ⟨11706175593050883371723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7804117062033922247815 11706175593050883371723)
            ·
              refine ⟨17559263389576325057585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11706175593050883371723 17559263389576325057585)
              ·
                refine ⟨13169447542182243793189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17559263389576325057585 13169447542182243793189)
                ·
                  refine ⟨2469271414159170711223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13169447542182243793189 2469271414159170711223)
                  ·
                    rfl

theorem cell20_5410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_5410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5410 prefixEnd_5410 := by exact prefixLift 5410
  have htrace : WordTrace (prefixWord ++ tailWord_5410) baseStart_5410 baseEnd_5410 := by
    simpa [prefixWord, tailWord_5410, baseEnd_5410] using wordTrace_append hprefix tailTrace_5410
  have hstable : (prefixWord ++ tailWord_5410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5410).length < 2 ^ (prefixWord ++ tailWord_5410).sum := by decide
  have hdescent : baseEnd_5410 < baseStart_5410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437 : List Nat := [1, 4, 1, 5, 2, 1, 1, 2, 3]
def baseStart_5437 : Nat := 118140960795 + 5437 * 2 ^ 59
def prefixEnd_5437 : Nat := 4983230072969 + 3 ^ 40 * 5437 * 2
def baseEnd_5437 : Nat := 2481594949867076811113

theorem tailTrace_5437 : CollatzResearch.WordTrace tailWord_5437 prefixEnd_5437 2481594949867076811113 := by
  unfold tailWord_5437
  simp only [CollatzResearch.WordTrace]
  refine ⟨198303681310152410782565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132202454206768273855043 198303681310152410782565)
  ·
    refine ⟨37181940245653577021731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198303681310152410782565 37181940245653577021731)
    ·
      refine ⟨55772910368480365532597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37181940245653577021731 55772910368480365532597)
      ·
        refine ⟨5228710347045034268681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55772910368480365532597 5228710347045034268681)
        ·
          refine ⟨3921532760283775701511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5228710347045034268681 3921532760283775701511)
          ·
            refine ⟨5882299140425663552267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3921532760283775701511 5882299140425663552267)
            ·
              refine ⟨8823448710638495328401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5882299140425663552267 8823448710638495328401)
              ·
                refine ⟨6617586532978871496301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8823448710638495328401 6617586532978871496301)
                ·
                  refine ⟨2481594949867076811113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6617586532978871496301 2481594949867076811113)
                  ·
                    rfl

theorem cell20_5437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_5437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5437 prefixEnd_5437 := by exact prefixLift 5437
  have htrace : WordTrace (prefixWord ++ tailWord_5437) baseStart_5437 baseEnd_5437 := by
    simpa [prefixWord, tailWord_5437, baseEnd_5437] using wordTrace_append hprefix tailTrace_5437
  have hstable : (prefixWord ++ tailWord_5437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437).length < 2 ^ (prefixWord ++ tailWord_5437).sum := by decide
  have hdescent : baseEnd_5437 < baseStart_5437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438 : List Nat := [4, 2, 1, 2, 1, 1, 9]
def baseStart_5438 : Nat := 118140960795 + 5438 * 2 ^ 59
def prefixEnd_5438 : Nat := 4983230072969 + 3 ^ 40 * 5438 * 2
def baseEnd_5438 : Nat := 275783486346168641975

theorem tailTrace_5438 : CollatzResearch.WordTrace tailWord_5438 prefixEnd_5438 275783486346168641975 := by
  unfold tailWord_5438
  simp only [CollatzResearch.WordTrace]
  refine ⟨24792519288316197696121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132226769537686387712645 24792519288316197696121)
  ·
    refine ⟨18594389466237148272091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24792519288316197696121 18594389466237148272091)
    ·
      refine ⟨27891584199355722408137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18594389466237148272091 27891584199355722408137)
      ·
        refine ⟨20918688149516791806103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27891584199355722408137 20918688149516791806103)
        ·
          refine ⟨31378032224275187709155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20918688149516791806103 31378032224275187709155)
          ·
            refine ⟨47067048336412781563733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31378032224275187709155 47067048336412781563733)
            ·
              refine ⟨275783486346168641975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 47067048336412781563733 275783486346168641975)
              ·
                rfl

theorem cell20_5438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 9].length) (baseStart_5438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5438 prefixEnd_5438 := by exact prefixLift 5438
  have htrace : WordTrace (prefixWord ++ tailWord_5438) baseStart_5438 baseEnd_5438 := by
    simpa [prefixWord, tailWord_5438, baseEnd_5438] using wordTrace_append hprefix tailTrace_5438
  have hstable : (prefixWord ++ tailWord_5438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438).length < 2 ^ (prefixWord ++ tailWord_5438).sum := by decide
  have hdescent : baseEnd_5438 < baseStart_5438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5441 : List Nat := [1, 2, 5, 2, 1, 1, 3, 2, 3]
def baseStart_5441 : Nat := 118140960795 + 5441 * 2 ^ 59
def prefixEnd_5441 : Nat := 4983230072969 + 3 ^ 40 * 5441 * 2
def baseEnd_5441 : Nat := 2483420658860840677763

theorem tailTrace_5441 : CollatzResearch.WordTrace tailWord_5441 prefixEnd_5441 2483420658860840677763 := by
  unfold tailWord_5441
  simp only [CollatzResearch.WordTrace]
  refine ⟨198449573295661093928177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132299715530440729285451 198449573295661093928177)
  ·
    refine ⟨148837179971745820446133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198449573295661093928177 148837179971745820446133)
    ·
      refine ⟨13953485622351170666825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 148837179971745820446133 13953485622351170666825)
      ·
        refine ⟨10465114216763378000119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13953485622351170666825 10465114216763378000119)
        ·
          refine ⟨15697671325145067000179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10465114216763378000119 15697671325145067000179)
          ·
            refine ⟨23546506987717600500269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15697671325145067000179 23546506987717600500269)
            ·
              refine ⟨8829940120394100187601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23546506987717600500269 8829940120394100187601)
              ·
                refine ⟨6622455090295575140701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8829940120394100187601 6622455090295575140701)
                ·
                  refine ⟨2483420658860840677763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6622455090295575140701 2483420658860840677763)
                  ·
                    rfl

theorem cell20_5441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 3].length) (baseStart_5441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5441 prefixEnd_5441 := by exact prefixLift 5441
  have htrace : WordTrace (prefixWord ++ tailWord_5441) baseStart_5441 baseEnd_5441 := by
    simpa [prefixWord, tailWord_5441, baseEnd_5441] using wordTrace_append hprefix tailTrace_5441
  have hstable : (prefixWord ++ tailWord_5441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5441).length < 2 ^ (prefixWord ++ tailWord_5441).sum := by decide
  have hdescent : baseEnd_5441 < baseStart_5441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459 : List Nat := [1, 1, 1, 2, 1, 1, 6, 7]
def baseStart_5459 : Nat := 118140960795 + 5459 * 2 ^ 59
def prefixEnd_5459 : Nat := 4983230072969 + 3 ^ 40 * 5459 * 2
def baseEnd_5459 : Nat := 830545449777592692563

theorem tailTrace_5459 : CollatzResearch.WordTrace tailWord_5459 prefixEnd_5459 830545449777592692563 := by
  unfold tailWord_5459
  simp only [CollatzResearch.WordTrace]
  refine ⟨199106087230450168083431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132737391486966778722287 199106087230450168083431)
  ·
    refine ⟨298659130845675252125147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199106087230450168083431 298659130845675252125147)
    ·
      refine ⟨447988696268512878187721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298659130845675252125147 447988696268512878187721)
      ·
        refine ⟨335991522201384658640791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447988696268512878187721 335991522201384658640791)
        ·
          refine ⟨503987283302076987961187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335991522201384658640791 503987283302076987961187)
          ·
            refine ⟨755980924953115481941781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503987283302076987961187 755980924953115481941781)
            ·
              refine ⟨35436605857177288216021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 755980924953115481941781 35436605857177288216021)
              ·
                refine ⟨830545449777592692563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 35436605857177288216021 830545449777592692563)
                ·
                  rfl

theorem cell20_5459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 7].length) (baseStart_5459 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5459 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5459 prefixEnd_5459 := by exact prefixLift 5459
  have htrace : WordTrace (prefixWord ++ tailWord_5459) baseStart_5459 baseEnd_5459 := by
    simpa [prefixWord, tailWord_5459, baseEnd_5459] using wordTrace_append hprefix tailTrace_5459
  have hstable : (prefixWord ++ tailWord_5459).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459).length < 2 ^ (prefixWord ++ tailWord_5459).sum := by decide
  have hdescent : baseEnd_5459 < baseStart_5459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476 : List Nat := [2, 3, 1, 1, 3, 3, 1, 6]
def baseStart_5476 : Nat := 118140960795 + 5476 * 2 ^ 59
def prefixEnd_5476 : Nat := 4983230072969 + 3 ^ 40 * 5476 * 2
def baseEnd_5476 : Nat := 833131870852091503651

theorem tailTrace_5476 : CollatzResearch.WordTrace tailWord_5476 prefixEnd_5476 833131870852091503651 := by
  unfold tailWord_5476
  simp only [CollatzResearch.WordTrace]
  refine ⟨99863064084431035726141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133150752112574714301521 99863064084431035726141)
  ·
    refine ⟨37448649031661638397303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99863064084431035726141 37448649031661638397303)
    ·
      refine ⟨56172973547492457595955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37448649031661638397303 56172973547492457595955)
      ·
        refine ⟨84259460321238686393933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56172973547492457595955 84259460321238686393933)
        ·
          refine ⟨31597297620464507397725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84259460321238686393933 31597297620464507397725)
          ·
            refine ⟨11848986607674190274147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31597297620464507397725 11848986607674190274147)
            ·
              refine ⟨17773479911511285411221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11848986607674190274147 17773479911511285411221)
              ·
                refine ⟨833131870852091503651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17773479911511285411221 833131870852091503651)
                ·
                  rfl

theorem cell20_5476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_5476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5476 prefixEnd_5476 := by exact prefixLift 5476
  have htrace : WordTrace (prefixWord ++ tailWord_5476) baseStart_5476 baseEnd_5476 := by
    simpa [prefixWord, tailWord_5476, baseEnd_5476] using wordTrace_append hprefix tailTrace_5476
  have hstable : (prefixWord ++ tailWord_5476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476).length < 2 ^ (prefixWord ++ tailWord_5476).sum := by decide
  have hdescent : baseEnd_5476 < baseStart_5476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482 : List Nat := [3, 1, 3, 3, 2, 2, 1, 3, 2]
def baseStart_5482 : Nat := 118140960795 + 5482 * 2 ^ 59
def prefixEnd_5482 : Nat := 4983230072969 + 3 ^ 40 * 5482 * 2
def baseEnd_5482 : Nat := 2502134176046920310929

theorem tailTrace_5482 : CollatzResearch.WordTrace tailWord_5482 prefixEnd_5482 2502134176046920310929 := by
  unfold tailWord_5482
  simp only [CollatzResearch.WordTrace]
  refine ⟨49986241536781274042675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133296644098083397447133 49986241536781274042675)
  ·
    refine ⟨74979362305171911064013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49986241536781274042675 74979362305171911064013)
    ·
      refine ⟨28117260864439466649005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74979362305171911064013 28117260864439466649005)
      ·
        refine ⟨10543972824164799993377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28117260864439466649005 10543972824164799993377)
        ·
          refine ⟨7907979618123599995033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10543972824164799993377 7907979618123599995033)
          ·
            refine ⟨5930984713592699996275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7907979618123599995033 5930984713592699996275)
            ·
              refine ⟨8896477070389049994413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5930984713592699996275 8896477070389049994413)
              ·
                refine ⟨3336178901395893747905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8896477070389049994413 3336178901395893747905)
                ·
                  refine ⟨2502134176046920310929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3336178901395893747905 2502134176046920310929)
                  ·
                    rfl

theorem cell20_5482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 2].length) (baseStart_5482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5482 prefixEnd_5482 := by exact prefixLift 5482
  have htrace : WordTrace (prefixWord ++ tailWord_5482) baseStart_5482 baseEnd_5482 := by
    simpa [prefixWord, tailWord_5482, baseEnd_5482] using wordTrace_append hprefix tailTrace_5482
  have hstable : (prefixWord ++ tailWord_5482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482).length < 2 ^ (prefixWord ++ tailWord_5482).sum := by decide
  have hdescent : baseEnd_5482 < baseStart_5482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493 : List Nat := [1, 3, 4, 1, 3, 2, 6]
def baseStart_5493 : Nat := 118140960795 + 5493 * 2 ^ 59
def prefixEnd_5493 : Nat := 4983230072969 + 3 ^ 40 * 5493 * 2
def baseEnd_5493 : Nat := 278572763975530104913

theorem tailTrace_5493 : CollatzResearch.WordTrace tailWord_5493 prefixEnd_5493 278572763975530104913 := by
  unfold tailWord_5493
  simp only [CollatzResearch.WordTrace]
  refine ⟨200346169107273974821133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133564112738182649880755 200346169107273974821133)
  ·
    refine ⟨75129813415227740557925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200346169107273974821133 75129813415227740557925)
    ·
      refine ⟨14086840015355201354611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75129813415227740557925 14086840015355201354611)
      ·
        refine ⟨21130260023032802031917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14086840015355201354611 21130260023032802031917)
        ·
          refine ⟨7923847508637300761969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21130260023032802031917 7923847508637300761969)
          ·
            refine ⟨5942885631477975571477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7923847508637300761969 5942885631477975571477)
            ·
              refine ⟨278572763975530104913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5942885631477975571477 278572763975530104913)
              ·
                rfl

theorem cell20_5493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 6].length) (baseStart_5493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5493 prefixEnd_5493 := by exact prefixLift 5493
  have htrace : WordTrace (prefixWord ++ tailWord_5493) baseStart_5493 baseEnd_5493 := by
    simpa [prefixWord, tailWord_5493, baseEnd_5493] using wordTrace_append hprefix tailTrace_5493
  have hstable : (prefixWord ++ tailWord_5493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493).length < 2 ^ (prefixWord ++ tailWord_5493).sum := by decide
  have hdescent : baseEnd_5493 < baseStart_5493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497 : List Nat := [1, 2, 1, 3, 2, 1, 10]
def baseStart_5497 : Nat := 118140960795 + 5497 * 2 ^ 59
def prefixEnd_5497 : Nat := 4983230072969 + 3 ^ 40 * 5497 * 2
def baseEnd_5497 : Nat := 278775620530392756763

theorem tailTrace_5497 : CollatzResearch.WordTrace tailWord_5497 prefixEnd_5497 278775620530392756763 := by
  unfold tailWord_5497
  simp only [CollatzResearch.WordTrace]
  refine ⟨200492061092782657966745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133661374061855105311163 200492061092782657966745)
  ·
    refine ⟨150369045819586993475059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200492061092782657966745 150369045819586993475059)
    ·
      refine ⟨225553568729380490212589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150369045819586993475059 225553568729380490212589)
      ·
        refine ⟨84582588273517683829721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225553568729380490212589 84582588273517683829721)
        ·
          refine ⟨63436941205138262872291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84582588273517683829721 63436941205138262872291)
          ·
            refine ⟨95155411807707394308437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63436941205138262872291 95155411807707394308437)
            ·
              refine ⟨278775620530392756763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 95155411807707394308437 278775620530392756763)
              ·
                rfl

theorem cell20_5497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 10].length) (baseStart_5497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5497 prefixEnd_5497 := by exact prefixLift 5497
  have htrace : WordTrace (prefixWord ++ tailWord_5497) baseStart_5497 baseEnd_5497 := by
    simpa [prefixWord, tailWord_5497, baseEnd_5497] using wordTrace_append hprefix tailTrace_5497
  have hstable : (prefixWord ++ tailWord_5497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497).length < 2 ^ (prefixWord ++ tailWord_5497).sum := by decide
  have hdescent : baseEnd_5497 < baseStart_5497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507 : List Nat := [1, 1, 1, 3, 5, 1, 3, 1, 4]
def baseStart_5507 : Nat := 118140960795 + 5507 * 2 ^ 59
def prefixEnd_5507 : Nat := 4983230072969 + 3 ^ 40 * 5507 * 2
def baseEnd_5507 : Nat := 2513544857257944477493

theorem tailTrace_5507 : CollatzResearch.WordTrace tailWord_5507 prefixEnd_5507 2513544857257944477493 := by
  unfold tailWord_5507
  simp only [CollatzResearch.WordTrace]
  refine ⟨200856791056554365830775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133904527371036243887183 200856791056554365830775)
  ·
    refine ⟨301285186584831548746163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200856791056554365830775 301285186584831548746163)
    ·
      refine ⟨451927779877247323119245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301285186584831548746163 451927779877247323119245)
      ·
        refine ⟨169472917453967746169717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 451927779877247323119245 169472917453967746169717)
        ·
          refine ⟨15888086011309476203411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 169472917453967746169717 15888086011309476203411)
          ·
            refine ⟨23832129016964214305117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15888086011309476203411 23832129016964214305117)
            ·
              refine ⟨8937048381361580364419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23832129016964214305117 8937048381361580364419)
              ·
                refine ⟨13405572572042370546629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8937048381361580364419 13405572572042370546629)
                ·
                  refine ⟨2513544857257944477493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13405572572042370546629 2513544857257944477493)
                  ·
                    rfl

theorem cell20_5507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 4].length) (baseStart_5507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5507 prefixEnd_5507 := by exact prefixLift 5507
  have htrace : WordTrace (prefixWord ++ tailWord_5507) baseStart_5507 baseEnd_5507 := by
    simpa [prefixWord, tailWord_5507, baseEnd_5507] using wordTrace_append hprefix tailTrace_5507
  have hstable : (prefixWord ++ tailWord_5507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507).length < 2 ^ (prefixWord ++ tailWord_5507).sum := by decide
  have hdescent : baseEnd_5507 < baseStart_5507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521 : List Nat := [1, 2, 2, 1, 1, 1, 2, 7, 3]
def baseStart_5521 : Nat := 118140960795 + 5521 * 2 ^ 59
def prefixEnd_5521 : Nat := 4983230072969 + 3 ^ 40 * 5521 * 2
def baseEnd_5521 : Nat := 2519934838736118010769

theorem tailTrace_5521 : CollatzResearch.WordTrace tailWord_5521 prefixEnd_5521 2519934838736118010769 := by
  unfold tailWord_5521
  simp only [CollatzResearch.WordTrace]
  refine ⟨201367413005834756840417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134244942003889837893611 201367413005834756840417)
  ·
    refine ⟨151025559754376067630313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201367413005834756840417 151025559754376067630313)
    ·
      refine ⟨113269169815782050722735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151025559754376067630313 113269169815782050722735)
      ·
        refine ⟨169903754723673076084103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113269169815782050722735 169903754723673076084103)
        ·
          refine ⟨254855632085509614126155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169903754723673076084103 254855632085509614126155)
          ·
            refine ⟨382283448128264421189233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254855632085509614126155 382283448128264421189233)
            ·
              refine ⟨286712586096198315891925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382283448128264421189233 286712586096198315891925)
              ·
                refine ⟨6719826236629648028717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 286712586096198315891925 6719826236629648028717)
                ·
                  refine ⟨2519934838736118010769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6719826236629648028717 2519934838736118010769)
                  ·
                    rfl

theorem cell20_5521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 3].length) (baseStart_5521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5521 prefixEnd_5521 := by exact prefixLift 5521
  have htrace : WordTrace (prefixWord ++ tailWord_5521) baseStart_5521 baseEnd_5521 := by
    simpa [prefixWord, tailWord_5521, baseEnd_5521] using wordTrace_append hprefix tailTrace_5521
  have hstable : (prefixWord ++ tailWord_5521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521).length < 2 ^ (prefixWord ++ tailWord_5521).sum := by decide
  have hdescent : baseEnd_5521 < baseStart_5521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610 : List Nat := [3, 1, 3, 1, 5, 1, 1, 2, 3]
def baseStart_5610 : Nat := 118140960795 + 5610 * 2 ^ 59
def prefixEnd_5610 : Nat := 4983230072969 + 3 ^ 40 * 5610 * 2
def baseEnd_5610 : Nat := 2560556863847364043739

theorem tailTrace_5610 : CollatzResearch.WordTrace tailWord_5610 prefixEnd_5610 2560556863847364043739 := by
  unfold tailWord_5610
  simp only [CollatzResearch.WordTrace]
  refine ⟨51153377420850739207571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136409006455601971220189 51153377420850739207571)
  ·
    refine ⟨76730066131276108811357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51153377420850739207571 76730066131276108811357)
    ·
      refine ⟨28773774799228540804259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76730066131276108811357 28773774799228540804259)
      ·
        refine ⟨43160662198842811206389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28773774799228540804259 43160662198842811206389)
        ·
          refine ⟨4046312081141513550599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43160662198842811206389 4046312081141513550599)
          ·
            refine ⟨6069468121712270325899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4046312081141513550599 6069468121712270325899)
            ·
              refine ⟨9104202182568405488849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6069468121712270325899 9104202182568405488849)
              ·
                refine ⟨6828151636926304116637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9104202182568405488849 6828151636926304116637)
                ·
                  refine ⟨2560556863847364043739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6828151636926304116637 2560556863847364043739)
                  ·
                    rfl

theorem cell20_5610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 3].length) (baseStart_5610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5610 prefixEnd_5610 := by exact prefixLift 5610
  have htrace : WordTrace (prefixWord ++ tailWord_5610) baseStart_5610 baseEnd_5610 := by
    simpa [prefixWord, tailWord_5610, baseEnd_5610] using wordTrace_append hprefix tailTrace_5610
  have hstable : (prefixWord ++ tailWord_5610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610).length < 2 ^ (prefixWord ++ tailWord_5610).sum := by decide
  have hdescent : baseEnd_5610 < baseStart_5610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649 : List Nat := [1, 2, 2, 1, 1, 2, 5, 6]
def baseStart_5649 : Nat := 118140960795 + 5649 * 2 ^ 59
def prefixEnd_5649 : Nat := 4983230072969 + 3 ^ 40 * 5649 * 2
def baseEnd_5649 : Nat := 859452508845520581193

theorem tailTrace_5649 : CollatzResearch.WordTrace tailWord_5649 prefixEnd_5649 859452508845520581193 := by
  unfold tailWord_5649
  simp only [CollatzResearch.WordTrace]
  refine ⟨206035956542112617500001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137357304361408411666667 206035956542112617500001)
  ·
    refine ⟨154526967406584463125001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206035956542112617500001 154526967406584463125001)
    ·
      refine ⟨115895225554938347343751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154526967406584463125001 115895225554938347343751)
      ·
        refine ⟨173842838332407521015627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115895225554938347343751 173842838332407521015627)
        ·
          refine ⟨260764257498611281523441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173842838332407521015627 260764257498611281523441)
          ·
            refine ⟨195573193123958461142581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260764257498611281523441 195573193123958461142581)
            ·
              refine ⟨18334986855371105732117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 195573193123958461142581 18334986855371105732117)
              ·
                refine ⟨859452508845520581193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18334986855371105732117 859452508845520581193)
                ·
                  rfl

theorem cell20_5649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 6].length) (baseStart_5649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5649 prefixEnd_5649 := by exact prefixLift 5649
  have htrace : WordTrace (prefixWord ++ tailWord_5649) baseStart_5649 baseEnd_5649 := by
    simpa [prefixWord, tailWord_5649, baseEnd_5649] using wordTrace_append hprefix tailTrace_5649
  have hstable : (prefixWord ++ tailWord_5649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649).length < 2 ^ (prefixWord ++ tailWord_5649).sum := by decide
  have hdescent : baseEnd_5649 < baseStart_5649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
