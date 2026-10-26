import V185TrunkScan23Chunk0652

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3860762 : List Nat := [3, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3]
def baseStart_3860762 : Nat := 118140960795 + 3860762 * 2 ^ 59
def prefixEnd_3860762 : Nat := 4983230072969 + 3 ^ 40 * 3860762 * 2
def baseEnd_3860762 : Nat := 1982426598613728984619685

theorem tailTrace_3860762 : CollatzResearch.WordTrace tailWord_3860762 prefixEnd_3860762 1982426598613728984619685 := by
  unfold tailWord_3860762
  simp only [CollatzResearch.WordTrace]
  refine ⟨35203389609781528624982135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93875705626084076333285693 35203389609781528624982135)
  ·
    refine ⟨52805084414672292937473203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35203389609781528624982135 52805084414672292937473203)
    ·
      refine ⟨79207626622008439406209805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52805084414672292937473203 79207626622008439406209805)
      ·
        refine ⟨29702859983253164777328677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79207626622008439406209805 29702859983253164777328677)
        ·
          refine ⟨5569286246859968395749127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29702859983253164777328677 5569286246859968395749127)
          ·
            refine ⟨8353929370289952593623691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5569286246859968395749127 8353929370289952593623691)
            ·
              refine ⟨12530894055434928890435537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8353929370289952593623691 12530894055434928890435537)
              ·
                refine ⟨9398170541576196667826653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12530894055434928890435537 9398170541576196667826653)
                ·
                  refine ⟨3524313953091073750434995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9398170541576196667826653 3524313953091073750434995)
                  ·
                    refine ⟨5286470929636610625652493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3524313953091073750434995 5286470929636610625652493)
                    ·
                      refine ⟨1982426598613728984619685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5286470929636610625652493 1982426598613728984619685)
                      ·
                        rfl

theorem cell23_3860762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_3860762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860762 prefixEnd_3860762 := by exact prefixLift 3860762
  have htrace : WordTrace (prefixWord ++ tailWord_3860762) baseStart_3860762 baseEnd_3860762 := by
    simpa [prefixWord, tailWord_3860762, baseEnd_3860762] using wordTrace_append hprefix tailTrace_3860762
  have hstable : (prefixWord ++ tailWord_3860762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860762).length < 2 ^ (prefixWord ++ tailWord_3860762).sum := by decide
  have hdescent : baseEnd_3860762 < baseStart_3860762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860772 : List Nat := [2, 3, 1, 3, 1, 2, 3, 1, 2, 3, 2]
def baseStart_3860772 : Nat := 118140960795 + 3860772 * 2 ^ 59
def prefixEnd_3860772 : Nat := 4983230072969 + 3 ^ 40 * 3860772 * 2
def baseEnd_3860772 : Nat := 1982431733420273945494639

theorem tailTrace_3860772 : CollatzResearch.WordTrace tailWord_3860772 prefixEnd_3860772 1982431733420273945494639 := by
  unfold tailWord_3860772
  simp only [CollatzResearch.WordTrace]
  refine ⟨70406961584544943103896285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93875948779393257471861713 70406961584544943103896285)
  ·
    refine ⟨26402610594204353663961107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70406961584544943103896285 26402610594204353663961107)
    ·
      refine ⟨39603915891306530495941661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26402610594204353663961107 39603915891306530495941661)
      ·
        refine ⟨14851468459239948935978123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39603915891306530495941661 14851468459239948935978123)
        ·
          refine ⟨22277202688859923403967185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14851468459239948935978123 22277202688859923403967185)
          ·
            refine ⟨16707902016644942552975389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22277202688859923403967185 16707902016644942552975389)
            ·
              refine ⟨6265463256241853457365771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16707902016644942552975389 6265463256241853457365771)
              ·
                refine ⟨9398194884362780186048657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6265463256241853457365771 9398194884362780186048657)
                ·
                  refine ⟨7048646163272085139536493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9398194884362780186048657 7048646163272085139536493)
                  ·
                    refine ⟨2643242311227031927326185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7048646163272085139536493 2643242311227031927326185)
                    ·
                      refine ⟨1982431733420273945494639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2643242311227031927326185 1982431733420273945494639)
                      ·
                        rfl

theorem cell23_3860772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_3860772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860772 prefixEnd_3860772 := by exact prefixLift 3860772
  have htrace : WordTrace (prefixWord ++ tailWord_3860772) baseStart_3860772 baseEnd_3860772 := by
    simpa [prefixWord, tailWord_3860772, baseEnd_3860772] using wordTrace_append hprefix tailTrace_3860772
  have hstable : (prefixWord ++ tailWord_3860772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860772).length < 2 ^ (prefixWord ++ tailWord_3860772).sum := by decide
  have hdescent : baseEnd_3860772 < baseStart_3860772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860811 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 6]
def baseStart_3860811 : Nat := 118140960795 + 3860811 * 2 ^ 59
def prefixEnd_3860811 : Nat := 4983230072969 + 3 ^ 40 * 3860811 * 2
def baseEnd_3860811 : Nat := 1982451759165799292906959

theorem tailTrace_3860811 : CollatzResearch.WordTrace tailWord_3860811 prefixEnd_3860811 1982451759165799292906959 := by
  unfold tailWord_3860811
  simp only [CollatzResearch.WordTrace]
  refine ⟨140815345615948595868462287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93876897077299063912308191 140815345615948595868462287)
  ·
    refine ⟨211223018423922893802693431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140815345615948595868462287 211223018423922893802693431)
    ·
      refine ⟨316834527635884340704040147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211223018423922893802693431 316834527635884340704040147)
      ·
        refine ⟨475251791453826511056060221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316834527635884340704040147 475251791453826511056060221)
        ·
          refine ⟨178219421795184941646022583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 475251791453826511056060221 178219421795184941646022583)
          ·
            refine ⟨267329132692777412469033875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178219421795184941646022583 267329132692777412469033875)
            ·
              refine ⟨400993699039166118703550813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267329132692777412469033875 400993699039166118703550813)
              ·
                refine ⟨150372637139687294513831555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 400993699039166118703550813 150372637139687294513831555)
                ·
                  refine ⟨225558955709530941770747333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150372637139687294513831555 225558955709530941770747333)
                  ·
                    refine ⟨42292304195537051582015125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 225558955709530941770747333 42292304195537051582015125)
                    ·
                      refine ⟨1982451759165799292906959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42292304195537051582015125 1982451759165799292906959)
                      ·
                        rfl

theorem cell23_3860811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 6].length) (baseStart_3860811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860811 prefixEnd_3860811 := by exact prefixLift 3860811
  have htrace : WordTrace (prefixWord ++ tailWord_3860811) baseStart_3860811 baseEnd_3860811 := by
    simpa [prefixWord, tailWord_3860811, baseEnd_3860811] using wordTrace_append hprefix tailTrace_3860811
  have hstable : (prefixWord ++ tailWord_3860811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860811).length < 2 ^ (prefixWord ++ tailWord_3860811).sum := by decide
  have hdescent : baseEnd_3860811 < baseStart_3860811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860812 : List Nat := [2, 2, 1, 3, 2, 1, 5, 1, 2, 4]
def baseStart_3860812 : Nat := 118140960795 + 3860812 * 2 ^ 59
def prefixEnd_3860812 : Nat := 4983230072969 + 3 ^ 40 * 3860812 * 2
def baseEnd_3860812 : Nat := 660817424215484596331485

theorem tailTrace_3860812 : CollatzResearch.WordTrace tailWord_3860812 prefixEnd_3860812 660817424215484596331485 := by
  unfold tailWord_3860812
  simp only [CollatzResearch.WordTrace]
  refine ⟨70407691044472486519624345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93876921392629982026165793 70407691044472486519624345)
  ·
    refine ⟨52805768283354364889718259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70407691044472486519624345 52805768283354364889718259)
    ·
      refine ⟨79208652425031547334577389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52805768283354364889718259 79208652425031547334577389)
      ·
        refine ⟨29703244659386830250466521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79208652425031547334577389 29703244659386830250466521)
        ·
          refine ⟨22277433494540122687849891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29703244659386830250466521 22277433494540122687849891)
          ·
            refine ⟨33416150241810184031774837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22277433494540122687849891 33416150241810184031774837)
            ·
              refine ⟨3132764085169704752978891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33416150241810184031774837 3132764085169704752978891)
              ·
                refine ⟨4699146127754557129468337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3132764085169704752978891 4699146127754557129468337)
                ·
                  refine ⟨3524359595815917847101253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4699146127754557129468337 3524359595815917847101253)
                  ·
                    refine ⟨660817424215484596331485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3524359595815917847101253 660817424215484596331485)
                    ·
                      rfl

theorem cell23_3860812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 2, 4].length) (baseStart_3860812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860812 prefixEnd_3860812 := by exact prefixLift 3860812
  have htrace : WordTrace (prefixWord ++ tailWord_3860812) baseStart_3860812 baseEnd_3860812 := by
    simpa [prefixWord, tailWord_3860812, baseEnd_3860812] using wordTrace_append hprefix tailTrace_3860812
  have hstable : (prefixWord ++ tailWord_3860812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860812).length < 2 ^ (prefixWord ++ tailWord_3860812).sum := by decide
  have hdescent : baseEnd_3860812 < baseStart_3860812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860835 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 6, 1, 3]
def baseStart_3860835 : Nat := 118140960795 + 3860835 * 2 ^ 59
def prefixEnd_3860835 : Nat := 4983230072969 + 3 ^ 40 * 3860835 * 2
def baseEnd_3860835 : Nat := 1982464082701507199006849

theorem tailTrace_3860835 : CollatzResearch.WordTrace tailWord_3860835 prefixEnd_3860835 1982464082701507199006849 := by
  unfold tailWord_3860835
  simp only [CollatzResearch.WordTrace]
  refine ⟨140816220967861647967335959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93877480645241098644890639 140816220967861647967335959)
  ·
    refine ⟨211224331451792471951003939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140816220967861647967335959 211224331451792471951003939)
    ·
      refine ⟨316836497177688707926505909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211224331451792471951003939 316836497177688707926505909)
      ·
        refine ⟨29703421610408316368109929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 316836497177688707926505909 29703421610408316368109929)
        ·
          refine ⟨22277566207806237276082447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29703421610408316368109929 22277566207806237276082447)
          ·
            refine ⟨33416349311709355914123671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22277566207806237276082447 33416349311709355914123671)
            ·
              refine ⟨50124523967564033871185507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33416349311709355914123671 50124523967564033871185507)
              ·
                refine ⟨75186785951346050806778261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50124523967564033871185507 75186785951346050806778261)
                ·
                  refine ⟨3524380591469346131567731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75186785951346050806778261 3524380591469346131567731)
                  ·
                    refine ⟨5286570887204019197351597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3524380591469346131567731 5286570887204019197351597)
                    ·
                      refine ⟨1982464082701507199006849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5286570887204019197351597 1982464082701507199006849)
                      ·
                        rfl

theorem cell23_3860835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_3860835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860835 prefixEnd_3860835 := by exact prefixLift 3860835
  have htrace : WordTrace (prefixWord ++ tailWord_3860835) baseStart_3860835 baseEnd_3860835 := by
    simpa [prefixWord, tailWord_3860835, baseEnd_3860835] using wordTrace_append hprefix tailTrace_3860835
  have hstable : (prefixWord ++ tailWord_3860835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860835).length < 2 ^ (prefixWord ++ tailWord_3860835).sum := by decide
  have hdescent : baseEnd_3860835 < baseStart_3860835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860853 : List Nat := [1, 3, 4, 1, 2, 2, 3, 2, 1, 2, 2]
def baseStart_3860853 : Nat := 118140960795 + 3860853 * 2 ^ 59
def prefixEnd_3860853 : Nat := 4983230072969 + 3 ^ 40 * 3860853 * 2
def baseEnd_3860853 : Nat := 1982473325353288128581767

theorem tailTrace_3860853 : CollatzResearch.WordTrace tailWord_3860853 prefixEnd_3860853 1982473325353288128581767 := by
  unfold tailWord_3860853
  simp only [CollatzResearch.WordTrace]
  refine ⟨140816877481796437041491213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93877918321197624694327475 140816877481796437041491213)
  ·
    refine ⟨52806329055673663890559205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140816877481796437041491213 52806329055673663890559205)
    ·
      refine ⟨9901186697938811979479851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52806329055673663890559205 9901186697938811979479851)
      ·
        refine ⟨14851780046908217969219777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9901186697938811979479851 14851780046908217969219777)
        ·
          refine ⟨11138835035181163476914833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14851780046908217969219777 11138835035181163476914833)
          ·
            refine ⟨8354126276385872607686125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11138835035181163476914833 8354126276385872607686125)
            ·
              refine ⟨3132797353644702227882297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8354126276385872607686125 3132797353644702227882297)
              ·
                refine ⟨2349598015233526670911723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3132797353644702227882297 2349598015233526670911723)
                ·
                  refine ⟨3524397022850290006367585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2349598015233526670911723 3524397022850290006367585)
                  ·
                    refine ⟨2643297767137717504775689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3524397022850290006367585 2643297767137717504775689)
                    ·
                      refine ⟨1982473325353288128581767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2643297767137717504775689 1982473325353288128581767)
                      ·
                        rfl

theorem cell23_3860853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_3860853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860853 prefixEnd_3860853 := by exact prefixLift 3860853
  have htrace : WordTrace (prefixWord ++ tailWord_3860853) baseStart_3860853 baseEnd_3860853 := by
    simpa [prefixWord, tailWord_3860853, baseEnd_3860853] using wordTrace_append hprefix tailTrace_3860853
  have hstable : (prefixWord ++ tailWord_3860853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860853).length < 2 ^ (prefixWord ++ tailWord_3860853).sum := by decide
  have hdescent : baseEnd_3860853 < baseStart_3860853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860868 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 1, 8]
def baseStart_3860868 : Nat := 118140960795 + 3860868 * 2 ^ 59
def prefixEnd_3860868 : Nat := 4983230072969 + 3 ^ 40 * 3860868 * 2
def baseEnd_3860868 : Nat := 660827009187701856631399

theorem tailTrace_3860868 : CollatzResearch.WordTrace tailWord_3860868 prefixEnd_3860868 660827009187701856631399 := by
  unfold tailWord_3860868
  simp only [CollatzResearch.WordTrace]
  refine ⟨70408712288371047301643629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93878283051161396402191505 70408712288371047301643629)
  ·
    refine ⟨26403267108139142738116361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70408712288371047301643629 26403267108139142738116361)
    ·
      refine ⟨19802450331104357053587271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26403267108139142738116361 19802450331104357053587271)
      ·
        refine ⟨29703675496656535580380907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19802450331104357053587271 29703675496656535580380907)
        ·
          refine ⟨44555513244984803370571361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29703675496656535580380907 44555513244984803370571361)
          ·
            refine ⟨33416634933738602527928521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44555513244984803370571361 33416634933738602527928521)
            ·
              refine ⟨25062476200303951895946391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33416634933738602527928521 25062476200303951895946391)
              ·
                refine ⟨37593714300455927843919587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25062476200303951895946391 37593714300455927843919587)
                ·
                  refine ⟨56390571450683891765879381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37593714300455927843919587 56390571450683891765879381)
                  ·
                    refine ⟨660827009187701856631399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56390571450683891765879381 660827009187701856631399)
                    ·
                      rfl

theorem cell23_3860868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_3860868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860868 prefixEnd_3860868 := by exact prefixLift 3860868
  have htrace : WordTrace (prefixWord ++ tailWord_3860868) baseStart_3860868 baseEnd_3860868 := by
    simpa [prefixWord, tailWord_3860868, baseEnd_3860868] using wordTrace_append hprefix tailTrace_3860868
  have hstable : (prefixWord ++ tailWord_3860868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860868).length < 2 ^ (prefixWord ++ tailWord_3860868).sum := by decide
  have hdescent : baseEnd_3860868 < baseStart_3860868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860925 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 1, 5, 3]
def baseStart_3860925 : Nat := 118140960795 + 3860925 * 2 ^ 59
def prefixEnd_3860925 : Nat := 4983230072969 + 3 ^ 40 * 3860925 * 2
def baseEnd_3860925 : Nat := 1982510295960411846881435

theorem tailTrace_3860925 : CollatzResearch.WordTrace tailWord_3860925 prefixEnd_3860925 1982510295960411846881435 := by
  unfold tailWord_3860925
  simp only [CollatzResearch.WordTrace]
  refine ⟨140819503537535593338112229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93879669025023728892074819 140819503537535593338112229)
  ·
    refine ⟨26403656913287923750896043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140819503537535593338112229 26403656913287923750896043)
    ·
      refine ⟨39605485369931885626344065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26403656913287923750896043 39605485369931885626344065)
      ·
        refine ⟨29704114027448914219758049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39605485369931885626344065 29704114027448914219758049)
        ·
          refine ⟨22278085520586685664818537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29704114027448914219758049 22278085520586685664818537)
          ·
            refine ⟨16708564140440014248613903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22278085520586685664818537 16708564140440014248613903)
            ·
              refine ⟨25062846210660021372920855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16708564140440014248613903 25062846210660021372920855)
              ·
                refine ⟨37594269315990032059381283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25062846210660021372920855 37594269315990032059381283)
                ·
                  refine ⟨56391403973985048089071925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37594269315990032059381283 56391403973985048089071925)
                  ·
                    refine ⟨5286694122561098258350493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56391403973985048089071925 5286694122561098258350493)
                    ·
                      refine ⟨1982510295960411846881435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5286694122561098258350493 1982510295960411846881435)
                      ·
                        rfl

theorem cell23_3860925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_3860925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860925 prefixEnd_3860925 := by exact prefixLift 3860925
  have htrace : WordTrace (prefixWord ++ tailWord_3860925) baseStart_3860925 baseEnd_3860925 := by
    simpa [prefixWord, tailWord_3860925, baseEnd_3860925] using wordTrace_append hprefix tailTrace_3860925
  have hstable : (prefixWord ++ tailWord_3860925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860925).length < 2 ^ (prefixWord ++ tailWord_3860925).sum := by decide
  have hdescent : baseEnd_3860925 < baseStart_3860925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860928 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 1, 7]
def baseStart_3860928 : Nat := 118140960795 + 3860928 * 2 ^ 59
def prefixEnd_3860928 : Nat := 4983230072969 + 3 ^ 40 * 3860928 * 2
def baseEnd_3860928 : Nat := 660837278800791778381307

theorem tailTrace_3860928 : CollatzResearch.WordTrace tailWord_3860928 prefixEnd_3860928 660837278800791778381307 := by
  unfold tailWord_3860928
  simp only [CollatzResearch.WordTrace]
  refine ⟨70409806478262362425235719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93879741971016483233647625 70409806478262362425235719)
  ·
    refine ⟨105614709717393543637853579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70409806478262362425235719 105614709717393543637853579)
    ·
      refine ⟨158422064576090315456780369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105614709717393543637853579 158422064576090315456780369)
      ·
        refine ⟨118816548432067736592585277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158422064576090315456780369 118816548432067736592585277)
        ·
          refine ⟨44556205662025401222219479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118816548432067736592585277 44556205662025401222219479)
          ·
            refine ⟨66834308493038101833329219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44556205662025401222219479 66834308493038101833329219)
            ·
              refine ⟨100251462739557152749993829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66834308493038101833329219 100251462739557152749993829)
              ·
                refine ⟨18797149263666966140623843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100251462739557152749993829 18797149263666966140623843)
                ·
                  refine ⟨28195723895500449210935765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18797149263666966140623843 28195723895500449210935765)
                  ·
                    refine ⟨660837278800791778381307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28195723895500449210935765 660837278800791778381307)
                    ·
                      rfl

theorem cell23_3860928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 1, 7].length) (baseStart_3860928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860928 prefixEnd_3860928 := by exact prefixLift 3860928
  have htrace : WordTrace (prefixWord ++ tailWord_3860928) baseStart_3860928 baseEnd_3860928 := by
    simpa [prefixWord, tailWord_3860928, baseEnd_3860928] using wordTrace_append hprefix tailTrace_3860928
  have hstable : (prefixWord ++ tailWord_3860928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860928).length < 2 ^ (prefixWord ++ tailWord_3860928).sum := by decide
  have hdescent : baseEnd_3860928 < baseStart_3860928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860932 : List Nat := [2, 3, 3, 2, 2, 1, 1, 2, 7]
def baseStart_3860932 : Nat := 118140960795 + 3860932 * 2 ^ 59
def prefixEnd_3860932 : Nat := 4983230072969 + 3 ^ 40 * 3860932 * 2
def baseEnd_3860932 : Nat := 220279321147221479943767

theorem tailTrace_3860932 : CollatzResearch.WordTrace tailWord_3860932 prefixEnd_3860932 220279321147221479943767 := by
  unfold tailWord_3860932
  simp only [CollatzResearch.WordTrace]
  refine ⟨70409879424255116766808525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93879839232340155689078033 70409879424255116766808525)
  ·
    refine ⟨26403704784095668787553197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70409879424255116766808525 26403704784095668787553197)
    ·
      refine ⟨9901389294035875795332449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26403704784095668787553197 9901389294035875795332449)
      ·
        refine ⟨7426041970526906846499337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9901389294035875795332449 7426041970526906846499337)
        ·
          refine ⟨5569531477895180134874503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7426041970526906846499337 5569531477895180134874503)
          ·
            refine ⟨8354297216842770202311755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5569531477895180134874503 8354297216842770202311755)
            ·
              refine ⟨12531445825264155303467633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8354297216842770202311755 12531445825264155303467633)
              ·
                refine ⟨9398584368948116477600725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12531445825264155303467633 9398584368948116477600725)
                ·
                  refine ⟨220279321147221479943767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9398584368948116477600725 220279321147221479943767)
                  ·
                    rfl

theorem cell23_3860932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_3860932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860932 prefixEnd_3860932 := by exact prefixLift 3860932
  have htrace : WordTrace (prefixWord ++ tailWord_3860932) baseStart_3860932 baseEnd_3860932 := by
    simpa [prefixWord, tailWord_3860932, baseEnd_3860932] using wordTrace_append hprefix tailTrace_3860932
  have hstable : (prefixWord ++ tailWord_3860932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860932).length < 2 ^ (prefixWord ++ tailWord_3860932).sum := by decide
  have hdescent : baseEnd_3860932 < baseStart_3860932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860985 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 1, 4, 3]
def baseStart_3860985 : Nat := 118140960795 + 3860985 * 2 ^ 59
def prefixEnd_3860985 : Nat := 4983230072969 + 3 ^ 40 * 3860985 * 2
def baseEnd_3860985 : Nat := 1982541104799681612131159

theorem tailTrace_3860985 : CollatzResearch.WordTrace tailWord_3860985 prefixEnd_3860985 1982541104799681612131159 := by
  unfold tailWord_3860985
  simp only [CollatzResearch.WordTrace]
  refine ⟨140821691917318223585296409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93881127944878815723530939 140821691917318223585296409)
  ·
    refine ⟨105616268937988667688972307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140821691917318223585296409 105616268937988667688972307)
    ·
      refine ⟨158424403406983001533458461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105616268937988667688972307 158424403406983001533458461)
      ·
        refine ⟨59409151277618625575046923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158424403406983001533458461 59409151277618625575046923)
        ·
          refine ⟨89113726916427938362570385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59409151277618625575046923 89113726916427938362570385)
          ·
            refine ⟨66835295187320953771927789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89113726916427938362570385 66835295187320953771927789)
            ·
              refine ⟨25063235695245357664472921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66835295187320953771927789 25063235695245357664472921)
              ·
                refine ⟨18797426771434018248354691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25063235695245357664472921 18797426771434018248354691)
                ·
                  refine ⟨28196140157151027372532037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18797426771434018248354691 28196140157151027372532037)
                  ·
                    refine ⟨5286776279465817632349757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28196140157151027372532037 5286776279465817632349757)
                    ·
                      refine ⟨1982541104799681612131159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5286776279465817632349757 1982541104799681612131159)
                      ·
                        rfl

theorem cell23_3860985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_3860985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860985 prefixEnd_3860985 := by exact prefixLift 3860985
  have htrace : WordTrace (prefixWord ++ tailWord_3860985) baseStart_3860985 baseEnd_3860985 := by
    simpa [prefixWord, tailWord_3860985, baseEnd_3860985] using wordTrace_append hprefix tailTrace_3860985
  have hstable : (prefixWord ++ tailWord_3860985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860985).length < 2 ^ (prefixWord ++ tailWord_3860985).sum := by decide
  have hdescent : baseEnd_3860985 < baseStart_3860985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861002 : List Nat := [3, 1, 2, 2, 2, 1, 2, 3, 2, 2, 3]
def baseStart_3861002 : Nat := 118140960795 + 3861002 * 2 ^ 59
def prefixEnd_3861002 : Nat := 4983230072969 + 3 ^ 40 * 3861002 * 2
def baseEnd_3861002 : Nat := 1982549833970808045618581

theorem tailTrace_3861002 : CollatzResearch.WordTrace tailWord_3861002 prefixEnd_3861002 1982549833970808045618581 := by
  unfold tailWord_3861002
  simp only [CollatzResearch.WordTrace]
  refine ⟨35205577989564158872166315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93881541305504423659110173 35205577989564158872166315)
  ·
    refine ⟨52808366984346238308249473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35205577989564158872166315 52808366984346238308249473)
    ·
      refine ⟨39606275238259678731187105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52808366984346238308249473 39606275238259678731187105)
      ·
        refine ⟨29704706428694759048390329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39606275238259678731187105 29704706428694759048390329)
        ·
          refine ⟨22278529821521069286292747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29704706428694759048390329 22278529821521069286292747)
          ·
            refine ⟨33417794732281603929439121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22278529821521069286292747 33417794732281603929439121)
            ·
              refine ⟨25063346049211202947079341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33417794732281603929439121 25063346049211202947079341)
              ·
                refine ⟨9398754768454201105154753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25063346049211202947079341 9398754768454201105154753)
                ·
                  refine ⟨7049066076340650828866065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9398754768454201105154753 7049066076340650828866065)
                  ·
                    refine ⟨5286799557255488121649549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7049066076340650828866065 5286799557255488121649549)
                    ·
                      refine ⟨1982549833970808045618581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5286799557255488121649549 1982549833970808045618581)
                      ·
                        rfl

theorem cell23_3861002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_3861002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861002 prefixEnd_3861002 := by exact prefixLift 3861002
  have htrace : WordTrace (prefixWord ++ tailWord_3861002) baseStart_3861002 baseEnd_3861002 := by
    simpa [prefixWord, tailWord_3861002, baseEnd_3861002] using wordTrace_append hprefix tailTrace_3861002
  have hstable : (prefixWord ++ tailWord_3861002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861002).length < 2 ^ (prefixWord ++ tailWord_3861002).sum := by decide
  have hdescent : baseEnd_3861002 < baseStart_3861002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861042 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2]
def baseStart_3861042 : Nat := 118140960795 + 3861042 * 2 ^ 59
def prefixEnd_3861042 : Nat := 4983230072969 + 3 ^ 40 * 3861042 * 2
def baseEnd_3861042 : Nat := 1982570373196987889118397

theorem tailTrace_3861042 : CollatzResearch.WordTrace tailWord_3861042 prefixEnd_3861042 1982570373196987889118397 := by
  unfold tailWord_3861042
  simp only [CollatzResearch.WordTrace]
  refine ⟨35205942719527930580030345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93882513918741148213414253 35205942719527930580030345)
  ·
    refine ⟨26404457039645947935022759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35205942719527930580030345 26404457039645947935022759)
    ·
      refine ⟨39606685559468921902534139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26404457039645947935022759 39606685559468921902534139)
      ·
        refine ⟨59410028339203382853801209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39606685559468921902534139 59410028339203382853801209)
        ·
          refine ⟨44557521254402537140350907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59410028339203382853801209 44557521254402537140350907)
          ·
            refine ⟨66836281881603805710526361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44557521254402537140350907 66836281881603805710526361)
            ·
              refine ⟨50127211411202854282894771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66836281881603805710526361 50127211411202854282894771)
              ·
                refine ⟨75190817116804281424342157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50127211411202854282894771 75190817116804281424342157)
                ·
                  refine ⟨28196556418801605534128309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75190817116804281424342157 28196556418801605534128309)
                  ·
                    refine ⟨2643427164262650518824529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28196556418801605534128309 2643427164262650518824529)
                    ·
                      refine ⟨1982570373196987889118397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2643427164262650518824529 1982570373196987889118397)
                      ·
                        rfl

theorem cell23_3861042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2].length) (baseStart_3861042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861042 prefixEnd_3861042 := by exact prefixLift 3861042
  have htrace : WordTrace (prefixWord ++ tailWord_3861042) baseStart_3861042 baseEnd_3861042 := by
    simpa [prefixWord, tailWord_3861042, baseEnd_3861042] using wordTrace_append hprefix tailTrace_3861042
  have hstable : (prefixWord ++ tailWord_3861042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861042).length < 2 ^ (prefixWord ++ tailWord_3861042).sum := by decide
  have hdescent : baseEnd_3861042 < baseStart_3861042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861052 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 3, 5]
def baseStart_3861052 : Nat := 118140960795 + 3861052 * 2 ^ 59
def prefixEnd_3861052 : Nat := 4983230072969 + 3 ^ 40 * 3861052 * 2
def baseEnd_3861052 : Nat := 660858502667844283331117

theorem tailTrace_3861052 : CollatzResearch.WordTrace tailWord_3861052 prefixEnd_3861052 660858502667844283331117 := by
  unfold tailWord_3861052
  simp only [CollatzResearch.WordTrace]
  refine ⟨70412067804037747013992705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93882757072050329351990273 70412067804037747013992705)
  ·
    refine ⟨52809050853028310260494529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70412067804037747013992705 52809050853028310260494529)
    ·
      refine ⟨39606788139771232695370897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52809050853028310260494529 39606788139771232695370897)
      ·
        refine ⟨29705091104828424521528173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39606788139771232695370897 29705091104828424521528173)
        ·
          refine ⟨11139409164310659195573065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29705091104828424521528173 11139409164310659195573065)
          ·
            refine ⟨8354556873232994396679799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11139409164310659195573065 8354556873232994396679799)
            ·
              refine ⟨12531835309849491595019699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8354556873232994396679799 12531835309849491595019699)
              ·
                refine ⟨18797752964774237392529549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12531835309849491595019699 18797752964774237392529549)
                ·
                  refine ⟨7049157361790339022198581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18797752964774237392529549 7049157361790339022198581)
                  ·
                    refine ⟨660858502667844283331117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7049157361790339022198581 660858502667844283331117)
                    ·
                      rfl

theorem cell23_3861052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_3861052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861052 prefixEnd_3861052 := by exact prefixLift 3861052
  have htrace : WordTrace (prefixWord ++ tailWord_3861052) baseStart_3861052 baseEnd_3861052 := by
    simpa [prefixWord, tailWord_3861052, baseEnd_3861052] using wordTrace_append hprefix tailTrace_3861052
  have hstable : (prefixWord ++ tailWord_3861052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861052).length < 2 ^ (prefixWord ++ tailWord_3861052).sum := by decide
  have hdescent : baseEnd_3861052 < baseStart_3861052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861092 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3]
def baseStart_3861092 : Nat := 118140960795 + 3861092 * 2 ^ 59
def prefixEnd_3861092 : Nat := 4983230072969 + 3 ^ 40 * 3861092 * 2
def baseEnd_3861092 : Nat := 1982596047229712693493167

theorem tailTrace_3861092 : CollatzResearch.WordTrace tailWord_3861092 prefixEnd_3861092 1982596047229712693493167 := by
  unfold tailWord_3861092
  simp only [CollatzResearch.WordTrace]
  refine ⟨70412797263965290429720765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93883729685287053906294353 70412797263965290429720765)
  ·
    refine ⟨26404798973986983911145287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70412797263965290429720765 26404798973986983911145287)
    ·
      refine ⟨39607198460980475866717931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26404798973986983911145287 39607198460980475866717931)
      ·
        refine ⟨59410797691470713800076897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39607198460980475866717931 59410797691470713800076897)
        ·
          refine ⟨44558098268603035350057673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59410797691470713800076897 44558098268603035350057673)
          ·
            refine ⟨33418573701452276512543255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44558098268603035350057673 33418573701452276512543255)
            ·
              refine ⟨50127860552178414768814883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33418573701452276512543255 50127860552178414768814883)
              ·
                refine ⟨75191790828267622153222325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50127860552178414768814883 75191790828267622153222325)
                ·
                  refine ⟨7049230390150089576864593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75191790828267622153222325 7049230390150089576864593)
                  ·
                    refine ⟨5286922792612567182648445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7049230390150089576864593 5286922792612567182648445)
                    ·
                      refine ⟨1982596047229712693493167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5286922792612567182648445 1982596047229712693493167)
                      ·
                        rfl

theorem cell23_3861092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_3861092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861092 prefixEnd_3861092 := by exact prefixLift 3861092
  have htrace : WordTrace (prefixWord ++ tailWord_3861092) baseStart_3861092 baseEnd_3861092 := by
    simpa [prefixWord, tailWord_3861092, baseEnd_3861092] using wordTrace_append hprefix tailTrace_3861092
  have hstable : (prefixWord ++ tailWord_3861092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861092).length < 2 ^ (prefixWord ++ tailWord_3861092).sum := by decide
  have hdescent : baseEnd_3861092 < baseStart_3861092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861110 : List Nat := [5, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2]
def baseStart_3861110 : Nat := 118140960795 + 3861110 * 2 ^ 59
def prefixEnd_3861110 : Nat := 4983230072969 + 3 ^ 40 * 3861110 * 2
def baseEnd_3861110 : Nat := 1982605289881493623068085

theorem tailTrace_3861110 : CollatzResearch.WordTrace tailWord_3861110 prefixEnd_3861110 1982605289881493623068085 := by
  unfold tailWord_3861110
  simp only [CollatzResearch.WordTrace]
  refine ⟨8801640690116585620849799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93884167361243579955731189 8801640690116585620849799)
  ·
    refine ⟨13202461035174878431274699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8801640690116585620849799 13202461035174878431274699)
    ·
      refine ⟨19803691552762317646912049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13202461035174878431274699 19803691552762317646912049)
      ·
        refine ⟨14852768664571738235184037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19803691552762317646912049 14852768664571738235184037)
        ·
          refine ⟨2784894124607200919097007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14852768664571738235184037 2784894124607200919097007)
          ·
            refine ⟨4177341186910801378645511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2784894124607200919097007 4177341186910801378645511)
            ·
              refine ⟨6266011780366202067968267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4177341186910801378645511 6266011780366202067968267)
              ·
                refine ⟨9399017670549303101952401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6266011780366202067968267 9399017670549303101952401)
                ·
                  refine ⟨7049263252911977326464301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9399017670549303101952401 7049263252911977326464301)
                  ·
                    refine ⟨2643473719841991497424113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7049263252911977326464301 2643473719841991497424113)
                    ·
                      refine ⟨1982605289881493623068085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2643473719841991497424113 1982605289881493623068085)
                      ·
                        rfl

theorem cell23_3861110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_3861110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861110 prefixEnd_3861110 := by exact prefixLift 3861110
  have htrace : WordTrace (prefixWord ++ tailWord_3861110) baseStart_3861110 baseEnd_3861110 := by
    simpa [prefixWord, tailWord_3861110, baseEnd_3861110] using wordTrace_append hprefix tailTrace_3861110
  have hstable : (prefixWord ++ tailWord_3861110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861110).length < 2 ^ (prefixWord ++ tailWord_3861110).sum := by decide
  have hdescent : baseEnd_3861110 < baseStart_3861110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861135 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 5]
def baseStart_3861135 : Nat := 118140960795 + 3861135 * 2 ^ 59
def prefixEnd_3861135 : Nat := 4983230072969 + 3 ^ 40 * 3861135 * 2
def baseEnd_3861135 : Nat := 1982618126897856025255469

theorem tailTrace_3861135 : CollatzResearch.WordTrace tailWord_3861135 prefixEnd_3861135 1982618126897856025255469 := by
  unfold tailWord_3861135
  simp only [CollatzResearch.WordTrace]
  refine ⟨140827162866774799203256859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93884775244516532802171239 140827162866774799203256859)
  ·
    refine ⟨211240744300162198804885289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140827162866774799203256859 211240744300162198804885289)
    ·
      refine ⟨158430558225121649103663967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211240744300162198804885289 158430558225121649103663967)
      ·
        refine ⟨237645837337682473655495951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158430558225121649103663967 237645837337682473655495951)
        ·
          refine ⟨356468756006523710483243927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237645837337682473655495951 356468756006523710483243927)
          ·
            refine ⟨534703134009785565724865891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356468756006523710483243927 534703134009785565724865891)
            ·
              refine ⟨802054701014678348587298837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534703134009785565724865891 802054701014678348587298837)
              ·
                refine ⟨37596314110063047590029633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 802054701014678348587298837 37596314110063047590029633)
                ·
                  refine ⟨28197235582547285692522225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37596314110063047590029633 28197235582547285692522225)
                  ·
                    refine ⟨21147926686910464269391669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28197235582547285692522225 21147926686910464269391669)
                    ·
                      refine ⟨1982618126897856025255469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21147926686910464269391669 1982618126897856025255469)
                      ·
                        rfl

theorem cell23_3861135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_3861135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861135 prefixEnd_3861135 := by exact prefixLift 3861135
  have htrace : WordTrace (prefixWord ++ tailWord_3861135) baseStart_3861135 baseEnd_3861135 := by
    simpa [prefixWord, tailWord_3861135, baseEnd_3861135] using wordTrace_append hprefix tailTrace_3861135
  have hstable : (prefixWord ++ tailWord_3861135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861135).length < 2 ^ (prefixWord ++ tailWord_3861135).sum := by decide
  have hdescent : baseEnd_3861135 < baseStart_3861135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861140 : List Nat := [2, 4, 2, 2, 1, 1, 2, 4, 1, 2, 2]
def baseStart_3861140 : Nat := 118140960795 + 3861140 * 2 ^ 59
def prefixEnd_3861140 : Nat := 4983230072969 + 3 ^ 40 * 3861140 * 2
def baseEnd_3861140 : Nat := 1982620694301128505692947

theorem tailTrace_3861140 : CollatzResearch.WordTrace tailWord_3861140 prefixEnd_3861140 1982620694301128505692947 := by
  unfold tailWord_3861140
  simp only [CollatzResearch.WordTrace]
  refine ⟨70413672615878342528594437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93884896821171123371459249 70413672615878342528594437)
  ·
    refine ⟨13202563615477189224111457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70413672615878342528594437 13202563615477189224111457)
    ·
      refine ⟨9901922711607891918083593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13202563615477189224111457 9901922711607891918083593)
      ·
        refine ⟨7426442033705918938562695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9901922711607891918083593 7426442033705918938562695)
        ·
          refine ⟨11139663050558878407844043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7426442033705918938562695 11139663050558878407844043)
          ·
            refine ⟨16709494575838317611766065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11139663050558878407844043 16709494575838317611766065)
            ·
              refine ⟨12532120931878738208824549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16709494575838317611766065 12532120931878738208824549)
              ·
                refine ⟨2349772674727263414154603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12532120931878738208824549 2349772674727263414154603)
                ·
                  refine ⟨3524659012090895121231905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2349772674727263414154603 3524659012090895121231905)
                  ·
                    refine ⟨2643494259068171340923929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3524659012090895121231905 2643494259068171340923929)
                    ·
                      refine ⟨1982620694301128505692947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2643494259068171340923929 1982620694301128505692947)
                      ·
                        rfl

theorem cell23_3861140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_3861140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861140 prefixEnd_3861140 := by exact prefixLift 3861140
  have htrace : WordTrace (prefixWord ++ tailWord_3861140) baseStart_3861140 baseEnd_3861140 := by
    simpa [prefixWord, tailWord_3861140, baseEnd_3861140] using wordTrace_append hprefix tailTrace_3861140
  have hstable : (prefixWord ++ tailWord_3861140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861140).length < 2 ^ (prefixWord ++ tailWord_3861140).sum := by decide
  have hdescent : baseEnd_3861140 < baseStart_3861140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861149 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 5, 3, 2]
def baseStart_3861149 : Nat := 118140960795 + 3861149 * 2 ^ 59
def prefixEnd_3861149 : Nat := 4983230072969 + 3 ^ 40 * 3861149 * 2
def baseEnd_3861149 : Nat := 1982625315627018970480405

theorem tailTrace_3861149 : CollatzResearch.WordTrace tailWord_3861149 prefixEnd_3861149 1982625315627018970480405 := by
  unfold tailWord_3861149
  simp only [CollatzResearch.WordTrace]
  refine ⟨140827673488724079594266501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93885115659149386396177667 140827673488724079594266501)
  ·
    refine ⟨26405188779135764923924969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140827673488724079594266501 26405188779135764923924969)
    ·
      refine ⟨19803891584351823692943727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26405188779135764923924969 19803891584351823692943727)
      ·
        refine ⟨29705837376527735539415591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19803891584351823692943727 29705837376527735539415591)
        ·
          refine ⟨44558756064791603309123387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29705837376527735539415591 44558756064791603309123387)
          ·
            refine ⟨66838134097187404963685081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44558756064791603309123387 66838134097187404963685081)
            ·
              refine ⟨50128600572890553722763811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66838134097187404963685081 50128600572890553722763811)
              ·
                refine ⟨75192900859335830584145717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50128600572890553722763811 75192900859335830584145717)
                ·
                  refine ⟨7049334455562734117263661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75192900859335830584145717 7049334455562734117263661)
                  ·
                    refine ⟨2643500420836025293973873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7049334455562734117263661 2643500420836025293973873)
                    ·
                      refine ⟨1982625315627018970480405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2643500420836025293973873 1982625315627018970480405)
                      ·
                        rfl

theorem cell23_3861149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_3861149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861149 prefixEnd_3861149 := by exact prefixLift 3861149
  have htrace : WordTrace (prefixWord ++ tailWord_3861149) baseStart_3861149 baseEnd_3861149 := by
    simpa [prefixWord, tailWord_3861149, baseEnd_3861149] using wordTrace_append hprefix tailTrace_3861149
  have hstable : (prefixWord ++ tailWord_3861149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861149).length < 2 ^ (prefixWord ++ tailWord_3861149).sum := by decide
  have hdescent : baseEnd_3861149 < baseStart_3861149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861155 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 1, 8]
def baseStart_3861155 : Nat := 118140960795 + 3861155 * 2 ^ 59
def prefixEnd_3861155 : Nat := 4983230072969 + 3 ^ 40 * 3861155 * 2
def baseEnd_3861155 : Nat := 660876132170315315668459

theorem tailTrace_3861155 : CollatzResearch.WordTrace tailWord_3861155 prefixEnd_3861155 660876132170315315668459 := by
  unfold tailWord_3861155
  simp only [CollatzResearch.WordTrace]
  refine ⟨140827892326702342618984919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93885261551134895079323279 140827892326702342618984919)
  ·
    refine ⟨211241838490053513928477379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140827892326702342618984919 211241838490053513928477379)
    ·
      refine ⟨316862757735080270892716069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211241838490053513928477379 316862757735080270892716069)
      ·
        refine ⟨59411767075327550792384263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 316862757735080270892716069 59411767075327550792384263)
        ·
          refine ⟨89117650612991326188576395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59411767075327550792384263 89117650612991326188576395)
          ·
            refine ⟨133676475919486989282864593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89117650612991326188576395 133676475919486989282864593)
            ·
              refine ⟨100257356939615241962148445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133676475919486989282864593 100257356939615241962148445)
              ·
                refine ⟨37596508852355715735805667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100257356939615241962148445 37596508852355715735805667)
                ·
                  refine ⟨56394763278533573603708501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37596508852355715735805667 56394763278533573603708501)
                  ·
                    refine ⟨660876132170315315668459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56394763278533573603708501 660876132170315315668459)
                    ·
                      rfl

theorem cell23_3861155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 8].length) (baseStart_3861155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861155 prefixEnd_3861155 := by exact prefixLift 3861155
  have htrace : WordTrace (prefixWord ++ tailWord_3861155) baseStart_3861155 baseEnd_3861155 := by
    simpa [prefixWord, tailWord_3861155, baseEnd_3861155] using wordTrace_append hprefix tailTrace_3861155
  have hstable : (prefixWord ++ tailWord_3861155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861155).length < 2 ^ (prefixWord ++ tailWord_3861155).sum := by decide
  have hdescent : baseEnd_3861155 < baseStart_3861155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861174 : List Nat := [5, 1, 3, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_3861174 : Nat := 118140960795 + 3861174 * 2 ^ 59
def prefixEnd_3861174 : Nat := 4983230072969 + 3 ^ 40 * 3861174 * 2
def baseEnd_3861174 : Nat := 1982638152643381372667791

theorem tailTrace_3861174 : CollatzResearch.WordTrace tailWord_3861174 prefixEnd_3861174 1982638152643381372667791 := by
  unfold tailWord_3861174
  simp only [CollatzResearch.WordTrace]
  refine ⟨8801786582102094303995411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93885723542422339242617717 8801786582102094303995411)
  ·
    refine ⟨13202679873153141455993117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8801786582102094303995411 13202679873153141455993117)
    ·
      refine ⟨4951004952432428045997419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13202679873153141455993117 4951004952432428045997419)
      ·
        refine ⟨7426507428648642068996129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4951004952432428045997419 7426507428648642068996129)
        ·
          refine ⟨5569880571486481551747097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7426507428648642068996129 5569880571486481551747097)
          ·
            refine ⟨4177410428614861163810323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5569880571486481551747097 4177410428614861163810323)
            ·
              refine ⟨6266115642922291745715485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4177410428614861163810323 6266115642922291745715485)
              ·
                refine ⟨2349793366095859404643307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6266115642922291745715485 2349793366095859404643307)
                ·
                  refine ⟨3524690049143789106964961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2349793366095859404643307 3524690049143789106964961)
                  ·
                    refine ⟨2643517536857841830223721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3524690049143789106964961 2643517536857841830223721)
                    ·
                      refine ⟨1982638152643381372667791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2643517536857841830223721 1982638152643381372667791)
                      ·
                        rfl

theorem cell23_3861174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_3861174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861174 prefixEnd_3861174 := by exact prefixLift 3861174
  have htrace : WordTrace (prefixWord ++ tailWord_3861174) baseStart_3861174 baseEnd_3861174 := by
    simpa [prefixWord, tailWord_3861174, baseEnd_3861174] using wordTrace_append hprefix tailTrace_3861174
  have hstable : (prefixWord ++ tailWord_3861174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861174).length < 2 ^ (prefixWord ++ tailWord_3861174).sum := by decide
  have hdescent : baseEnd_3861174 < baseStart_3861174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861242 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5]
def baseStart_3861242 : Nat := 118140960795 + 3861242 * 2 ^ 59
def prefixEnd_3861242 : Nat := 4983230072969 + 3 ^ 40 * 3861242 * 2
def baseEnd_3861242 : Nat := 1982673069327887106617477

theorem tailTrace_3861242 : CollatzResearch.WordTrace tailWord_3861242 prefixEnd_3861242 1982673069327887106617477 := by
  unfold tailWord_3861242
  simp only [CollatzResearch.WordTrace]
  refine ⟨35207766369346789119350495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93887376984924770984934653 35207766369346789119350495)
  ·
    refine ⟨52811649554020183679025743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35207766369346789119350495 52811649554020183679025743)
    ·
      refine ⟨79217474331030275518538615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52811649554020183679025743 79217474331030275518538615)
      ·
        refine ⟨118826211496545413277807923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79217474331030275518538615 118826211496545413277807923)
        ·
          refine ⟨178239317244818119916711885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118826211496545413277807923 178239317244818119916711885)
          ·
            refine ⟨66839743966806794968766957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178239317244818119916711885 66839743966806794968766957)
            ·
              refine ⟨25064903987552548113287609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66839743966806794968766957 25064903987552548113287609)
              ·
                refine ⟨18798677990664411084965707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25064903987552548113287609 18798677990664411084965707)
                ·
                  refine ⟨28198016985996616627448561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18798677990664411084965707 28198016985996616627448561)
                  ·
                    refine ⟨21148512739497462470586421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28198016985996616627448561 21148512739497462470586421)
                    ·
                      refine ⟨1982673069327887106617477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21148512739497462470586421 1982673069327887106617477)
                      ·
                        rfl

theorem cell23_3861242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_3861242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861242 prefixEnd_3861242 := by exact prefixLift 3861242
  have htrace : WordTrace (prefixWord ++ tailWord_3861242) baseStart_3861242 baseEnd_3861242 := by
    simpa [prefixWord, tailWord_3861242, baseEnd_3861242] using wordTrace_append hprefix tailTrace_3861242
  have hstable : (prefixWord ++ tailWord_3861242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861242).length < 2 ^ (prefixWord ++ tailWord_3861242).sum := by decide
  have hdescent : baseEnd_3861242 < baseStart_3861242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861262 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 2, 8]
def baseStart_3861262 : Nat := 118140960795 + 3861262 * 2 ^ 59
def prefixEnd_3861262 : Nat := 4983230072969 + 3 ^ 40 * 3861262 * 2
def baseEnd_3861262 : Nat := 660894446313659009455795

theorem tailTrace_3861262 : CollatzResearch.WordTrace tailWord_3861262 prefixEnd_3861262 660894446313659009455795 := by
  unfold tailWord_3861262
  simp only [CollatzResearch.WordTrace]
  refine ⟨17603974367164337486641255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93887863291543133262086693 17603974367164337486641255)
  ·
    refine ⟨26405961550746506229961883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17603974367164337486641255 26405961550746506229961883)
    ·
      refine ⟨39608942326119759344942825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26405961550746506229961883 39608942326119759344942825)
      ·
        refine ⟨29706706744589819508707119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39608942326119759344942825 29706706744589819508707119)
        ·
          refine ⟨44560060116884729263060679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29706706744589819508707119 44560060116884729263060679)
          ·
            refine ⟨66840090175327093894591019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44560060116884729263060679 66840090175327093894591019)
            ·
              refine ⟨100260135262990640841886529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66840090175327093894591019 100260135262990640841886529)
              ·
                refine ⟨75195101447242980631414897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100260135262990640841886529 75195101447242980631414897)
                ·
                  refine ⟨56396326085432235473561173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75195101447242980631414897 56396326085432235473561173)
                  ·
                    refine ⟨660894446313659009455795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56396326085432235473561173 660894446313659009455795)
                    ·
                      rfl

theorem cell23_3861262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_3861262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861262 prefixEnd_3861262 := by exact prefixLift 3861262
  have htrace : WordTrace (prefixWord ++ tailWord_3861262) baseStart_3861262 baseEnd_3861262 := by
    simpa [prefixWord, tailWord_3861262, baseEnd_3861262] using wordTrace_append hprefix tailTrace_3861262
  have hstable : (prefixWord ++ tailWord_3861262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861262).length < 2 ^ (prefixWord ++ tailWord_3861262).sum := by decide
  have hdescent : baseEnd_3861262 < baseStart_3861262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861279 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 5, 4]
def baseStart_3861279 : Nat := 118140960795 + 3861279 * 2 ^ 59
def prefixEnd_3861279 : Nat := 4983230072969 + 3 ^ 40 * 3861279 * 2
def baseEnd_3861279 : Nat := 660897356037367820618269

theorem tailTrace_3861279 : CollatzResearch.WordTrace tailWord_3861279 prefixEnd_3861279 660897356037367820618269 := by
  unfold tailWord_3861279
  simp only [CollatzResearch.WordTrace]
  refine ⟨140832414978253111796498891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93888276652168741197665927 140832414978253111796498891)
  ·
    refine ⟨211248622467379667694748337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140832414978253111796498891 211248622467379667694748337)
    ·
      refine ⟨158436466850534750771061253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211248622467379667694748337 158436466850534750771061253)
      ·
        refine ⟨29706837534475265769573985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158436466850534750771061253 29706837534475265769573985)
        ·
          refine ⟨22280128150856449327180489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29706837534475265769573985 22280128150856449327180489)
          ·
            refine ⟨16710096113142336995385367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22280128150856449327180489 16710096113142336995385367)
            ·
              refine ⟨25065144169713505493078051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16710096113142336995385367 25065144169713505493078051)
              ·
                refine ⟨37597716254570258239617077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25065144169713505493078051 37597716254570258239617077)
                ·
                  refine ⟨3524785898865961709964101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37597716254570258239617077 3524785898865961709964101)
                  ·
                    refine ⟨660897356037367820618269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3524785898865961709964101 660897356037367820618269)
                    ·
                      rfl

theorem cell23_3861279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 4].length) (baseStart_3861279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861279 prefixEnd_3861279 := by exact prefixLift 3861279
  have htrace : WordTrace (prefixWord ++ tailWord_3861279) baseStart_3861279 baseEnd_3861279 := by
    simpa [prefixWord, tailWord_3861279, baseEnd_3861279] using wordTrace_append hprefix tailTrace_3861279
  have hstable : (prefixWord ++ tailWord_3861279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861279).length < 2 ^ (prefixWord ++ tailWord_3861279).sum := by decide
  have hdescent : baseEnd_3861279 < baseStart_3861279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861292 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 8]
def baseStart_3861292 : Nat := 118140960795 + 3861292 * 2 ^ 59
def prefixEnd_3861292 : Nat := 4983230072969 + 3 ^ 40 * 3861292 * 2
def baseEnd_3861292 : Nat := 220299860373401323443583

theorem tailTrace_3861292 : CollatzResearch.WordTrace tailWord_3861292 prefixEnd_3861292 220299860373401323443583 := by
  unfold tailWord_3861292
  simp only [CollatzResearch.WordTrace]
  refine ⟨70416444563603007508361065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93888592751470676677814753 70416444563603007508361065)
  ·
    refine ⟨52812333422702255631270799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70416444563603007508361065 52812333422702255631270799)
    ·
      refine ⟨79218500134053383446906199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52812333422702255631270799 79218500134053383446906199)
      ·
        refine ⟨118827750201080075170359299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79218500134053383446906199 118827750201080075170359299)
        ·
          refine ⟨178241625301620112755538949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118827750201080075170359299 178241625301620112755538949)
          ·
            refine ⟨33420304744053771141663553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178241625301620112755538949 33420304744053771141663553)
            ·
              refine ⟨25065228558040328356247665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33420304744053771141663553 25065228558040328356247665)
              ·
                refine ⟨18798921418530246267185749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25065228558040328356247665 18798921418530246267185749)
                ·
                  refine ⟨220299860373401323443583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18798921418530246267185749 220299860373401323443583)
                  ·
                    rfl

theorem cell23_3861292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 8].length) (baseStart_3861292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861292 prefixEnd_3861292 := by exact prefixLift 3861292
  have htrace : WordTrace (prefixWord ++ tailWord_3861292) baseStart_3861292 baseEnd_3861292 := by
    simpa [prefixWord, tailWord_3861292, baseEnd_3861292] using wordTrace_append hprefix tailTrace_3861292
  have hstable : (prefixWord ++ tailWord_3861292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861292).length < 2 ^ (prefixWord ++ tailWord_3861292).sum := by decide
  have hdescent : baseEnd_3861292 < baseStart_3861292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861322 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 2, 9]
def baseStart_3861322 : Nat := 118140960795 + 3861322 * 2 ^ 59
def prefixEnd_3861322 : Nat := 4983230072969 + 3 ^ 40 * 3861322 * 2
def baseEnd_3861322 : Nat := 660904715926748931205703

theorem tailTrace_3861322 : CollatzResearch.WordTrace tailWord_3861322 prefixEnd_3861322 660904715926748931205703 := by
  unfold tailWord_3861322
  simp only [CollatzResearch.WordTrace]
  refine ⟨35208495829274332535078555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93889322211398220093542813 35208495829274332535078555)
  ·
    refine ⟨52812743743911498802617833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35208495829274332535078555 52812743743911498802617833)
    ·
      refine ⟨39609557807933624101963375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52812743743911498802617833 39609557807933624101963375)
      ·
        refine ⟨59414336711900436152945063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39609557807933624101963375 59414336711900436152945063)
        ·
          refine ⟨89121505067850654229417595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59414336711900436152945063 89121505067850654229417595)
          ·
            refine ⟨133682257601775981344126393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89121505067850654229417595 133682257601775981344126393)
            ·
              refine ⟨100261693201331986008094795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133682257601775981344126393 100261693201331986008094795)
              ·
                refine ⟨150392539801997979012142193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100261693201331986008094795 150392539801997979012142193)
                ·
                  refine ⟨112794404851498484259106645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150392539801997979012142193 112794404851498484259106645)
                  ·
                    refine ⟨660904715926748931205703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 112794404851498484259106645 660904715926748931205703)
                    ·
                      rfl

theorem cell23_3861322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_3861322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861322 prefixEnd_3861322 := by exact prefixLift 3861322
  have htrace : WordTrace (prefixWord ++ tailWord_3861322) baseStart_3861322 baseEnd_3861322 := by
    simpa [prefixWord, tailWord_3861322, baseEnd_3861322] using wordTrace_append hprefix tailTrace_3861322
  have hstable : (prefixWord ++ tailWord_3861322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861322).length < 2 ^ (prefixWord ++ tailWord_3861322).sum := by decide
  have hdescent : baseEnd_3861322 < baseStart_3861322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861379 : List Nat := [1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 5]
def baseStart_3861379 : Nat := 118140960795 + 3861379 * 2 ^ 59
def prefixEnd_3861379 : Nat := 4983230072969 + 3 ^ 40 * 3861379 * 2
def baseEnd_3861379 : Nat := 1982743416177553070604347

theorem tailTrace_3861379 : CollatzResearch.WordTrace tailWord_3861379 prefixEnd_3861379 1982743416177553070604347 := by
  unfold tailWord_3861379
  simp only [CollatzResearch.WordTrace]
  refine ⟨140836062277890828875139191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93890708185260552583426127 140836062277890828875139191)
  ·
    refine ⟨211254093416836243312708787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140836062277890828875139191 211254093416836243312708787)
    ·
      refine ⟨316881140125254364969063181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211254093416836243312708787 316881140125254364969063181)
      ·
        refine ⟨118830427546970386863398693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316881140125254364969063181 118830427546970386863398693)
        ·
          refine ⟨22280705165056947536887255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118830427546970386863398693 22280705165056947536887255)
          ·
            refine ⟨33421057747585421305330883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22280705165056947536887255 33421057747585421305330883)
            ·
              refine ⟨50131586621378131957996325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33421057747585421305330883 50131586621378131957996325)
              ·
                refine ⟨9399672491508399742124311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50131586621378131957996325 9399672491508399742124311)
                ·
                  refine ⟨14099508737262599613186467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9399672491508399742124311 14099508737262599613186467)
                  ·
                    refine ⟨21149263105893899419779701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14099508737262599613186467 21149263105893899419779701)
                    ·
                      refine ⟨1982743416177553070604347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21149263105893899419779701 1982743416177553070604347)
                      ·
                        rfl

theorem cell23_3861379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_3861379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861379 prefixEnd_3861379 := by exact prefixLift 3861379
  have htrace : WordTrace (prefixWord ++ tailWord_3861379) baseStart_3861379 baseEnd_3861379 := by
    simpa [prefixWord, tailWord_3861379, baseEnd_3861379] using wordTrace_append hprefix tailTrace_3861379
  have hstable : (prefixWord ++ tailWord_3861379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861379).length < 2 ^ (prefixWord ++ tailWord_3861379).sum := by decide
  have hdescent : baseEnd_3861379 < baseStart_3861379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861410 : List Nat := [3, 3, 1, 2, 2, 2, 3, 1, 1, 1, 4]
def baseStart_3861410 : Nat := 118140960795 + 3861410 * 2 ^ 59
def prefixEnd_3861410 : Nat := 4983230072969 + 3 ^ 40 * 3861410 * 2
def baseEnd_3861410 : Nat := 1982759334077842449316705

theorem tailTrace_3861410 : CollatzResearch.WordTrace tailWord_3861410 prefixEnd_3861410 1982759334077842449316705 := by
  unfold tailWord_3861410
  simp only [CollatzResearch.WordTrace]
  refine ⟨35209298235194630292379421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93891461960519014113011789 35209298235194630292379421)
  ·
    refine ⟨13203486838197986359642283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35209298235194630292379421 13203486838197986359642283)
    ·
      refine ⟨19805230257296979539463425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13203486838197986359642283 19805230257296979539463425)
      ·
        refine ⟨14853922692972734654597569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19805230257296979539463425 14853922692972734654597569)
        ·
          refine ⟨11140442019729550990948177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14853922692972734654597569 11140442019729550990948177)
          ·
            refine ⟨8355331514797163243211133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11140442019729550990948177 8355331514797163243211133)
            ·
              refine ⟨3133249318048936216204175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8355331514797163243211133 3133249318048936216204175)
              ·
                refine ⟨4699873977073404324306263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3133249318048936216204175 4699873977073404324306263)
                ·
                  refine ⟨7049810965610106486459395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4699873977073404324306263 7049810965610106486459395)
                  ·
                    refine ⟨10574716448415159729689093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7049810965610106486459395 10574716448415159729689093)
                    ·
                      refine ⟨1982759334077842449316705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10574716448415159729689093 1982759334077842449316705)
                      ·
                        rfl

theorem cell23_3861410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_3861410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861410 prefixEnd_3861410 := by exact prefixLift 3861410
  have htrace : WordTrace (prefixWord ++ tailWord_3861410) baseStart_3861410 baseEnd_3861410 := by
    simpa [prefixWord, tailWord_3861410, baseEnd_3861410] using wordTrace_append hprefix tailTrace_3861410
  have hstable : (prefixWord ++ tailWord_3861410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861410).length < 2 ^ (prefixWord ++ tailWord_3861410).sum := by decide
  have hdescent : baseEnd_3861410 < baseStart_3861410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861421 : List Nat := [1, 5, 2, 3, 1, 2, 2, 2, 1, 1, 3]
def baseStart_3861421 : Nat := 118140960795 + 3861421 * 2 ^ 59
def prefixEnd_3861421 : Nat := 4983230072969 + 3 ^ 40 * 3861421 * 2
def baseEnd_3861421 : Nat := 1982764982365041906279155

theorem tailTrace_3861421 : CollatzResearch.WordTrace tailWord_3861421 prefixEnd_3861421 1982764982365041906279155 := by
  unfold tailWord_3861421
  simp only [CollatzResearch.WordTrace]
  refine ⟨140837594143738670048168117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93891729429159113365445411 140837594143738670048168117)
  ·
    refine ⟨13203524450975500317015761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140837594143738670048168117 13203524450975500317015761)
    ·
      refine ⟨9902643338231625237761821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13203524450975500317015761 9902643338231625237761821)
      ·
        refine ⟨3713491251836859464160683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9902643338231625237761821 3713491251836859464160683)
        ·
          refine ⟨5570236877755289196241025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3713491251836859464160683 5570236877755289196241025)
          ·
            refine ⟨4177677658316466897180769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5570236877755289196241025 4177677658316466897180769)
            ·
              refine ⟨3133258243737350172885577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4177677658316466897180769 3133258243737350172885577)
              ·
                refine ⟨2349943682803012629664183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3133258243737350172885577 2349943682803012629664183)
                ·
                  refine ⟨3524915524204518944496275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2349943682803012629664183 3524915524204518944496275)
                  ·
                    refine ⟨5287373286306778416744413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3524915524204518944496275 5287373286306778416744413)
                    ·
                      refine ⟨1982764982365041906279155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5287373286306778416744413 1982764982365041906279155)
                      ·
                        rfl

theorem cell23_3861421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_3861421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861421 prefixEnd_3861421 := by exact prefixLift 3861421
  have htrace : WordTrace (prefixWord ++ tailWord_3861421) baseStart_3861421 baseEnd_3861421 := by
    simpa [prefixWord, tailWord_3861421, baseEnd_3861421] using wordTrace_append hprefix tailTrace_3861421
  have hstable : (prefixWord ++ tailWord_3861421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861421).length < 2 ^ (prefixWord ++ tailWord_3861421).sum := by decide
  have hdescent : baseEnd_3861421 < baseStart_3861421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861429 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 1, 9]
def baseStart_3861429 : Nat := 118140960795 + 3861429 * 2 ^ 59
def prefixEnd_3861429 : Nat := 4983230072969 + 3 ^ 40 * 3861429 * 2
def baseEnd_3861429 : Nat := 660923030070092624993039

theorem tailTrace_3861429 : CollatzResearch.WordTrace tailWord_3861429 prefixEnd_3861429 660923030070092624993039 := by
  unfold tailWord_3861429
  simp only [CollatzResearch.WordTrace]
  refine ⟨140837885927709687414459341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93891923951806458276306227 140837885927709687414459341)
  ·
    refine ⟨52814207222891132780422253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140837885927709687414459341 52814207222891132780422253)
    ·
      refine ⟨19805327708584174792658345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52814207222891132780422253 19805327708584174792658345)
      ·
        refine ⟨14853995781438131094493759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19805327708584174792658345 14853995781438131094493759)
        ·
          refine ⟨22280993672157196641740639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14853995781438131094493759 22280993672157196641740639)
          ·
            refine ⟨33421490508235794962610959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22280993672157196641740639 33421490508235794962610959)
            ·
              refine ⟨50132235762353692443916439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33421490508235794962610959 50132235762353692443916439)
              ·
                refine ⟨75198353643530538665874659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50132235762353692443916439 75198353643530538665874659)
                ·
                  refine ⟨112797530465295807998811989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75198353643530538665874659 112797530465295807998811989)
                  ·
                    refine ⟨660923030070092624993039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 112797530465295807998811989 660923030070092624993039)
                    ·
                      rfl

theorem cell23_3861429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_3861429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861429 prefixEnd_3861429 := by exact prefixLift 3861429
  have htrace : WordTrace (prefixWord ++ tailWord_3861429) baseStart_3861429 baseEnd_3861429 := by
    simpa [prefixWord, tailWord_3861429, baseEnd_3861429] using wordTrace_append hprefix tailTrace_3861429
  have hstable : (prefixWord ++ tailWord_3861429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861429).length < 2 ^ (prefixWord ++ tailWord_3861429).sum := by decide
  have hdescent : baseEnd_3861429 < baseStart_3861429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861500 : List Nat := [2, 2, 2, 1, 2, 5, 1, 1, 1, 4, 2]
def baseStart_3861500 : Nat := 118140960795 + 3861500 * 2 ^ 59
def prefixEnd_3861500 : Nat := 4983230072969 + 3 ^ 40 * 3861500 * 2
def baseEnd_3861500 : Nat := 1982805547336747097191291

theorem tailTrace_3861500 : CollatzResearch.WordTrace tailWord_3861500 prefixEnd_3861500 1982805547336747097191291 := by
  unfold tailWord_3861500
  simp only [CollatzResearch.WordTrace]
  refine ⟨70420237755226233270146977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93893650340301644360195969 70420237755226233270146977)
  ·
    refine ⟨52815178316419674952610233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70420237755226233270146977 52815178316419674952610233)
    ·
      refine ⟨39611383737314756214457675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52815178316419674952610233 39611383737314756214457675)
      ·
        refine ⟨59417075605972134321686513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39611383737314756214457675 59417075605972134321686513)
        ·
          refine ⟨44562806704479100741264885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59417075605972134321686513 44562806704479100741264885)
          ·
            refine ⟨4177763128544915694493583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44562806704479100741264885 4177763128544915694493583)
            ·
              refine ⟨6266644692817373541740375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4177763128544915694493583 6266644692817373541740375)
              ·
                refine ⟨9399967039226060312610563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6266644692817373541740375 9399967039226060312610563)
                ·
                  refine ⟨14099950558839090468915845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9399967039226060312610563 14099950558839090468915845)
                  ·
                    refine ⟨2643740729782329462921721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14099950558839090468915845 2643740729782329462921721)
                    ·
                      refine ⟨1982805547336747097191291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2643740729782329462921721 1982805547336747097191291)
                      ·
                        rfl

theorem cell23_3861500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 1, 4, 2].length) (baseStart_3861500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861500 prefixEnd_3861500 := by exact prefixLift 3861500
  have htrace : WordTrace (prefixWord ++ tailWord_3861500) baseStart_3861500 baseEnd_3861500 := by
    simpa [prefixWord, tailWord_3861500, baseEnd_3861500] using wordTrace_append hprefix tailTrace_3861500
  have hstable : (prefixWord ++ tailWord_3861500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861500).length < 2 ^ (prefixWord ++ tailWord_3861500).sum := by decide
  have hdescent : baseEnd_3861500 < baseStart_3861500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861600 : List Nat := [2, 1, 1, 3, 2, 2, 3, 4, 1, 4]
def baseStart_3861600 : Nat := 118140960795 + 3861600 * 2 ^ 59
def prefixEnd_3861600 : Nat := 4983230072969 + 3 ^ 40 * 3861600 * 2
def baseEnd_3861600 : Nat := 660952298467398901980277

theorem tailTrace_3861600 : CollatzResearch.WordTrace tailWord_3861600 prefixEnd_3861600 660952298467398901980277 := by
  unfold tailWord_3861600
  simp only [CollatzResearch.WordTrace]
  refine ⟨70422061405045091809467127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93896081873393455745956169 70422061405045091809467127)
  ·
    refine ⟨105633092107567637714200691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70422061405045091809467127 105633092107567637714200691)
    ·
      refine ⟨158449638161351456571301037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105633092107567637714200691 158449638161351456571301037)
      ·
        refine ⟨59418614310506796214237889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158449638161351456571301037 59418614310506796214237889)
        ·
          refine ⟨44563960732880097160678417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59418614310506796214237889 44563960732880097160678417)
          ·
            refine ⟨33422970549660072870508813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44563960732880097160678417 33422970549660072870508813)
            ·
              refine ⟨12533613956122527326440805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33422970549660072870508813 12533613956122527326440805)
              ·
                refine ⟨2350052616772973873707651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12533613956122527326440805 2350052616772973873707651)
                ·
                  refine ⟨3525078925159460810561477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2350052616772973873707651 3525078925159460810561477)
                  ·
                    refine ⟨660952298467398901980277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3525078925159460810561477 660952298467398901980277)
                    ·
                      rfl

theorem cell23_3861600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 1, 4].length) (baseStart_3861600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861600 prefixEnd_3861600 := by exact prefixLift 3861600
  have htrace : WordTrace (prefixWord ++ tailWord_3861600) baseStart_3861600 baseEnd_3861600 := by
    simpa [prefixWord, tailWord_3861600, baseEnd_3861600] using wordTrace_append hprefix tailTrace_3861600
  have hstable : (prefixWord ++ tailWord_3861600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861600).length < 2 ^ (prefixWord ++ tailWord_3861600).sum := by decide
  have hdescent : baseEnd_3861600 < baseStart_3861600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861613 : List Nat := [1, 5, 1, 1, 2, 2, 2, 3, 6]
def baseStart_3861613 : Nat := 118140960795 + 3861613 * 2 ^ 59
def prefixEnd_3861613 : Nat := 4983230072969 + 3 ^ 40 * 3861613 * 2
def baseEnd_3861613 : Nat := 220318174516745017230919

theorem tailTrace_3861613 : CollatzResearch.WordTrace tailWord_3861613 prefixEnd_3861613 220318174516745017230919 := by
  unfold tailWord_3861613
  simp only [CollatzResearch.WordTrace]
  refine ⟨140844596959043086839157493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93896397972695391226104995 140844596959043086839157493)
  ·
    refine ⟨13204180964910289391171015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140844596959043086839157493 13204180964910289391171015)
    ·
      refine ⟨19806271447365434086756523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13204180964910289391171015 19806271447365434086756523)
      ·
        refine ⟨29709407171048151130134785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19806271447365434086756523 29709407171048151130134785)
        ·
          refine ⟨22282055378286113347601089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29709407171048151130134785 22282055378286113347601089)
          ·
            refine ⟨16711541533714585010700817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22282055378286113347601089 16711541533714585010700817)
            ·
              refine ⟨12533656150285938758025613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16711541533714585010700817 12533656150285938758025613)
              ·
                refine ⟨4700121056357227034259605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12533656150285938758025613 4700121056357227034259605)
                ·
                  refine ⟨220318174516745017230919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4700121056357227034259605 220318174516745017230919)
                  ·
                    rfl

theorem cell23_3861613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_3861613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861613 prefixEnd_3861613 := by exact prefixLift 3861613
  have htrace : WordTrace (prefixWord ++ tailWord_3861613) baseStart_3861613 baseEnd_3861613 := by
    simpa [prefixWord, tailWord_3861613, baseEnd_3861613] using wordTrace_append hprefix tailTrace_3861613
  have hstable : (prefixWord ++ tailWord_3861613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861613).length < 2 ^ (prefixWord ++ tailWord_3861613).sum := by decide
  have hdescent : baseEnd_3861613 < baseStart_3861613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861677 : List Nat := [1, 5, 2, 1, 3, 1, 2, 2, 1, 5]
def baseStart_3861677 : Nat := 118140960795 + 3861677 * 2 ^ 59
def prefixEnd_3861677 : Nat := 4983230072969 + 3 ^ 40 * 3861677 * 2
def baseEnd_3861677 : Nat := 660965477804197634892659

theorem tailTrace_3861677 : CollatzResearch.WordTrace tailWord_3861677 prefixEnd_3861677 660965477804197634892659 := by
  unfold tailWord_3861677
  simp only [CollatzResearch.WordTrace]
  refine ⟨140846931230811225769487285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93897954153874150512991523 140846931230811225769487285)
  ·
    refine ⟨13204399802888552415889433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140846931230811225769487285 13204399802888552415889433)
    ·
      refine ⟨9903299852166414311917075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13204399802888552415889433 9903299852166414311917075)
      ·
        refine ⟨14854949778249621467875613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9903299852166414311917075 14854949778249621467875613)
        ·
          refine ⟨5570606166843608050453355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14854949778249621467875613 5570606166843608050453355)
          ·
            refine ⟨8355909250265412075680033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5570606166843608050453355 8355909250265412075680033)
            ·
              refine ⟨6266931937699059056760025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8355909250265412075680033 6266931937699059056760025)
              ·
                refine ⟨4700198953274294292570019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6266931937699059056760025 4700198953274294292570019)
                ·
                  refine ⟨7050298429911441438855029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4700198953274294292570019 7050298429911441438855029)
                  ·
                    refine ⟨660965477804197634892659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7050298429911441438855029 660965477804197634892659)
                    ·
                      rfl

theorem cell23_3861677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_3861677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861677 prefixEnd_3861677 := by exact prefixLift 3861677
  have htrace : WordTrace (prefixWord ++ tailWord_3861677) baseStart_3861677 baseEnd_3861677 := by
    simpa [prefixWord, tailWord_3861677, baseEnd_3861677] using wordTrace_append hprefix tailTrace_3861677
  have hstable : (prefixWord ++ tailWord_3861677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861677).length < 2 ^ (prefixWord ++ tailWord_3861677).sum := by decide
  have hdescent : baseEnd_3861677 < baseStart_3861677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861683 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 3]
def baseStart_3861683 : Nat := 118140960795 + 3861683 * 2 ^ 59
def prefixEnd_3861683 : Nat := 4983230072969 + 3 ^ 40 * 3861683 * 2
def baseEnd_3861683 : Nat := 1982899514296519881202949

theorem tailTrace_3861683 : CollatzResearch.WordTrace tailWord_3861683 prefixEnd_3861683 1982899514296519881202949 := by
  unfold tailWord_3861683
  simp only [CollatzResearch.WordTrace]
  refine ⟨140847150068789488794205703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93898100045859659196137135 140847150068789488794205703)
  ·
    refine ⟨211270725103184233191308555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140847150068789488794205703 211270725103184233191308555)
    ·
      refine ⟨316906087654776349786962833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211270725103184233191308555 316906087654776349786962833)
      ·
        refine ⟨237679565741082262340222125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316906087654776349786962833 237679565741082262340222125)
        ·
          refine ⟨89129837152905848377583297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237679565741082262340222125 89129837152905848377583297)
          ·
            refine ⟨66847377864679386283187473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89129837152905848377583297 66847377864679386283187473)
            ·
              refine ⟨50135533398509539712390605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66847377864679386283187473 50135533398509539712390605)
              ·
                refine ⟨18800825024441077392146477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50135533398509539712390605 18800825024441077392146477)
                ·
                  refine ⟨7050309384165404022054929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18800825024441077392146477 7050309384165404022054929)
                  ·
                    refine ⟨5287732038124053016541197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7050309384165404022054929 5287732038124053016541197)
                    ·
                      refine ⟨1982899514296519881202949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5287732038124053016541197 1982899514296519881202949)
                      ·
                        rfl

theorem cell23_3861683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 3].length) (baseStart_3861683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861683 prefixEnd_3861683 := by exact prefixLift 3861683
  have htrace : WordTrace (prefixWord ++ tailWord_3861683) baseStart_3861683 baseEnd_3861683 := by
    simpa [prefixWord, tailWord_3861683, baseEnd_3861683] using wordTrace_append hprefix tailTrace_3861683
  have hstable : (prefixWord ++ tailWord_3861683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861683).length < 2 ^ (prefixWord ++ tailWord_3861683).sum := by decide
  have hdescent : baseEnd_3861683 < baseStart_3861683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861693 : List Nat := [1, 4, 1, 2, 1, 1, 2, 4, 1, 2, 4]
def baseStart_3861693 : Nat := 118140960795 + 3861693 * 2 ^ 59
def prefixEnd_3861693 : Nat := 4983230072969 + 3 ^ 40 * 3861693 * 2
def baseEnd_3861693 : Nat := 1982904649103064842077903

theorem tailTrace_3861693 : CollatzResearch.WordTrace tailWord_3861693 prefixEnd_3861693 1982904649103064842077903 := by
  unfold tailWord_3861693
  simp only [CollatzResearch.WordTrace]
  refine ⟨140847514798753260502069733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93898343199168840334713155 140847514798753260502069733)
  ·
    refine ⟨26408909024766236344138075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140847514798753260502069733 26408909024766236344138075)
    ·
      refine ⟨39613363537149354516207113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26408909024766236344138075 39613363537149354516207113)
      ·
        refine ⟨29710022652862015887155335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39613363537149354516207113 29710022652862015887155335)
        ·
          refine ⟨44565033979293023830733003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29710022652862015887155335 44565033979293023830733003)
          ·
            refine ⟨66847550968939535746099505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44565033979293023830733003 66847550968939535746099505)
            ·
              refine ⟨50135663226704651809574629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66847550968939535746099505 50135663226704651809574629)
              ·
                refine ⟨9400436855007122214295243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50135663226704651809574629 9400436855007122214295243)
                ·
                  refine ⟨14100655282510683321442865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9400436855007122214295243 14100655282510683321442865)
                  ·
                    refine ⟨10575491461883012491082149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14100655282510683321442865 10575491461883012491082149)
                    ·
                      refine ⟨1982904649103064842077903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10575491461883012491082149 1982904649103064842077903)
                      ·
                        rfl

theorem cell23_3861693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_3861693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861693 prefixEnd_3861693 := by exact prefixLift 3861693
  have htrace : WordTrace (prefixWord ++ tailWord_3861693) baseStart_3861693 baseEnd_3861693 := by
    simpa [prefixWord, tailWord_3861693, baseEnd_3861693] using wordTrace_append hprefix tailTrace_3861693
  have hstable : (prefixWord ++ tailWord_3861693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861693).length < 2 ^ (prefixWord ++ tailWord_3861693).sum := by decide
  have hdescent : baseEnd_3861693 < baseStart_3861693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861697 : List Nat := [1, 2, 6, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_3861697 : Nat := 118140960795 + 3861697 * 2 ^ 59
def prefixEnd_3861697 : Nat := 4983230072969 + 3 ^ 40 * 3861697 * 2
def baseEnd_3861697 : Nat := 1982906703025682826427885

theorem tailTrace_3861697 : CollatzResearch.WordTrace tailWord_3861697 prefixEnd_3861697 1982906703025682826427885 := by
  unfold tailWord_3861697
  simp only [CollatzResearch.WordTrace]
  refine ⟨140847660690738769185215345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93898440460492512790143563 140847660690738769185215345)
  ·
    refine ⟨105635745518054076888911509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140847660690738769185215345 105635745518054076888911509)
    ·
      refine ⟨4951675571158784854167727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 105635745518054076888911509 4951675571158784854167727)
      ·
        refine ⟨7427513356738177281251591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4951675571158784854167727 7427513356738177281251591)
        ·
          refine ⟨11141270035107265921877387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7427513356738177281251591 11141270035107265921877387)
          ·
            refine ⟨16711905052660898882816081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11141270035107265921877387 16711905052660898882816081)
            ·
              refine ⟨12533928789495674162112061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16711905052660898882816081 12533928789495674162112061)
              ·
                refine ⟨4700223296060877810792023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12533928789495674162112061 4700223296060877810792023)
                ·
                  refine ⟨7050334944091316716188035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4700223296060877810792023 7050334944091316716188035)
                  ·
                    refine ⟨10575502416136975074282053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7050334944091316716188035 10575502416136975074282053)
                    ·
                      refine ⟨1982906703025682826427885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10575502416136975074282053 1982906703025682826427885)
                      ·
                        rfl

theorem cell23_3861697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_3861697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861697 prefixEnd_3861697 := by exact prefixLift 3861697
  have htrace : WordTrace (prefixWord ++ tailWord_3861697) baseStart_3861697 baseEnd_3861697 := by
    simpa [prefixWord, tailWord_3861697, baseEnd_3861697] using wordTrace_append hprefix tailTrace_3861697
  have hstable : (prefixWord ++ tailWord_3861697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861697).length < 2 ^ (prefixWord ++ tailWord_3861697).sum := by decide
  have hdescent : baseEnd_3861697 < baseStart_3861697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861748 : List Nat := [2, 6, 1, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_3861748 : Nat := 118140960795 + 3861748 * 2 ^ 59
def prefixEnd_3861748 : Nat := 4983230072969 + 3 ^ 40 * 3861748 * 2
def baseEnd_3861748 : Nat := 1982932890539062126890151

theorem tailTrace_3861748 : CollatzResearch.WordTrace tailWord_3861748 prefixEnd_3861748 1982932890539062126890151 := by
  unfold tailWord_3861748
  simp only [CollatzResearch.WordTrace]
  refine ⟨70424760406777002447660949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93899680542369336596881265 70424760406777002447660949)
  ·
    refine ⟨3301160644067671989734107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70424760406777002447660949 3301160644067671989734107)
    ·
      refine ⟨4951740966101507984601161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3301160644067671989734107 4951740966101507984601161)
      ·
        refine ⟨3713805724576130988450871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4951740966101507984601161 3713805724576130988450871)
        ·
          refine ⟨5570708586864196482676307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3713805724576130988450871 5570708586864196482676307)
          ·
            refine ⟨8356062880296294724014461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5570708586864196482676307 8356062880296294724014461)
            ·
              refine ⟨3133523580111110521505423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8356062880296294724014461 3133523580111110521505423)
              ·
                refine ⟨4700285370166665782258135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3133523580111110521505423 4700285370166665782258135)
                ·
                  refine ⟨7050428055249998673387203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4700285370166665782258135 7050428055249998673387203)
                  ·
                    refine ⟨10575642082874998010080805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7050428055249998673387203 10575642082874998010080805)
                    ·
                      refine ⟨1982932890539062126890151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10575642082874998010080805 1982932890539062126890151)
                      ·
                        rfl

theorem cell23_3861748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_3861748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861748 prefixEnd_3861748 := by exact prefixLift 3861748
  have htrace : WordTrace (prefixWord ++ tailWord_3861748) baseStart_3861748 baseEnd_3861748 := by
    simpa [prefixWord, tailWord_3861748, baseEnd_3861748] using wordTrace_append hprefix tailTrace_3861748
  have hstable : (prefixWord ++ tailWord_3861748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861748).length < 2 ^ (prefixWord ++ tailWord_3861748).sum := by decide
  have hdescent : baseEnd_3861748 < baseStart_3861748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861764 : List Nat := [2, 3, 2, 2, 2, 2, 2, 2, 2, 1, 3]
def baseStart_3861764 : Nat := 118140960795 + 3861764 * 2 ^ 59
def prefixEnd_3861764 : Nat := 4983230072969 + 3 ^ 40 * 3861764 * 2
def baseEnd_3861764 : Nat := 1982941106229534064290077

theorem tailTrace_3861764 : CollatzResearch.WordTrace tailWord_3861764 prefixEnd_3861764 1982941106229534064290077 := by
  unfold tailWord_3861764
  simp only [CollatzResearch.WordTrace]
  refine ⟨70425052190748019813952173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93900069587664026418602897 70425052190748019813952173)
  ·
    refine ⟨26409394571530507430232065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70425052190748019813952173 26409394571530507430232065)
    ·
      refine ⟨19807045928647880572674049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26409394571530507430232065 19807045928647880572674049)
      ·
        refine ⟨14855284446485910429505537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19807045928647880572674049 14855284446485910429505537)
        ·
          refine ⟨11141463334864432822129153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14855284446485910429505537 11141463334864432822129153)
          ·
            refine ⟨8356097501148324616596865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11141463334864432822129153 8356097501148324616596865)
            ·
              refine ⟨6267073125861243462447649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8356097501148324616596865 6267073125861243462447649)
              ·
                refine ⟨4700304844395932596835737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6267073125861243462447649 4700304844395932596835737)
                ·
                  refine ⟨3525228633296949447626803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4700304844395932596835737 3525228633296949447626803)
                  ·
                    refine ⟨5287842949945424171440205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3525228633296949447626803 5287842949945424171440205)
                    ·
                      refine ⟨1982941106229534064290077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5287842949945424171440205 1982941106229534064290077)
                      ·
                        rfl

theorem cell23_3861764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_3861764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861764 prefixEnd_3861764 := by exact prefixLift 3861764
  have htrace : WordTrace (prefixWord ++ tailWord_3861764) baseStart_3861764 baseEnd_3861764 := by
    simpa [prefixWord, tailWord_3861764, baseEnd_3861764] using wordTrace_append hprefix tailTrace_3861764
  have hstable : (prefixWord ++ tailWord_3861764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861764).length < 2 ^ (prefixWord ++ tailWord_3861764).sum := by decide
  have hdescent : baseEnd_3861764 < baseStart_3861764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861770 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2]
def baseStart_3861770 : Nat := 118140960795 + 3861770 * 2 ^ 59
def prefixEnd_3861770 : Nat := 4983230072969 + 3 ^ 40 * 3861770 * 2
def baseEnd_3861770 : Nat := 1982944187113461040815049

theorem tailTrace_3861770 : CollatzResearch.WordTrace tailWord_3861770 prefixEnd_3861770 1982944187113461040815049 := by
  unfold tailWord_3861770
  simp only [CollatzResearch.WordTrace]
  refine ⟨35212580804868575663155691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93900215479649535101748509 35212580804868575663155691)
  ·
    refine ⟨52818871207302863494733537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35212580804868575663155691 52818871207302863494733537)
    ·
      refine ⟨39614153405477147621050153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52818871207302863494733537 39614153405477147621050153)
      ·
        refine ⟨29710615054107860715787615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39614153405477147621050153 29710615054107860715787615)
        ·
          refine ⟨44565922581161791073681423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29710615054107860715787615 44565922581161791073681423)
          ·
            refine ⟨66848883871742686610522135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44565922581161791073681423 66848883871742686610522135)
            ·
              refine ⟨100273325807614029915783203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66848883871742686610522135 100273325807614029915783203)
              ·
                refine ⟨150409988711421044873674805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100273325807614029915783203 150409988711421044873674805)
                ·
                  refine ⟨14100936441695722956907013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150409988711421044873674805 14100936441695722956907013)
                  ·
                    refine ⟨2643925582817948054420065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14100936441695722956907013 2643925582817948054420065)
                    ·
                      refine ⟨1982944187113461040815049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2643925582817948054420065 1982944187113461040815049)
                      ·
                        rfl

theorem cell23_3861770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_3861770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861770 prefixEnd_3861770 := by exact prefixLift 3861770
  have htrace : WordTrace (prefixWord ++ tailWord_3861770) baseStart_3861770 baseEnd_3861770 := by
    simpa [prefixWord, tailWord_3861770, baseEnd_3861770] using wordTrace_append hprefix tailTrace_3861770
  have hstable : (prefixWord ++ tailWord_3861770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861770).length < 2 ^ (prefixWord ++ tailWord_3861770).sum := by decide
  have hdescent : baseEnd_3861770 < baseStart_3861770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861820 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 2, 3, 3]
def baseStart_3861820 : Nat := 118140960795 + 3861820 * 2 ^ 59
def prefixEnd_3861820 : Nat := 4983230072969 + 3 ^ 40 * 3861820 * 2
def baseEnd_3861820 : Nat := 1982969861146185845189819

theorem tailTrace_3861820 : CollatzResearch.WordTrace tailWord_3861820 prefixEnd_3861820 1982969861146185845189819 := by
  unfold tailWord_3861820
  simp only [CollatzResearch.WordTrace]
  refine ⟨70426073434646580595971457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93901431246195440794628609 70426073434646580595971457)
  ·
    refine ⟨52819555075984935446978593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70426073434646580595971457 52819555075984935446978593)
    ·
      refine ⟨39614666306988701585233945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52819555075984935446978593 39614666306988701585233945)
      ·
        refine ⟨29710999730241526188925459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39614666306988701585233945 29710999730241526188925459)
        ·
          refine ⟨44566499595362289283388189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29710999730241526188925459 44566499595362289283388189)
          ·
            refine ⟨16712437348260858481270571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44566499595362289283388189 16712437348260858481270571)
            ·
              refine ⟨25068656022391287721905857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16712437348260858481270571 25068656022391287721905857)
              ·
                refine ⟨18801492016793465791429393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25068656022391287721905857 18801492016793465791429393)
                ·
                  refine ⟨14101119012595099343572045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18801492016793465791429393 14101119012595099343572045)
                  ·
                    refine ⟨5287919629723162253839517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14101119012595099343572045 5287919629723162253839517)
                    ·
                      refine ⟨1982969861146185845189819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5287919629723162253839517 1982969861146185845189819)
                      ·
                        rfl

theorem cell23_3861820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_3861820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861820 prefixEnd_3861820 := by exact prefixLift 3861820
  have htrace : WordTrace (prefixWord ++ tailWord_3861820) baseStart_3861820 baseEnd_3861820 := by
    simpa [prefixWord, tailWord_3861820, baseEnd_3861820] using wordTrace_append hprefix tailTrace_3861820
  have hstable : (prefixWord ++ tailWord_3861820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861820).length < 2 ^ (prefixWord ++ tailWord_3861820).sum := by decide
  have hdescent : baseEnd_3861820 < baseStart_3861820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861821 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 4, 2, 2]
def baseStart_3861821 : Nat := 118140960795 + 3861821 * 2 ^ 59
def prefixEnd_3861821 : Nat := 4983230072969 + 3 ^ 40 * 3861821 * 2
def baseEnd_3861821 : Nat := 1982970374626840341277315

theorem tailTrace_3861821 : CollatzResearch.WordTrace tailWord_3861821 prefixEnd_3861821 1982970374626840341277315 := by
  unfold tailWord_3861821
  simp only [CollatzResearch.WordTrace]
  refine ⟨140852183342289538362729317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93901455561526358908486211 140852183342289538362729317)
  ·
    refine ⟨26409784376679288443011747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140852183342289538362729317 26409784376679288443011747)
    ·
      refine ⟨39614676565018932664517621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26409784376679288443011747 39614676565018932664517621)
      ·
        refine ⟨3713875927970524937298527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39614676565018932664517621 3713875927970524937298527)
        ·
          refine ⟨5570813891955787405947791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3713875927970524937298527 5570813891955787405947791)
          ·
            refine ⟨8356220837933681108921687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5570813891955787405947791 8356220837933681108921687)
            ·
              refine ⟨12534331256900521663382531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8356220837933681108921687 12534331256900521663382531)
              ·
                refine ⟨18801496885350782495073797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12534331256900521663382531 18801496885350782495073797)
                ·
                  refine ⟨3525280666003271717826337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18801496885350782495073797 3525280666003271717826337)
                  ·
                    refine ⟨2643960499502453788369753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3525280666003271717826337 2643960499502453788369753)
                    ·
                      refine ⟨1982970374626840341277315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2643960499502453788369753 1982970374626840341277315)
                      ·
                        rfl

theorem cell23_3861821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_3861821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861821 prefixEnd_3861821 := by exact prefixLift 3861821
  have htrace : WordTrace (prefixWord ++ tailWord_3861821) baseStart_3861821 baseEnd_3861821 := by
    simpa [prefixWord, tailWord_3861821, baseEnd_3861821] using wordTrace_append hprefix tailTrace_3861821
  have hstable : (prefixWord ++ tailWord_3861821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861821).length < 2 ^ (prefixWord ++ tailWord_3861821).sum := by decide
  have hdescent : baseEnd_3861821 < baseStart_3861821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861833 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 1, 2, 5]
def baseStart_3861833 : Nat := 118140960795 + 3861833 * 2 ^ 59
def prefixEnd_3861833 : Nat := 4983230072969 + 3 ^ 40 * 3861833 * 2
def baseEnd_3861833 : Nat := 1982976536394694294327259

theorem tailTrace_3861833 : CollatzResearch.WordTrace tailWord_3861833 prefixEnd_3861833 1982976536394694294327259 := by
  unfold tailWord_3861833
  simp only [CollatzResearch.WordTrace]
  refine ⟨140852621018246064412166153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93901747345497376274777435 140852621018246064412166153)
  ·
    refine ⟨105639465763684548309124615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140852621018246064412166153 105639465763684548309124615)
    ·
      refine ⟨158459198645526822463686923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105639465763684548309124615 158459198645526822463686923)
      ·
        refine ⟨237688797968290233695530385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158459198645526822463686923 237688797968290233695530385)
        ·
          refine ⟨178266598476217675271647789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237688797968290233695530385 178266598476217675271647789)
          ·
            refine ⟨66849974428581628226867921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178266598476217675271647789 66849974428581628226867921)
            ·
              refine ⟨50137480821436221170150941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66849974428581628226867921 50137480821436221170150941)
              ·
                refine ⟨18801555308038582938806603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50137480821436221170150941 18801555308038582938806603)
                ·
                  refine ⟨28202332962057874408209905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18801555308038582938806603 28202332962057874408209905)
                  ·
                    refine ⟨21151749721543405806157429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28202332962057874408209905 21151749721543405806157429)
                    ·
                      refine ⟨1982976536394694294327259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21151749721543405806157429 1982976536394694294327259)
                      ·
                        rfl

theorem cell23_3861833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 2, 5].length) (baseStart_3861833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861833 prefixEnd_3861833 := by exact prefixLift 3861833
  have htrace : WordTrace (prefixWord ++ tailWord_3861833) baseStart_3861833 baseEnd_3861833 := by
    simpa [prefixWord, tailWord_3861833, baseEnd_3861833] using wordTrace_append hprefix tailTrace_3861833
  have hstable : (prefixWord ++ tailWord_3861833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861833).length < 2 ^ (prefixWord ++ tailWord_3861833).sum := by decide
  have hdescent : baseEnd_3861833 < baseStart_3861833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861843 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 4]
def baseStart_3861843 : Nat := 118140960795 + 3861843 * 2 ^ 59
def prefixEnd_3861843 : Nat := 4983230072969 + 3 ^ 40 * 3861843 * 2
def baseEnd_3861843 : Nat := 1982981671201239255202213

theorem tailTrace_3861843 : CollatzResearch.WordTrace tailWord_3861843 prefixEnd_3861843 1982981671201239255202213 := by
  unfold tailWord_3861843
  simp only [CollatzResearch.WordTrace]
  refine ⟨140852985748209836120030183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93901990498806557413353455 140852985748209836120030183)
  ·
    refine ⟨211279478622314754180045275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140852985748209836120030183 211279478622314754180045275)
    ·
      refine ⟨316919217933472131270067913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211279478622314754180045275 316919217933472131270067913)
      ·
        refine ⟨237689413450104098452550935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316919217933472131270067913 237689413450104098452550935)
        ·
          refine ⟨356534120175156147678826403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237689413450104098452550935 356534120175156147678826403)
          ·
            refine ⟨534801180262734221518239605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356534120175156147678826403 534801180262734221518239605)
            ·
              refine ⟨50137610649631333267334963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 534801180262734221518239605 50137610649631333267334963)
              ·
                refine ⟨75206415974446999901002445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50137610649631333267334963 75206415974446999901002445)
                ·
                  refine ⟨28202405990417624962875917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75206415974446999901002445 28202405990417624962875917)
                  ·
                    refine ⟨10575902246406609361078469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28202405990417624962875917 10575902246406609361078469)
                    ·
                      refine ⟨1982981671201239255202213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10575902246406609361078469 1982981671201239255202213)
                      ·
                        rfl

theorem cell23_3861843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 4].length) (baseStart_3861843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861843 prefixEnd_3861843 := by exact prefixLift 3861843
  have htrace : WordTrace (prefixWord ++ tailWord_3861843) baseStart_3861843 baseEnd_3861843 := by
    simpa [prefixWord, tailWord_3861843, baseEnd_3861843] using wordTrace_append hprefix tailTrace_3861843
  have hstable : (prefixWord ++ tailWord_3861843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861843).length < 2 ^ (prefixWord ++ tailWord_3861843).sum := by decide
  have hdescent : baseEnd_3861843 < baseStart_3861843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861860 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 1, 3, 4]
def baseStart_3861860 : Nat := 118140960795 + 3861860 * 2 ^ 59
def prefixEnd_3861860 : Nat := 4983230072969 + 3 ^ 40 * 3861860 * 2
def baseEnd_3861860 : Nat := 1982990400372365688689635

theorem tailTrace_3861860 : CollatzResearch.WordTrace tailWord_3861860 prefixEnd_3861860 1982990400372365688689635 := by
  unfold tailWord_3861860
  simp only [CollatzResearch.WordTrace]
  refine ⟨70426802894574124011699517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93902403859432165348932689 70426802894574124011699517)
  ·
    refine ⟨26410051085465296504387319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70426802894574124011699517 26410051085465296504387319)
    ·
      refine ⟨39615076628197944756580979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26410051085465296504387319 39615076628197944756580979)
      ·
        refine ⟨59422614942296917134871469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39615076628197944756580979 59422614942296917134871469)
        ·
          refine ⟨22283480603361343925576801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59422614942296917134871469 22283480603361343925576801)
          ·
            refine ⟨16712610452521007944182601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22283480603361343925576801 16712610452521007944182601)
            ·
              refine ⟨12534457839390755958136951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16712610452521007944182601 12534457839390755958136951)
              ·
                refine ⟨18801686759086133937205427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12534457839390755958136951 18801686759086133937205427)
                ·
                  refine ⟨28202530138629200905808141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18801686759086133937205427 28202530138629200905808141)
                  ·
                    refine ⟨10575948801985950339678053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28202530138629200905808141 10575948801985950339678053)
                    ·
                      refine ⟨1982990400372365688689635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10575948801985950339678053 1982990400372365688689635)
                      ·
                        rfl

theorem cell23_3861860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_3861860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861860 prefixEnd_3861860 := by exact prefixLift 3861860
  have htrace : WordTrace (prefixWord ++ tailWord_3861860) baseStart_3861860 baseEnd_3861860 := by
    simpa [prefixWord, tailWord_3861860, baseEnd_3861860] using wordTrace_append hprefix tailTrace_3861860
  have hstable : (prefixWord ++ tailWord_3861860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861860).length < 2 ^ (prefixWord ++ tailWord_3861860).sum := by decide
  have hdescent : baseEnd_3861860 < baseStart_3861860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861873 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 1, 3, 6]
def baseStart_3861873 : Nat := 118140960795 + 3861873 * 2 ^ 59
def prefixEnd_3861873 : Nat := 4983230072969 + 3 ^ 40 * 3861873 * 2
def baseEnd_3861873 : Nat := 1982997075620874137827075

theorem tailTrace_3861873 : CollatzResearch.WordTrace tailWord_3861873 prefixEnd_3861873 1982997075620874137827075 := by
  unfold tailWord_3861873
  simp only [CollatzResearch.WordTrace]
  refine ⟨140854079938101151243622273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93902719958734100829081515 140854079938101151243622273)
  ·
    refine ⟨105640559953575863432716705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140854079938101151243622273 105640559953575863432716705)
    ·
      refine ⟨79230419965181897574537529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105640559953575863432716705 79230419965181897574537529)
      ·
        refine ⟨59422814973886423180903147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79230419965181897574537529 59422814973886423180903147)
        ·
          refine ⟨89134222460829634771354721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59422814973886423180903147 89134222460829634771354721)
          ·
            refine ⟨66850666845622226078516041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89134222460829634771354721 66850666845622226078516041)
            ·
              refine ⟨50138000134216669558887031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66850666845622226078516041 50138000134216669558887031)
              ·
                refine ⟨75207000201325004338330547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50138000134216669558887031 75207000201325004338330547)
                ·
                  refine ⟨112810500301987506507495821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75207000201325004338330547 112810500301987506507495821)
                  ·
                    refine ⟨42303937613245314940310933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112810500301987506507495821 42303937613245314940310933)
                    ·
                      refine ⟨1982997075620874137827075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42303937613245314940310933 1982997075620874137827075)
                      ·
                        rfl

theorem cell23_3861873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_3861873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861873 prefixEnd_3861873 := by exact prefixLift 3861873
  have htrace : WordTrace (prefixWord ++ tailWord_3861873) baseStart_3861873 baseEnd_3861873 := by
    simpa [prefixWord, tailWord_3861873, baseEnd_3861873] using wordTrace_append hprefix tailTrace_3861873
  have hstable : (prefixWord ++ tailWord_3861873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861873).length < 2 ^ (prefixWord ++ tailWord_3861873).sum := by decide
  have hdescent : baseEnd_3861873 < baseStart_3861873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861883 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 8]
def baseStart_3861883 : Nat := 118140960795 + 3861883 * 2 ^ 59
def prefixEnd_3861883 : Nat := 4983230072969 + 3 ^ 40 * 3861883 * 2
def baseEnd_3861883 : Nat := 220333578936379899855781

theorem tailTrace_3861883 : CollatzResearch.WordTrace tailWord_3861883 prefixEnd_3861883 220333578936379899855781 := by
  unfold tailWord_3861883
  simp only [CollatzResearch.WordTrace]
  refine ⟨140854444668064922951486303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93902963112043281967657535 140854444668064922951486303)
  ·
    refine ⟨211281667002097384427229455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140854444668064922951486303 211281667002097384427229455)
    ·
      refine ⟨316922500503146076640844183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211281667002097384427229455 316922500503146076640844183)
      ·
        refine ⟨475383750754719114961266275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316922500503146076640844183 475383750754719114961266275)
        ·
          refine ⟨713075626132078672441899413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475383750754719114961266275 713075626132078672441899413)
          ·
            refine ⟨33425419974941187770714035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 713075626132078672441899413 33425419974941187770714035)
            ·
              refine ⟨50138129962411781656071053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33425419974941187770714035 50138129962411781656071053)
              ·
                refine ⟨18801798735904418121026645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50138129962411781656071053 18801798735904418121026645)
                ·
                  refine ⟨220333578936379899855781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18801798735904418121026645 220333578936379899855781)
                  ·
                    rfl

theorem cell23_3861883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 8].length) (baseStart_3861883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861883 prefixEnd_3861883 := by exact prefixLift 3861883
  have htrace : WordTrace (prefixWord ++ tailWord_3861883) baseStart_3861883 baseEnd_3861883 := by
    simpa [prefixWord, tailWord_3861883, baseEnd_3861883] using wordTrace_append hprefix tailTrace_3861883
  have hstable : (prefixWord ++ tailWord_3861883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861883).length < 2 ^ (prefixWord ++ tailWord_3861883).sum := by decide
  have hdescent : baseEnd_3861883 < baseStart_3861883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861900 : List Nat := [2, 2, 1, 2, 1, 3, 3, 3, 6]
def baseStart_3861900 : Nat := 118140960795 + 3861900 * 2 ^ 59
def prefixEnd_3861900 : Nat := 4983230072969 + 3 ^ 40 * 3861900 * 2
def baseEnd_3861900 : Nat := 220334548844282836909939

theorem tailTrace_3861900 : CollatzResearch.WordTrace tailWord_3861900 prefixEnd_3861900 220334548844282836909939 := by
  unfold tailWord_3861900
  simp only [CollatzResearch.WordTrace]
  refine ⟨70427532354501667427427577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93903376472668889903236769 70427532354501667427427577)
  ·
    refine ⟨52820649265876250570570683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70427532354501667427427577 52820649265876250570570683)
    ·
      refine ⟨79230973898814375855856025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52820649265876250570570683 79230973898814375855856025)
      ·
        refine ⟨59423230424110781891892019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79230973898814375855856025 59423230424110781891892019)
        ·
          refine ⟨89134845636166172837838029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59423230424110781891892019 89134845636166172837838029)
          ·
            refine ⟨33425567113562314814189261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89134845636166172837838029 33425567113562314814189261)
            ·
              refine ⟨12534587667585868055320973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33425567113562314814189261 12534587667585868055320973)
              ·
                refine ⟨4700470375344700520745365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12534587667585868055320973 4700470375344700520745365)
                ·
                  refine ⟨220334548844282836909939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4700470375344700520745365 220334548844282836909939)
                  ·
                    rfl

theorem cell23_3861900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 6].length) (baseStart_3861900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861900 prefixEnd_3861900 := by exact prefixLift 3861900
  have htrace : WordTrace (prefixWord ++ tailWord_3861900) baseStart_3861900 baseEnd_3861900 := by
    simpa [prefixWord, tailWord_3861900, baseEnd_3861900] using wordTrace_append hprefix tailTrace_3861900
  have hstable : (prefixWord ++ tailWord_3861900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861900).length < 2 ^ (prefixWord ++ tailWord_3861900).sum := by decide
  have hdescent : baseEnd_3861900 < baseStart_3861900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861981 : List Nat := [1, 4, 3, 1, 1, 4, 2, 1, 1, 5]
def baseStart_3861981 : Nat := 118140960795 + 3861981 * 2 ^ 59
def prefixEnd_3861981 : Nat := 4983230072969 + 3 ^ 40 * 3861981 * 2
def baseEnd_3861981 : Nat := 661017510510519905092193

theorem tailTrace_3861981 : CollatzResearch.WordTrace tailWord_3861981 prefixEnd_3861981 661017510510519905092193 := by
  unfold tailWord_3861981
  simp only [CollatzResearch.WordTrace]
  refine ⟨140858019021709885688553797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93905346014473257125702531 140858019021709885688553797)
  ·
    refine ⟨26410878566570603566603837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140858019021709885688553797 26410878566570603566603837)
    ·
      refine ⟨9904079462463976337476439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26410878566570603566603837 9904079462463976337476439)
      ·
        refine ⟨14856119193695964506214659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9904079462463976337476439 14856119193695964506214659)
        ·
          refine ⟨22284178790543946759321989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14856119193695964506214659 22284178790543946759321989)
          ·
            refine ⟨4178283523226990017372873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22284178790543946759321989 4178283523226990017372873)
            ·
              refine ⟨3133712642420242513029655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4178283523226990017372873 3133712642420242513029655)
              ·
                refine ⟨4700568963630363769544483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3133712642420242513029655 4700568963630363769544483)
                ·
                  refine ⟨7050853445445545654316725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4700568963630363769544483 7050853445445545654316725)
                  ·
                    refine ⟨661017510510519905092193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7050853445445545654316725 661017510510519905092193)
                    ·
                      rfl

theorem cell23_3861981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_3861981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861981 prefixEnd_3861981 := by exact prefixLift 3861981
  have htrace : WordTrace (prefixWord ++ tailWord_3861981) baseStart_3861981 baseEnd_3861981 := by
    simpa [prefixWord, tailWord_3861981, baseEnd_3861981] using wordTrace_append hprefix tailTrace_3861981
  have hstable : (prefixWord ++ tailWord_3861981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861981).length < 2 ^ (prefixWord ++ tailWord_3861981).sum := by decide
  have hdescent : baseEnd_3861981 < baseStart_3861981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3861994 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 4, 4]
def baseStart_3861994 : Nat := 118140960795 + 3861994 * 2 ^ 59
def prefixEnd_3861994 : Nat := 4983230072969 + 3 ^ 40 * 3861994 * 2
def baseEnd_3861994 : Nat := 661019735593356054804673

theorem tailTrace_3861994 : CollatzResearch.WordTrace tailWord_3861994 prefixEnd_3861994 661019735593356054804673 := by
  unfold tailWord_3861994
  simp only [CollatzResearch.WordTrace]
  refine ⟨35214623292665697227194259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93905662113775192605851357 35214623292665697227194259)
  ·
    refine ⟨52821934938998545840791389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35214623292665697227194259 52821934938998545840791389)
    ·
      refine ⟨19808225602124454690296771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52821934938998545840791389 19808225602124454690296771)
      ·
        refine ⟨29712338403186682035445157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19808225602124454690296771 29712338403186682035445157)
        ·
          refine ⟨5571063450597502881645967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29712338403186682035445157 5571063450597502881645967)
          ·
            refine ⟨8356595175896254322468951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5571063450597502881645967 8356595175896254322468951)
            ·
              refine ⟨12534892763844381483703427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8356595175896254322468951 12534892763844381483703427)
              ·
                refine ⟨18802339145766572225555141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12534892763844381483703427 18802339145766572225555141)
                ·
                  refine ⟨3525438589831232292291589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18802339145766572225555141 3525438589831232292291589)
                  ·
                    refine ⟨661019735593356054804673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3525438589831232292291589 661019735593356054804673)
                    ·
                      rfl

theorem cell23_3861994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_3861994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3861994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3861994 prefixEnd_3861994 := by exact prefixLift 3861994
  have htrace : WordTrace (prefixWord ++ tailWord_3861994) baseStart_3861994 baseEnd_3861994 := by
    simpa [prefixWord, tailWord_3861994, baseEnd_3861994] using wordTrace_append hprefix tailTrace_3861994
  have hstable : (prefixWord ++ tailWord_3861994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3861994).length < 2 ^ (prefixWord ++ tailWord_3861994).sum := by decide
  have hdescent : baseEnd_3861994 < baseStart_3861994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3861994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862001 : List Nat := [1, 2, 2, 2, 3, 3, 2, 1, 3, 2, 2]
def baseStart_3862001 : Nat := 118140960795 + 3862001 * 2 ^ 59
def prefixEnd_3862001 : Nat := 4983230072969 + 3 ^ 40 * 3862001 * 2
def baseEnd_3862001 : Nat := 1983062801144649637026487

theorem tailTrace_3862001 : CollatzResearch.WordTrace tailWord_3862001 prefixEnd_3862001 1983062801144649637026487 := by
  unfold tailWord_3862001
  simp only [CollatzResearch.WordTrace]
  refine ⟨140858748481637429104281857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93905832321091619402854571 140858748481637429104281857)
  ·
    refine ⟨105644061361228071828211393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140858748481637429104281857 105644061361228071828211393)
    ·
      refine ⟨79233046020921053871158545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105644061361228071828211393 79233046020921053871158545)
      ·
        refine ⟨59424784515690790403368909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79233046020921053871158545 59424784515690790403368909)
        ·
          refine ⟨22284294193384046401263341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59424784515690790403368909 22284294193384046401263341)
          ·
            refine ⟨8356610322519017400473753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22284294193384046401263341 8356610322519017400473753)
            ·
              refine ⟨6267457741889263050355315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8356610322519017400473753 6267457741889263050355315)
              ·
                refine ⟨9401186612833894575532973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6267457741889263050355315 9401186612833894575532973)
                ·
                  refine ⟨3525444979812710465824865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9401186612833894575532973 3525444979812710465824865)
                  ·
                    refine ⟨2644083734859532849368649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3525444979812710465824865 2644083734859532849368649)
                    ·
                      refine ⟨1983062801144649637026487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2644083734859532849368649 1983062801144649637026487)
                      ·
                        rfl

theorem cell23_3862001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 2, 2].length) (baseStart_3862001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862001 prefixEnd_3862001 := by exact prefixLift 3862001
  have htrace : WordTrace (prefixWord ++ tailWord_3862001) baseStart_3862001 baseEnd_3862001 := by
    simpa [prefixWord, tailWord_3862001, baseEnd_3862001] using wordTrace_append hprefix tailTrace_3862001
  have hstable : (prefixWord ++ tailWord_3862001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862001).length < 2 ^ (prefixWord ++ tailWord_3862001).sum := by decide
  have hdescent : baseEnd_3862001 < baseStart_3862001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862018 : List Nat := [3, 4, 1, 2, 1, 1, 2, 2, 3, 2, 2]
def baseStart_3862018 : Nat := 118140960795 + 3862018 * 2 ^ 59
def prefixEnd_3862018 : Nat := 4983230072969 + 3 ^ 40 * 3862018 * 2
def baseEnd_3862018 : Nat := 1983071530315776070513909

theorem tailTrace_3862018 : CollatzResearch.WordTrace tailWord_3862018 prefixEnd_3862018 1983071530315776070513909 := by
  unfold tailWord_3862018
  simp only [CollatzResearch.WordTrace]
  refine ⟨35214842130643960251912677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93906245681717227338433805 35214842130643960251912677)
  ·
    refine ⟨6602782899495742547233627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35214842130643960251912677 6602782899495742547233627)
    ·
      refine ⟨9904174349243613820850441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6602782899495742547233627 9904174349243613820850441)
      ·
        refine ⟨7428130761932710365637831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9904174349243613820850441 7428130761932710365637831)
        ·
          refine ⟨11142196142899065548456747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7428130761932710365637831 11142196142899065548456747)
          ·
            refine ⟨16713294214348598322685121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11142196142899065548456747 16713294214348598322685121)
            ·
              refine ⟨12534970660761448742013841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16713294214348598322685121 12534970660761448742013841)
              ·
                refine ⟨9401227995571086556510381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12534970660761448742013841 9401227995571086556510381)
                ·
                  refine ⟨3525460498339157458691393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9401227995571086556510381 3525460498339157458691393)
                  ·
                    refine ⟨2644095373754368094018545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3525460498339157458691393 2644095373754368094018545)
                    ·
                      refine ⟨1983071530315776070513909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2644095373754368094018545 1983071530315776070513909)
                      ·
                        rfl

theorem cell23_3862018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_3862018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862018 prefixEnd_3862018 := by exact prefixLift 3862018
  have htrace : WordTrace (prefixWord ++ tailWord_3862018) baseStart_3862018 baseEnd_3862018 := by
    simpa [prefixWord, tailWord_3862018, baseEnd_3862018] using wordTrace_append hprefix tailTrace_3862018
  have hstable : (prefixWord ++ tailWord_3862018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862018).length < 2 ^ (prefixWord ++ tailWord_3862018).sum := by decide
  have hdescent : baseEnd_3862018 < baseStart_3862018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862029 : List Nat := [1, 7, 1, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_3862029 : Nat := 118140960795 + 3862029 * 2 ^ 59
def prefixEnd_3862029 : Nat := 4983230072969 + 3 ^ 40 * 3862029 * 2
def baseEnd_3862029 : Nat := 1983077178602975527476359

theorem tailTrace_3862029 : CollatzResearch.WordTrace tailWord_3862029 prefixEnd_3862029 1983077178602975527476359 := by
  unfold tailWord_3862029
  simp only [CollatzResearch.WordTrace]
  refine ⟨140859769725535989886301141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93906513150357326590867427 140859769725535989886301141)
  ·
    refine ⟨3301400852942249762960183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 140859769725535989886301141 3301400852942249762960183)
    ·
      refine ⟨4952101279413374644440275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3301400852942249762960183 4952101279413374644440275)
      ·
        refine ⟨7428151919120061966660413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4952101279413374644440275 7428151919120061966660413)
        ·
          refine ⟨2785556969670023237497655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7428151919120061966660413 2785556969670023237497655)
          ·
            refine ⟨4178335454505034856246483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2785556969670023237497655 4178335454505034856246483)
            ·
              refine ⟨6267503181757552284369725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4178335454505034856246483 6267503181757552284369725)
              ·
                refine ⟨2350313693159082106638647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6267503181757552284369725 2350313693159082106638647)
                ·
                  refine ⟨3525470539738623159957971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2350313693159082106638647 3525470539738623159957971)
                  ·
                    refine ⟨5288205809607934739936957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3525470539738623159957971 5288205809607934739936957)
                    ·
                      refine ⟨1983077178602975527476359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5288205809607934739936957 1983077178602975527476359)
                      ·
                        rfl

theorem cell23_3862029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_3862029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862029 prefixEnd_3862029 := by exact prefixLift 3862029
  have htrace : WordTrace (prefixWord ++ tailWord_3862029) baseStart_3862029 baseEnd_3862029 := by
    simpa [prefixWord, tailWord_3862029, baseEnd_3862029] using wordTrace_append hprefix tailTrace_3862029
  have hstable : (prefixWord ++ tailWord_3862029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862029).length < 2 ^ (prefixWord ++ tailWord_3862029).sum := by decide
  have hdescent : baseEnd_3862029 < baseStart_3862029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862074 : List Nat := [3, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2]
def baseStart_3862074 : Nat := 118140960795 + 3862074 * 2 ^ 59
def prefixEnd_3862074 : Nat := 4983230072969 + 3 ^ 40 * 3862074 * 2
def baseEnd_3862074 : Nat := 1983100285232427851413651

theorem tailTrace_3862074 : CollatzResearch.WordTrace tailWord_3862074 prefixEnd_3862074 1983100285232427851413651 := by
  unfold tailWord_3862074
  simp only [CollatzResearch.WordTrace]
  refine ⟨35215352752593240642922319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93907607340248641714459517 35215352752593240642922319)
  ·
    refine ⟨52823029128889860964383479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35215352752593240642922319 52823029128889860964383479)
    ·
      refine ⟨79234543693334791446575219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52823029128889860964383479 79234543693334791446575219)
      ·
        refine ⟨118851815540002187169862829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79234543693334791446575219 118851815540002187169862829)
        ·
          refine ⟨44569430827500820188698561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118851815540002187169862829 44569430827500820188698561)
          ·
            refine ⟨33427073120625615141523921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44569430827500820188698561 33427073120625615141523921)
            ·
              refine ⟨25070304840469211356142941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33427073120625615141523921 25070304840469211356142941)
              ·
                refine ⟨9401364315175954258553603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25070304840469211356142941 9401364315175954258553603)
                ·
                  refine ⟨14102046472763931387830405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9401364315175954258553603 14102046472763931387830405)
                  ·
                    refine ⟨2644133713643237135218201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14102046472763931387830405 2644133713643237135218201)
                    ·
                      refine ⟨1983100285232427851413651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2644133713643237135218201 1983100285232427851413651)
                      ·
                        rfl

theorem cell23_3862074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2].length) (baseStart_3862074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862074 prefixEnd_3862074 := by exact prefixLift 3862074
  have htrace : WordTrace (prefixWord ++ tailWord_3862074) baseStart_3862074 baseEnd_3862074 := by
    simpa [prefixWord, tailWord_3862074, baseEnd_3862074] using wordTrace_append hprefix tailTrace_3862074
  have hstable : (prefixWord ++ tailWord_3862074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862074).length < 2 ^ (prefixWord ++ tailWord_3862074).sum := by decide
  have hdescent : baseEnd_3862074 < baseStart_3862074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862080 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 9]
def baseStart_3862080 : Nat := 118140960795 + 3862080 * 2 ^ 59
def prefixEnd_3862080 : Nat := 4983230072969 + 3 ^ 40 * 3862080 * 2
def baseEnd_3862080 : Nat := 220344818457372758659847

theorem tailTrace_3862080 : CollatzResearch.WordTrace tailWord_3862080 prefixEnd_3862080 220344818457372758659847 := by
  unfold tailWord_3862080
  simp only [CollatzResearch.WordTrace]
  refine ⟨70430814924175612798203847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93907753232234150397605129 70430814924175612798203847)
  ·
    refine ⟨105646222386263419197305771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70430814924175612798203847 105646222386263419197305771)
    ·
      refine ⟨158469333579395128795958657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105646222386263419197305771 158469333579395128795958657)
      ·
        refine ⟨118852000184546346596968993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158469333579395128795958657 118852000184546346596968993)
        ·
          refine ⟨89139000138409759947726745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118852000184546346596968993 89139000138409759947726745)
          ·
            refine ⟨66854250103807319960795059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89139000138409759947726745 66854250103807319960795059)
            ·
              refine ⟨100281375155710979941192589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66854250103807319960795059 100281375155710979941192589)
              ·
                refine ⟨37605515683391617477947221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100281375155710979941192589 37605515683391617477947221)
                ·
                  refine ⟨220344818457372758659847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37605515683391617477947221 220344818457372758659847)
                  ·
                    rfl

theorem cell23_3862080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 9].length) (baseStart_3862080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862080 prefixEnd_3862080 := by exact prefixLift 3862080
  have htrace : WordTrace (prefixWord ++ tailWord_3862080) baseStart_3862080 baseEnd_3862080 := by
    simpa [prefixWord, tailWord_3862080, baseEnd_3862080] using wordTrace_append hprefix tailTrace_3862080
  have hstable : (prefixWord ++ tailWord_3862080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862080).length < 2 ^ (prefixWord ++ tailWord_3862080).sum := by decide
  have hdescent : baseEnd_3862080 < baseStart_3862080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862102 : List Nat := [5, 2, 2, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_3862102 : Nat := 118140960795 + 3862102 * 2 ^ 59
def prefixEnd_3862102 : Nat := 4983230072969 + 3 ^ 40 * 3862102 * 2
def baseEnd_3862102 : Nat := 1983114662690753741863523

theorem tailTrace_3862102 : CollatzResearch.WordTrace tailWord_3862102 prefixEnd_3862102 1983114662690753741863523 := by
  unfold tailWord_3862102
  simp only [CollatzResearch.WordTrace]
  refine ⟨8803902015891970209606785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93908288169514348902472373 8803902015891970209606785)
  ·
    refine ⟨6602926511918977657205089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8803902015891970209606785 6602926511918977657205089)
    ·
      refine ⟨4952194883939233242903817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6602926511918977657205089 4952194883939233242903817)
      ·
        refine ⟨3714146162954424932177863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4952194883939233242903817 3714146162954424932177863)
        ·
          refine ⟨5571219244431637398266795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3714146162954424932177863 5571219244431637398266795)
          ·
            refine ⟨8356828866647456097400193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5571219244431637398266795 8356828866647456097400193)
            ·
              refine ⟨6267621649985592073050145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8356828866647456097400193 6267621649985592073050145)
              ·
                refine ⟨4700716237489194054787609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6267621649985592073050145 4700716237489194054787609)
                ·
                  refine ⟨3525537178116895541090707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4700716237489194054787609 3525537178116895541090707)
                  ·
                    refine ⟨5288305767175343311636061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3525537178116895541090707 5288305767175343311636061)
                    ·
                      refine ⟨1983114662690753741863523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5288305767175343311636061 1983114662690753741863523)
                      ·
                        rfl

theorem cell23_3862102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_3862102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862102 prefixEnd_3862102 := by exact prefixLift 3862102
  have htrace : WordTrace (prefixWord ++ tailWord_3862102) baseStart_3862102 baseEnd_3862102 := by
    simpa [prefixWord, tailWord_3862102, baseEnd_3862102] using wordTrace_append hprefix tailTrace_3862102
  have hstable : (prefixWord ++ tailWord_3862102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862102).length < 2 ^ (prefixWord ++ tailWord_3862102).sum := by decide
  have hdescent : baseEnd_3862102 < baseStart_3862102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862108 : List Nat := [2, 2, 4, 1, 2, 1, 1, 4, 2, 2, 2]
def baseStart_3862108 : Nat := 118140960795 + 3862108 * 2 ^ 59
def prefixEnd_3862108 : Nat := 4983230072969 + 3 ^ 40 * 3862108 * 2
def baseEnd_3862108 : Nat := 1983117743574680718388495

theorem tailTrace_3862108 : CollatzResearch.WordTrace tailWord_3862108 prefixEnd_3862108 1983117743574680718388495 := by
  unfold tailWord_3862108
  simp only [CollatzResearch.WordTrace]
  refine ⟨70431325546124893189213489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93908434061499857585617985 70431325546124893189213489)
  ·
    refine ⟨52823494159593669891910117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70431325546124893189213489 52823494159593669891910117)
    ·
      refine ⟨9904405154923813104733147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52823494159593669891910117 9904405154923813104733147)
      ·
        refine ⟨14856607732385719657099721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9904405154923813104733147 14856607732385719657099721)
        ·
          refine ⟨11142455799289289742824791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14856607732385719657099721 11142455799289289742824791)
          ·
            refine ⟨16713683698933934614237187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11142455799289289742824791 16713683698933934614237187)
            ·
              refine ⟨25070525548400901921355781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16713683698933934614237187 25070525548400901921355781)
              ·
                refine ⟨4700723540325169110254209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25070525548400901921355781 4700723540325169110254209)
                ·
                  refine ⟨3525542655243876832690657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4700723540325169110254209 3525542655243876832690657)
                  ·
                    refine ⟨2644156991432907624517993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3525542655243876832690657 2644156991432907624517993)
                    ·
                      refine ⟨1983117743574680718388495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2644156991432907624517993 1983117743574680718388495)
                      ·
                        rfl

theorem cell23_3862108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_3862108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862108 prefixEnd_3862108 := by exact prefixLift 3862108
  have htrace : WordTrace (prefixWord ++ tailWord_3862108) baseStart_3862108 baseEnd_3862108 := by
    simpa [prefixWord, tailWord_3862108, baseEnd_3862108] using wordTrace_append hprefix tailTrace_3862108
  have hstable : (prefixWord ++ tailWord_3862108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862108).length < 2 ^ (prefixWord ++ tailWord_3862108).sum := by decide
  have hdescent : baseEnd_3862108 < baseStart_3862108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862221 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 8]
def baseStart_3862221 : Nat := 118140960795 + 3862221 * 2 ^ 59
def prefixEnd_3862221 : Nat := 4983230072969 + 3 ^ 40 * 3862221 * 2
def baseEnd_3862221 : Nat := 220352862987626530697275

theorem tailTrace_3862221 : CollatzResearch.WordTrace tailWord_3862221 prefixEnd_3862221 220352862987626530697275 := by
  unfold tailWord_3862221
  simp only [CollatzResearch.WordTrace]
  refine ⟨140866772540840406677290517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93911181693893604451527011 140866772540840406677290517)
  ·
    refine ⟨6603129962851894062997993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 140866772540840406677290517 6603129962851894062997993)
    ·
      refine ⟨4952347472138920547248495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6603129962851894062997993 4952347472138920547248495)
      ·
        refine ⟨7428521208208380820872743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4952347472138920547248495 7428521208208380820872743)
        ·
          refine ⟨11142781812312571231309115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7428521208208380820872743 11142781812312571231309115)
          ·
            refine ⟨16714172718468856846963673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11142781812312571231309115 16714172718468856846963673)
            ·
              refine ⟨12535629538851642635222755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16714172718468856846963673 12535629538851642635222755)
              ·
                refine ⟨18803444308277463952834133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12535629538851642635222755 18803444308277463952834133)
                ·
                  refine ⟨220352862987626530697275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18803444308277463952834133 220352862987626530697275)
                  ·
                    rfl

theorem cell23_3862221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_3862221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862221 prefixEnd_3862221 := by exact prefixLift 3862221
  have htrace : WordTrace (prefixWord ++ tailWord_3862221) baseStart_3862221 baseEnd_3862221 := by
    simpa [prefixWord, tailWord_3862221, baseEnd_3862221] using wordTrace_append hprefix tailTrace_3862221
  have hstable : (prefixWord ++ tailWord_3862221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862221).length < 2 ^ (prefixWord ++ tailWord_3862221).sum := by decide
  have hdescent : baseEnd_3862221 < baseStart_3862221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862224 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 3, 5, 2]
def baseStart_3862224 : Nat := 118140960795 + 3862224 * 2 ^ 59
def prefixEnd_3862224 : Nat := 4983230072969 + 3 ^ 40 * 3862224 * 2
def baseEnd_3862224 : Nat := 1983177307330602264537961

theorem tailTrace_3862224 : CollatzResearch.WordTrace tailWord_3862224 prefixEnd_3862224 1983177307330602264537961 := by
  unfold tailWord_3862224
  simp only [CollatzResearch.WordTrace]
  refine ⟨70433440979914769094824863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93911254639886358793099817 70433440979914769094824863)
  ·
    refine ⟨105650161469872153642237295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70433440979914769094824863 105650161469872153642237295)
    ·
      refine ⟨158475242204808230463355943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105650161469872153642237295 158475242204808230463355943)
      ·
        refine ⟨237712863307212345695033915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158475242204808230463355943 237712863307212345695033915)
        ·
          refine ⟨356569294960818518542550873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237712863307212345695033915 356569294960818518542550873)
          ·
            refine ⟨267426971220613888906913155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356569294960818518542550873 267426971220613888906913155)
            ·
              refine ⟨401140456830920833360369733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267426971220613888906913155 401140456830920833360369733)
              ·
                refine ⟨75213835655797656255069325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 401140456830920833360369733 75213835655797656255069325)
                ·
                  refine ⟨28205188370924121095650997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75213835655797656255069325 28205188370924121095650997)
                  ·
                    refine ⟨2644236409774136352717281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28205188370924121095650997 2644236409774136352717281)
                    ·
                      refine ⟨1983177307330602264537961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2644236409774136352717281 1983177307330602264537961)
                      ·
                        rfl

theorem cell23_3862224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 3, 5, 2].length) (baseStart_3862224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862224 prefixEnd_3862224 := by exact prefixLift 3862224
  have htrace : WordTrace (prefixWord ++ tailWord_3862224) baseStart_3862224 baseEnd_3862224 := by
    simpa [prefixWord, tailWord_3862224, baseEnd_3862224] using wordTrace_append hprefix tailTrace_3862224
  have hstable : (prefixWord ++ tailWord_3862224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862224).length < 2 ^ (prefixWord ++ tailWord_3862224).sum := by decide
  have hdescent : baseEnd_3862224 < baseStart_3862224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862258 : List Nat := [3, 2, 1, 3, 1, 1, 4, 1, 2, 3, 2]
def baseStart_3862258 : Nat := 118140960795 + 3862258 * 2 ^ 59
def prefixEnd_3862258 : Nat := 4983230072969 + 3 ^ 40 * 3862258 * 2
def baseEnd_3862258 : Nat := 1983194765672855131512805

theorem tailTrace_3862258 : CollatzResearch.WordTrace tailWord_3862258 prefixEnd_3862258 1983194765672855131512805 := by
  unfold tailWord_3862258
  simp only [CollatzResearch.WordTrace]
  refine ⟨35217030510426590499096857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93912081361137574664258285 35217030510426590499096857)
  ·
    refine ⟨26412772882819942874322643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35217030510426590499096857 26412772882819942874322643)
    ·
      refine ⟨39619159324229914311483965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26412772882819942874322643 39619159324229914311483965)
      ·
        refine ⟨14857184746586217866806487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39619159324229914311483965 14857184746586217866806487)
        ·
          refine ⟨22285777119879326800209731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14857184746586217866806487 22285777119879326800209731)
          ·
            refine ⟨33428665679818990200314597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22285777119879326800209731 33428665679818990200314597)
            ·
              refine ⟨6267874814966060662558987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33428665679818990200314597 6267874814966060662558987)
              ·
                refine ⟨9401812222449090993838481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6267874814966060662558987 9401812222449090993838481)
                ·
                  refine ⟨7051359166836818245378861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9401812222449090993838481 7051359166836818245378861)
                  ·
                    refine ⟨2644259687563806842017073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7051359166836818245378861 2644259687563806842017073)
                    ·
                      refine ⟨1983194765672855131512805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2644259687563806842017073 1983194765672855131512805)
                      ·
                        rfl

theorem cell23_3862258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_3862258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862258 prefixEnd_3862258 := by exact prefixLift 3862258
  have htrace : WordTrace (prefixWord ++ tailWord_3862258) baseStart_3862258 baseEnd_3862258 := by
    simpa [prefixWord, tailWord_3862258, baseEnd_3862258] using wordTrace_append hprefix tailTrace_3862258
  have hstable : (prefixWord ++ tailWord_3862258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862258).length < 2 ^ (prefixWord ++ tailWord_3862258).sum := by decide
  have hdescent : baseEnd_3862258 < baseStart_3862258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862264 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 4, 4]
def baseStart_3862264 : Nat := 118140960795 + 3862264 * 2 ^ 59
def prefixEnd_3862264 : Nat := 4983230072969 + 3 ^ 40 * 3862264 * 2
def baseEnd_3862264 : Nat := 661065948852260702679259

theorem tailTrace_3862264 : CollatzResearch.WordTrace tailWord_3862264 prefixEnd_3862264 661065948852260702679259 := by
  unfold tailWord_3862264
  simp only [CollatzResearch.WordTrace]
  refine ⟨70434170439842312510552923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93912227253123083347403897 70434170439842312510552923)
  ·
    refine ⟨105651255659763468765829385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70434170439842312510552923 105651255659763468765829385)
    ·
      refine ⟨79238441744822601574372039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105651255659763468765829385 79238441744822601574372039)
      ·
        refine ⟨118857662617233902361558059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79238441744822601574372039 118857662617233902361558059)
        ·
          refine ⟨178286493925850853542337089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118857662617233902361558059 178286493925850853542337089)
          ·
            refine ⟨133714870444388140156752817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178286493925850853542337089 133714870444388140156752817)
            ·
              refine ⟨100286152833291105117564613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133714870444388140156752817 100286152833291105117564613)
              ·
                refine ⟨18803653656242082209543365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100286152833291105117564613 18803653656242082209543365)
                ·
                  refine ⟨3525685060545390414289381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18803653656242082209543365 3525685060545390414289381)
                  ·
                    refine ⟨661065948852260702679259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3525685060545390414289381 661065948852260702679259)
                    ·
                      rfl

theorem cell23_3862264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 4, 4].length) (baseStart_3862264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862264 prefixEnd_3862264 := by exact prefixLift 3862264
  have htrace : WordTrace (prefixWord ++ tailWord_3862264) baseStart_3862264 baseEnd_3862264 := by
    simpa [prefixWord, tailWord_3862264, baseEnd_3862264] using wordTrace_append hprefix tailTrace_3862264
  have hstable : (prefixWord ++ tailWord_3862264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862264).length < 2 ^ (prefixWord ++ tailWord_3862264).sum := by decide
  have hdescent : baseEnd_3862264 < baseStart_3862264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862267 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 6]
def baseStart_3862267 : Nat := 118140960795 + 3862267 * 2 ^ 59
def prefixEnd_3862267 : Nat := 4983230072969 + 3 ^ 40 * 3862267 * 2
def baseEnd_3862267 : Nat := 1983199386998745596300263

theorem tailTrace_3862267 : CollatzResearch.WordTrace tailWord_3862267 prefixEnd_3862267 1983199386998745596300263 := by
  unfold tailWord_3862267
  simp only [CollatzResearch.WordTrace]
  refine ⟨140868450298673756533465055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93912300199115837688976703 140868450298673756533465055)
  ·
    refine ⟨211302675448010634800197583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140868450298673756533465055 211302675448010634800197583)
    ·
      refine ⟨316954013172015952200296375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211302675448010634800197583 316954013172015952200296375)
      ·
        refine ⟨475431019758023928300444563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316954013172015952200296375 475431019758023928300444563)
        ·
          refine ⟨713146529637035892450666845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475431019758023928300444563 713146529637035892450666845)
          ·
            refine ⟨267429948613888459669000067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 713146529637035892450666845 267429948613888459669000067)
            ·
              refine ⟨401144922920832689503500101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267429948613888459669000067 401144922920832689503500101)
              ·
                refine ⟨75214673047656129281906269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 401144922920832689503500101 75214673047656129281906269)
                ·
                  refine ⟨28205502392871048480714851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75214673047656129281906269 28205502392871048480714851)
                  ·
                    refine ⟨42308253589306572721072277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28205502392871048480714851 42308253589306572721072277)
                    ·
                      refine ⟨1983199386998745596300263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42308253589306572721072277 1983199386998745596300263)
                      ·
                        rfl

theorem cell23_3862267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 6].length) (baseStart_3862267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862267 prefixEnd_3862267 := by exact prefixLift 3862267
  have htrace : WordTrace (prefixWord ++ tailWord_3862267) baseStart_3862267 baseEnd_3862267 := by
    simpa [prefixWord, tailWord_3862267, baseEnd_3862267] using wordTrace_append hprefix tailTrace_3862267
  have hstable : (prefixWord ++ tailWord_3862267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862267).length < 2 ^ (prefixWord ++ tailWord_3862267).sum := by decide
  have hdescent : baseEnd_3862267 < baseStart_3862267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862282 : List Nat := [3, 1, 2, 2, 1, 5, 2, 2, 1, 1, 3]
def baseStart_3862282 : Nat := 118140960795 + 3862282 * 2 ^ 59
def prefixEnd_3862282 : Nat := 4983230072969 + 3 ^ 40 * 3862282 * 2
def baseEnd_3862282 : Nat := 1983207089208563037612695

theorem tailTrace_3862282 : CollatzResearch.WordTrace tailWord_3862282 prefixEnd_3862282 1983207089208563037612695 := by
  unfold tailWord_3862282
  simp only [CollatzResearch.WordTrace]
  refine ⟨35217249348404853523815275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93912664929079609396840733 35217249348404853523815275)
  ·
    refine ⟨52825874022607280285722913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35217249348404853523815275 52825874022607280285722913)
    ·
      refine ⟨39619405516955460214292185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52825874022607280285722913 39619405516955460214292185)
      ·
        refine ⟨29714554137716595160719139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39619405516955460214292185 29714554137716595160719139)
        ·
          refine ⟨44571831206574892741078709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29714554137716595160719139 44571831206574892741078709)
          ·
            refine ⟨4178609175616396194476129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44571831206574892741078709 4178609175616396194476129)
            ·
              refine ⟨3133956881712297145857097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4178609175616396194476129 3133956881712297145857097)
              ·
                refine ⟨2350467661284222859392823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3133956881712297145857097 2350467661284222859392823)
                ·
                  refine ⟨3525701491926334289089235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2350467661284222859392823 3525701491926334289089235)
                  ·
                    refine ⟨5288552237889501433633853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3525701491926334289089235 5288552237889501433633853)
                    ·
                      refine ⟨1983207089208563037612695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5288552237889501433633853 1983207089208563037612695)
                      ·
                        rfl

theorem cell23_3862282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_3862282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862282 prefixEnd_3862282 := by exact prefixLift 3862282
  have htrace : WordTrace (prefixWord ++ tailWord_3862282) baseStart_3862282 baseEnd_3862282 := by
    simpa [prefixWord, tailWord_3862282, baseEnd_3862282] using wordTrace_append hprefix tailTrace_3862282
  have hstable : (prefixWord ++ tailWord_3862282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862282).length < 2 ^ (prefixWord ++ tailWord_3862282).sum := by decide
  have hdescent : baseEnd_3862282 < baseStart_3862282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862287 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 7]
def baseStart_3862287 : Nat := 118140960795 + 3862287 * 2 ^ 59
def prefixEnd_3862287 : Nat := 4983230072969 + 3 ^ 40 * 3862287 * 2
def baseEnd_3862287 : Nat := 1983209656611835518050171

theorem tailTrace_3862287 : CollatzResearch.WordTrace tailWord_3862287 prefixEnd_3862287 1983209656611835518050171 := by
  unfold tailWord_3862287
  simp only [CollatzResearch.WordTrace]
  refine ⟨140869179758601299949193115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93912786505734199966128743 140869179758601299949193115)
  ·
    refine ⟨211303769637901949923789673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140869179758601299949193115 211303769637901949923789673)
    ·
      refine ⟨158477827228426462442842255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211303769637901949923789673 158477827228426462442842255)
      ·
        refine ⟨237716740842639693664263383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158477827228426462442842255 237716740842639693664263383)
        ·
          refine ⟨356575111263959540496395075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237716740842639693664263383 356575111263959540496395075)
          ·
            refine ⟨534862666895939310744592613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356575111263959540496395075 534862666895939310744592613)
            ·
              refine ⟨100286750042988620764611115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 534862666895939310744592613 100286750042988620764611115)
              ·
                refine ⟨150430125064482931146916673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100286750042988620764611115 150430125064482931146916673)
                ·
                  refine ⟨112822593798362198360187505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150430125064482931146916673 112822593798362198360187505)
                  ·
                    refine ⟨84616945348771648770140629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112822593798362198360187505 84616945348771648770140629)
                    ·
                      refine ⟨1983209656611835518050171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84616945348771648770140629 1983209656611835518050171)
                      ·
                        rfl

theorem cell23_3862287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_3862287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862287 prefixEnd_3862287 := by exact prefixLift 3862287
  have htrace : WordTrace (prefixWord ++ tailWord_3862287) baseStart_3862287 baseEnd_3862287 := by
    simpa [prefixWord, tailWord_3862287, baseEnd_3862287] using wordTrace_append hprefix tailTrace_3862287
  have hstable : (prefixWord ++ tailWord_3862287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862287).length < 2 ^ (prefixWord ++ tailWord_3862287).sum := by decide
  have hdescent : baseEnd_3862287 < baseStart_3862287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862321 : List Nat := [1, 2, 2, 3, 2, 2, 2, 2, 1, 3, 3]
def baseStart_3862321 : Nat := 118140960795 + 3862321 * 2 ^ 59
def prefixEnd_3862321 : Nat := 4983230072969 + 3 ^ 40 * 3862321 * 2
def baseEnd_3862321 : Nat := 1983227114954088385025015

theorem tailTrace_3862321 : CollatzResearch.WordTrace tailWord_3862321 prefixEnd_3862321 1983227114954088385025015 := by
  unfold tailWord_3862321
  simp only [CollatzResearch.WordTrace]
  refine ⟨140870419840478123755930817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93913613226985415837287211 140870419840478123755930817)
  ·
    refine ⟨105652814880358592816948113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140870419840478123755930817 105652814880358592816948113)
    ·
      refine ⟨79239611160268944612711085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105652814880358592816948113 79239611160268944612711085)
      ·
        refine ⟨29714854185100854229766657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79239611160268944612711085 29714854185100854229766657)
        ·
          refine ⟨22286140638825640672324993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29714854185100854229766657 22286140638825640672324993)
          ·
            refine ⟨16714605479119230504243745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22286140638825640672324993 16714605479119230504243745)
            ·
              refine ⟨12535954109339422878182809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16714605479119230504243745 12535954109339422878182809)
              ·
                refine ⟨9401965582004567158637107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12535954109339422878182809 9401965582004567158637107)
                ·
                  refine ⟨14102948373006850737955661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9401965582004567158637107 14102948373006850737955661)
                  ·
                    refine ⟨5288605639877569026733373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14102948373006850737955661 5288605639877569026733373)
                    ·
                      refine ⟨1983227114954088385025015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5288605639877569026733373 1983227114954088385025015)
                      ·
                        rfl

theorem cell23_3862321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_3862321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862321 prefixEnd_3862321 := by exact prefixLift 3862321
  have htrace : WordTrace (prefixWord ++ tailWord_3862321) baseStart_3862321 baseEnd_3862321 := by
    simpa [prefixWord, tailWord_3862321, baseEnd_3862321] using wordTrace_append hprefix tailTrace_3862321
  have hstable : (prefixWord ++ tailWord_3862321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862321).length < 2 ^ (prefixWord ++ tailWord_3862321).sum := by decide
  have hdescent : baseEnd_3862321 < baseStart_3862321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862322 : List Nat := [3, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2]
def baseStart_3862322 : Nat := 118140960795 + 3862322 * 2 ^ 59
def prefixEnd_3862322 : Nat := 4983230072969 + 3 ^ 40 * 3862322 * 2
def baseEnd_3862322 : Nat := 1983227628434742881112511

theorem tailTrace_3862322 : CollatzResearch.WordTrace tailWord_3862322 prefixEnd_3862322 1983227628434742881112511 := by
  unfold tailWord_3862322
  simp only [CollatzResearch.WordTrace]
  refine ⟨35217614078368625231679305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93913637542316333951144813 35217614078368625231679305)
  ·
    refine ⟨26413210558776468923759479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35217614078368625231679305 26413210558776468923759479)
    ·
      refine ⟨39619815838164703385639219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26413210558776468923759479 39619815838164703385639219)
      ·
        refine ⟨59429723757247055078458829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39619815838164703385639219 59429723757247055078458829)
        ·
          refine ⟨22286146408967645654422061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59429723757247055078458829 22286146408967645654422061)
          ·
            refine ⟨8357304903362867120408273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22286146408967645654422061 8357304903362867120408273)
            ·
              refine ⟨6267978677522150340306205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8357304903362867120408273 6267978677522150340306205)
              ·
                refine ⟨2350492004070806377614827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6267978677522150340306205 2350492004070806377614827)
                ·
                  refine ⟨3525738006106209566422241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2350492004070806377614827 3525738006106209566422241)
                  ·
                    refine ⟨2644303504579657174816681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3525738006106209566422241 2644303504579657174816681)
                    ·
                      refine ⟨1983227628434742881112511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2644303504579657174816681 1983227628434742881112511)
                      ·
                        rfl

theorem cell23_3862322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2].length) (baseStart_3862322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862322 prefixEnd_3862322 := by exact prefixLift 3862322
  have htrace : WordTrace (prefixWord ++ tailWord_3862322) baseStart_3862322 baseEnd_3862322 := by
    simpa [prefixWord, tailWord_3862322, baseEnd_3862322] using wordTrace_append hprefix tailTrace_3862322
  have hstable : (prefixWord ++ tailWord_3862322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862322).length < 2 ^ (prefixWord ++ tailWord_3862322).sum := by decide
  have hdescent : baseEnd_3862322 < baseStart_3862322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862451 : List Nat := [1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 4]
def baseStart_3862451 : Nat := 118140960795 + 3862451 * 2 ^ 59
def prefixEnd_3862451 : Nat := 4983230072969 + 3 ^ 40 * 3862451 * 2
def baseEnd_3862451 : Nat := 1983293867439172876399417

theorem tailTrace_3862451 : CollatzResearch.WordTrace tailWord_3862451 prefixEnd_3862451 1983293867439172876399417 := by
  unfold tailWord_3862451
  simp only [CollatzResearch.WordTrace]
  refine ⟨140875161330007155958163207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93916774220004770638775471 140875161330007155958163207)
  ·
    refine ⟨211312741995010733937244811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140875161330007155958163207 211312741995010733937244811)
    ·
      refine ⟨316969112992516100905867217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211312741995010733937244811 316969112992516100905867217)
      ·
        refine ⟨237726834744387075679400413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316969112992516100905867217 237726834744387075679400413)
        ·
          refine ⟨89147563029145153379775155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237726834744387075679400413 89147563029145153379775155)
          ·
            refine ⟨133721344543717730069662733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89147563029145153379775155 133721344543717730069662733)
            ·
              refine ⟨50145504203894148776123525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133721344543717730069662733 50145504203894148776123525)
              ·
                refine ⟨9402282038230152895523161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50145504203894148776123525 9402282038230152895523161)
                ·
                  refine ⟨7051711528672614671642371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9402282038230152895523161 7051711528672614671642371)
                  ·
                    refine ⟨10577567293008922007463557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7051711528672614671642371 10577567293008922007463557)
                    ·
                      refine ⟨1983293867439172876399417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10577567293008922007463557 1983293867439172876399417)
                      ·
                        rfl

theorem cell23_3862451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 4].length) (baseStart_3862451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862451 prefixEnd_3862451 := by exact prefixLift 3862451
  have htrace : WordTrace (prefixWord ++ tailWord_3862451) baseStart_3862451 baseEnd_3862451 := by
    simpa [prefixWord, tailWord_3862451, baseEnd_3862451] using wordTrace_append hprefix tailTrace_3862451
  have hstable : (prefixWord ++ tailWord_3862451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862451).length < 2 ^ (prefixWord ++ tailWord_3862451).sum := by decide
  have hdescent : baseEnd_3862451 < baseStart_3862451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862452 : List Nat := [2, 5, 2, 1, 2, 1, 1, 4, 5]
def baseStart_3862452 : Nat := 118140960795 + 3862452 * 2 ^ 59
def prefixEnd_3862452 : Nat := 4983230072969 + 3 ^ 40 * 3862452 * 2
def baseEnd_3862452 : Nat := 220366042324425263609657

theorem tailTrace_3862452 : CollatzResearch.WordTrace tailWord_3862452 prefixEnd_3862452 220366042324425263609657 := by
  unfold tailWord_3862452
  simp only [CollatzResearch.WordTrace]
  refine ⟨70437598901501766564474805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93916798535335688752633073 70437598901501766564474805)
  ·
    refine ⟨6603524897015790615419513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70437598901501766564474805 6603524897015790615419513)
    ·
      refine ⟨4952643672761842961564635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6603524897015790615419513 4952643672761842961564635)
      ·
        refine ⟨7428965509142764442346953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4952643672761842961564635 7428965509142764442346953)
        ·
          refine ⟨5571724131857073331760215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7428965509142764442346953 5571724131857073331760215)
          ·
            refine ⟨8357586197785609997640323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5571724131857073331760215 8357586197785609997640323)
            ·
              refine ⟨12536379296678414996460485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8357586197785609997640323 12536379296678414996460485)
              ·
                refine ⟨2350571118127202811836341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12536379296678414996460485 2350571118127202811836341)
                ·
                  refine ⟨220366042324425263609657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2350571118127202811836341 220366042324425263609657)
                  ·
                    rfl

theorem cell23_3862452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_3862452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862452 prefixEnd_3862452 := by exact prefixLift 3862452
  have htrace : WordTrace (prefixWord ++ tailWord_3862452) baseStart_3862452 baseEnd_3862452 := by
    simpa [prefixWord, tailWord_3862452, baseEnd_3862452] using wordTrace_append hprefix tailTrace_3862452
  have hstable : (prefixWord ++ tailWord_3862452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862452).length < 2 ^ (prefixWord ++ tailWord_3862452).sum := by decide
  have hdescent : baseEnd_3862452 < baseStart_3862452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862471 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 3]
def baseStart_3862471 : Nat := 118140960795 + 3862471 * 2 ^ 59
def prefixEnd_3862471 : Nat := 4983230072969 + 3 ^ 40 * 3862471 * 2
def baseEnd_3862471 : Nat := 1983304137052262798149325

theorem tailTrace_3862471 : CollatzResearch.WordTrace tailWord_3862471 prefixEnd_3862471 1983304137052262798149325 := by
  unfold tailWord_3862471
  simp only [CollatzResearch.WordTrace]
  refine ⟨140875890789934699373891267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93917260526623132915927511 140875890789934699373891267)
  ·
    refine ⟨211313836184902049060836901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140875890789934699373891267 211313836184902049060836901)
    ·
      refine ⟨39621344284669134198906919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211313836184902049060836901 39621344284669134198906919)
      ·
        refine ⟨59432016427003701298360379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39621344284669134198906919 59432016427003701298360379)
        ·
          refine ⟨89148024640505551947540569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59432016427003701298360379 89148024640505551947540569)
          ·
            refine ⟨66861018480379163960655427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89148024640505551947540569 66861018480379163960655427)
            ·
              refine ⟨100291527720568745940983141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66861018480379163960655427 100291527720568745940983141)
              ·
                refine ⟨18804661447606639863934339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100291527720568745940983141 18804661447606639863934339)
                ·
                  refine ⟨28206992171409959795901509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18804661447606639863934339 28206992171409959795901509)
                  ·
                    refine ⟨5288811032139367461731533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28206992171409959795901509 5288811032139367461731533)
                    ·
                      refine ⟨1983304137052262798149325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5288811032139367461731533 1983304137052262798149325)
                      ·
                        rfl

theorem cell23_3862471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_3862471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862471 prefixEnd_3862471 := by exact prefixLift 3862471
  have htrace : WordTrace (prefixWord ++ tailWord_3862471) baseStart_3862471 baseEnd_3862471 := by
    simpa [prefixWord, tailWord_3862471, baseEnd_3862471] using wordTrace_append hprefix tailTrace_3862471
  have hstable : (prefixWord ++ tailWord_3862471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862471).length < 2 ^ (prefixWord ++ tailWord_3862471).sum := by decide
  have hdescent : baseEnd_3862471 < baseStart_3862471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862478 : List Nat := [4, 1, 1, 1, 2, 2, 3, 2, 3, 4]
def baseStart_3862478 : Nat := 118140960795 + 3862478 * 2 ^ 59
def prefixEnd_3862478 : Nat := 4983230072969 + 3 ^ 40 * 3862478 * 2
def baseEnd_3862478 : Nat := 661102577138948090253931

theorem tailTrace_3862478 : CollatzResearch.WordTrace tailWord_3862478 prefixEnd_3862478 661102577138948090253931 := by
  unfold tailWord_3862478
  simp only [CollatzResearch.WordTrace]
  refine ⟨17609518262613667446174511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93917430733939559712930725 17609518262613667446174511)
  ·
    refine ⟨26414277393920501169261767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17609518262613667446174511 26414277393920501169261767)
    ·
      refine ⟨39621416090880751753892651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26414277393920501169261767 39621416090880751753892651)
      ·
        refine ⟨59432124136321127630838977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39621416090880751753892651 59432124136321127630838977)
        ·
          refine ⟨44574093102240845723129233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59432124136321127630838977 44574093102240845723129233)
          ·
            refine ⟨33430569826680634292346925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44574093102240845723129233 33430569826680634292346925)
            ·
              refine ⟨12536463685005237859630097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33430569826680634292346925 12536463685005237859630097)
              ·
                refine ⟨9402347763753928394722573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12536463685005237859630097 9402347763753928394722573)
                ·
                  refine ⟨3525880411407723148020965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9402347763753928394722573 3525880411407723148020965)
                  ·
                    refine ⟨661102577138948090253931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3525880411407723148020965 661102577138948090253931)
                    ·
                      rfl

theorem cell23_3862478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_3862478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862478 prefixEnd_3862478 := by exact prefixLift 3862478
  have htrace : WordTrace (prefixWord ++ tailWord_3862478) baseStart_3862478 baseEnd_3862478 := by
    simpa [prefixWord, tailWord_3862478, baseEnd_3862478] using wordTrace_append hprefix tailTrace_3862478
  have hstable : (prefixWord ++ tailWord_3862478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862478).length < 2 ^ (prefixWord ++ tailWord_3862478).sum := by decide
  have hdescent : baseEnd_3862478 < baseStart_3862478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862482 : List Nat := [3, 2, 2, 3, 3, 1, 1, 1, 2, 5]
def baseStart_3862482 : Nat := 118140960795 + 3862482 * 2 ^ 59
def prefixEnd_3862482 : Nat := 4983230072969 + 3 ^ 40 * 3862482 * 2
def baseEnd_3862482 : Nat := 661103261779820751703925

theorem tailTrace_3862482 : CollatzResearch.WordTrace tailWord_3862482 prefixEnd_3862482 661103261779820751703925 := by
  unfold tailWord_3862482
  simp only [CollatzResearch.WordTrace]
  refine ⟨35219072998223712063135425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93917527995263232168361133 35219072998223712063135425)
  ·
    refine ⟨26414304748667784047351569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35219072998223712063135425 26414304748667784047351569)
    ·
      refine ⟨19810728561500838035513677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26414304748667784047351569 19810728561500838035513677)
      ·
        refine ⟨7429023210562814263317629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19810728561500838035513677 7429023210562814263317629)
        ·
          refine ⟨2785883703961055348744111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7429023210562814263317629 2785883703961055348744111)
          ·
            refine ⟨4178825555941583023116167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2785883703961055348744111 4178825555941583023116167)
            ·
              refine ⟨6268238333912374534674251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4178825555941583023116167 6268238333912374534674251)
              ·
                refine ⟨9402357500868561802011377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6268238333912374534674251 9402357500868561802011377)
                ·
                  refine ⟨7051768125651421351508533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9402357500868561802011377 7051768125651421351508533)
                  ·
                    refine ⟨661103261779820751703925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7051768125651421351508533 661103261779820751703925)
                    ·
                      rfl

theorem cell23_3862482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_3862482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862482 prefixEnd_3862482 := by exact prefixLift 3862482
  have htrace : WordTrace (prefixWord ++ tailWord_3862482) baseStart_3862482 baseEnd_3862482 := by
    simpa [prefixWord, tailWord_3862482, baseEnd_3862482] using wordTrace_append hprefix tailTrace_3862482
  have hstable : (prefixWord ++ tailWord_3862482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862482).length < 2 ^ (prefixWord ++ tailWord_3862482).sum := by decide
  have hdescent : baseEnd_3862482 < baseStart_3862482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862485 : List Nat := [1, 3, 2, 3, 2, 3, 1, 1, 2, 1, 4]
def baseStart_3862485 : Nat := 118140960795 + 3862485 * 2 ^ 59
def prefixEnd_3862485 : Nat := 4983230072969 + 3 ^ 40 * 3862485 * 2
def baseEnd_3862485 : Nat := 1983311325781425743374261

theorem tailTrace_3862485 : CollatzResearch.WordTrace tailWord_3862485 prefixEnd_3862485 1983311325781425743374261 := by
  unfold tailWord_3862485
  simp only [CollatzResearch.WordTrace]
  refine ⟨140876401411883979764900909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93917600941255986509933939 140876401411883979764900909)
  ·
    refine ⟨52828650529456492411837841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140876401411883979764900909 52828650529456492411837841)
    ·
      refine ⟨39621487897092369308878381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52828650529456492411837841 39621487897092369308878381)
      ·
        refine ⟨14858057961409638490829393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39621487897092369308878381 14858057961409638490829393)
        ·
          refine ⟨11143543471057228868122045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14858057961409638490829393 11143543471057228868122045)
          ·
            refine ⟨4178828801646460825545767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11143543471057228868122045 4178828801646460825545767)
            ·
              refine ⟨6268243202469691238318651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4178828801646460825545767 6268243202469691238318651)
              ·
                refine ⟨9402364803704536857477977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6268243202469691238318651 9402364803704536857477977)
                ·
                  refine ⟨7051773602778402643108483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9402364803704536857477977 7051773602778402643108483)
                  ·
                    refine ⟨10577660404167603964662725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7051773602778402643108483 10577660404167603964662725)
                    ·
                      refine ⟨1983311325781425743374261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10577660404167603964662725 1983311325781425743374261)
                      ·
                        rfl

theorem cell23_3862485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_3862485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862485 prefixEnd_3862485 := by exact prefixLift 3862485
  have htrace : WordTrace (prefixWord ++ tailWord_3862485) baseStart_3862485 baseEnd_3862485 := by
    simpa [prefixWord, tailWord_3862485, baseEnd_3862485] using wordTrace_append hprefix tailTrace_3862485
  have hstable : (prefixWord ++ tailWord_3862485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862485).length < 2 ^ (prefixWord ++ tailWord_3862485).sum := by decide
  have hdescent : baseEnd_3862485 < baseStart_3862485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862495 : List Nat := [1, 1, 2, 3, 4, 1, 1, 5, 1, 4]
def baseStart_3862495 : Nat := 118140960795 + 3862495 * 2 ^ 59
def prefixEnd_3862495 : Nat := 4983230072969 + 3 ^ 40 * 3862495 * 2
def baseEnd_3862495 : Nat := 661105486862656901416405

theorem tailTrace_3862495 : CollatzResearch.WordTrace tailWord_3862495 prefixEnd_3862495 661105486862656901416405 := by
  unfold tailWord_3862495
  simp only [CollatzResearch.WordTrace]
  refine ⟨140876766141847751472764939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93917844094565167648509959 140876766141847751472764939)
  ·
    refine ⟨211315149212771627209147409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140876766141847751472764939 211315149212771627209147409)
    ·
      refine ⟨158486361909578720406860557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211315149212771627209147409 158486361909578720406860557)
      ·
        refine ⟨59432385716092020152572709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158486361909578720406860557 59432385716092020152572709)
        ·
          refine ⟨11143572321767253778607383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59432385716092020152572709 11143572321767253778607383)
          ·
            refine ⟨16715358482650880667911075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11143572321767253778607383 16715358482650880667911075)
            ·
              refine ⟨25073037723976321001866613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16715358482650880667911075 25073037723976321001866613)
              ·
                refine ⟨2350597286622780093924995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25073037723976321001866613 2350597286622780093924995)
                ·
                  refine ⟨3525895929934170140887493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2350597286622780093924995 3525895929934170140887493)
                  ·
                    refine ⟨661105486862656901416405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3525895929934170140887493 661105486862656901416405)
                    ·
                      rfl

theorem cell23_3862495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 1, 4].length) (baseStart_3862495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862495 prefixEnd_3862495 := by exact prefixLift 3862495
  have htrace : WordTrace (prefixWord ++ tailWord_3862495) baseStart_3862495 baseEnd_3862495 := by
    simpa [prefixWord, tailWord_3862495, baseEnd_3862495] using wordTrace_append hprefix tailTrace_3862495
  have hstable : (prefixWord ++ tailWord_3862495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862495).length < 2 ^ (prefixWord ++ tailWord_3862495).sum := by decide
  have hdescent : baseEnd_3862495 < baseStart_3862495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862528 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 6, 3, 2]
def baseStart_3862528 : Nat := 118140960795 + 3862528 * 2 ^ 59
def prefixEnd_3862528 : Nat := 4983230072969 + 3 ^ 40 * 3862528 * 2
def baseEnd_3862528 : Nat := 1983333405449569075136563

theorem tailTrace_3862528 : CollatzResearch.WordTrace tailWord_3862528 prefixEnd_3862528 1983333405449569075136563 := by
  unfold tailWord_3862528
  simp only [CollatzResearch.WordTrace]
  refine ⟨70438984875364099054358119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93918646500485465405810825 70438984875364099054358119)
  ·
    refine ⟨105658477313046148581537179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70438984875364099054358119 105658477313046148581537179)
    ·
      refine ⟨158487715969569222872305769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105658477313046148581537179 158487715969569222872305769)
      ·
        refine ⟨118865786977176917154229327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158487715969569222872305769 118865786977176917154229327)
        ·
          refine ⟨178298680465765375731343991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118865786977176917154229327 178298680465765375731343991)
          ·
            refine ⟨267448020698648063597015987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178298680465765375731343991 267448020698648063597015987)
            ·
              refine ⟨401172031047972095395523981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267448020698648063597015987 401172031047972095395523981)
              ·
                refine ⟨150439511642989535773321493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 401172031047972095395523981 150439511642989535773321493)
                ·
                  refine ⟨7051852108265134489374445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150439511642989535773321493 7051852108265134489374445)
                  ·
                    refine ⟨2644444540599425433515417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7051852108265134489374445 2644444540599425433515417)
                    ·
                      refine ⟨1983333405449569075136563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2644444540599425433515417 1983333405449569075136563)
                      ·
                        rfl

theorem cell23_3862528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 6, 3, 2].length) (baseStart_3862528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862528 prefixEnd_3862528 := by exact prefixLift 3862528
  have htrace : WordTrace (prefixWord ++ tailWord_3862528) baseStart_3862528 baseEnd_3862528 := by
    simpa [prefixWord, tailWord_3862528, baseEnd_3862528] using wordTrace_append hprefix tailTrace_3862528
  have hstable : (prefixWord ++ tailWord_3862528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862528).length < 2 ^ (prefixWord ++ tailWord_3862528).sum := by decide
  have hdescent : baseEnd_3862528 < baseStart_3862528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862535 : List Nat := [1, 1, 4, 3, 1, 2, 2, 2, 3, 1, 3]
def baseStart_3862535 : Nat := 118140960795 + 3862535 * 2 ^ 59
def prefixEnd_3862535 : Nat := 4983230072969 + 3 ^ 40 * 3862535 * 2
def baseEnd_3862535 : Nat := 1983336999814150547749031

theorem tailTrace_3862535 : CollatzResearch.WordTrace tailWord_3862535 prefixEnd_3862535 1983336999814150547749031 := by
  unfold tailWord_3862535
  simp only [CollatzResearch.WordTrace]
  refine ⟨140878225061702838304221059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93918816707801892202814039 140878225061702838304221059)
  ·
    refine ⟨211317337592554257456331589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140878225061702838304221059 211317337592554257456331589)
    ·
      refine ⟨39622000798603923273062173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211317337592554257456331589 39622000798603923273062173)
      ·
        refine ⟨14858250299476471227398315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39622000798603923273062173 14858250299476471227398315)
        ·
          refine ⟨22287375449214706841097473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14858250299476471227398315 22287375449214706841097473)
          ·
            refine ⟨16715531586911030130823105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22287375449214706841097473 16715531586911030130823105)
            ·
              refine ⟨12536648690183272598117329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16715531586911030130823105 12536648690183272598117329)
              ·
                refine ⟨9402486517637454448587997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12536648690183272598117329 9402486517637454448587997)
                ·
                  refine ⟨3525932444114045418220499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9402486517637454448587997 3525932444114045418220499)
                  ·
                    refine ⟨5288898666171068127330749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3525932444114045418220499 5288898666171068127330749)
                    ·
                      refine ⟨1983336999814150547749031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5288898666171068127330749 1983336999814150547749031)
                      ·
                        rfl

theorem cell23_3862535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_3862535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862535 prefixEnd_3862535 := by exact prefixLift 3862535
  have htrace : WordTrace (prefixWord ++ tailWord_3862535) baseStart_3862535 baseEnd_3862535 := by
    simpa [prefixWord, tailWord_3862535, baseEnd_3862535] using wordTrace_append hprefix tailTrace_3862535
  have hstable : (prefixWord ++ tailWord_3862535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862535).length < 2 ^ (prefixWord ++ tailWord_3862535).sum := by decide
  have hdescent : baseEnd_3862535 < baseStart_3862535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862571 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 4]
def baseStart_3862571 : Nat := 118140960795 + 3862571 * 2 ^ 59
def prefixEnd_3862571 : Nat := 4983230072969 + 3 ^ 40 * 3862571 * 2
def baseEnd_3862571 : Nat := 1983355485117712406898865

theorem tailTrace_3862571 : CollatzResearch.WordTrace tailWord_3862571 prefixEnd_3862571 1983355485117712406898865 := by
  unfold tailWord_3862571
  simp only [CollatzResearch.WordTrace]
  refine ⟨140879538089572416452531567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93919692059714944301687711 140879538089572416452531567)
  ·
    refine ⟨211319307134358624678797351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140879538089572416452531567 211319307134358624678797351)
    ·
      refine ⟨316978960701537937018196027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211319307134358624678797351 316978960701537937018196027)
      ·
        refine ⟨475468441052306905527294041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316978960701537937018196027 475468441052306905527294041)
        ·
          refine ⟨356601330789230179145470531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475468441052306905527294041 356601330789230179145470531)
          ·
            refine ⟨534901996183845268718205797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356601330789230179145470531 534901996183845268718205797)
            ·
              refine ⟨100294124284470987884663587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 534901996183845268718205797 100294124284470987884663587)
              ·
                refine ⟨150441186426706481826995381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100294124284470987884663587 150441186426706481826995381)
                ·
                  refine ⟨14103861227503732671280817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150441186426706481826995381 14103861227503732671280817)
                  ·
                    refine ⟨10577895920627799503460613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14103861227503732671280817 10577895920627799503460613)
                    ·
                      refine ⟨1983355485117712406898865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10577895920627799503460613 1983355485117712406898865)
                      ·
                        rfl

theorem cell23_3862571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 4].length) (baseStart_3862571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862571 prefixEnd_3862571 := by exact prefixLift 3862571
  have htrace : WordTrace (prefixWord ++ tailWord_3862571) baseStart_3862571 baseEnd_3862571 := by
    simpa [prefixWord, tailWord_3862571, baseEnd_3862571] using wordTrace_append hprefix tailTrace_3862571
  have hstable : (prefixWord ++ tailWord_3862571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862571).length < 2 ^ (prefixWord ++ tailWord_3862571).sum := by decide
  have hdescent : baseEnd_3862571 < baseStart_3862571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862575 : List Nat := [1, 1, 2, 1, 2, 1, 1, 7, 3, 2, 2]
def baseStart_3862575 : Nat := 118140960795 + 3862575 * 2 ^ 59
def prefixEnd_3862575 : Nat := 4983230072969 + 3 ^ 40 * 3862575 * 2
def baseEnd_3862575 : Nat := 1983357539040330391248847

theorem tailTrace_3862575 : CollatzResearch.WordTrace tailWord_3862575 prefixEnd_3862575 1983357539040330391248847 := by
  unfold tailWord_3862575
  simp only [CollatzResearch.WordTrace]
  refine ⟨140879683981557925135677179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93919789321038616757118119 140879683981557925135677179)
  ·
    refine ⟨211319525972336887703515769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140879683981557925135677179 211319525972336887703515769)
    ·
      refine ⟨158489644479252665777636827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211319525972336887703515769 158489644479252665777636827)
      ·
        refine ⟨237734466718878998666455241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158489644479252665777636827 237734466718878998666455241)
        ·
          refine ⟨178300850039159248999841431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237734466718878998666455241 178300850039159248999841431)
          ·
            refine ⟨267451275058738873499762147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178300850039159248999841431 267451275058738873499762147)
            ·
              refine ⟨401176912588108310249643221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267451275058738873499762147 401176912588108310249643221)
              ·
                refine ⟨9402583888783788521476013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 401176912588108310249643221 9402583888783788521476013)
                ·
                  refine ⟨3525968958293920695553505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9402583888783788521476013 3525968958293920695553505)
                  ·
                    refine ⟨2644476718720440521665129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3525968958293920695553505 2644476718720440521665129)
                    ·
                      refine ⟨1983357539040330391248847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2644476718720440521665129 1983357539040330391248847)
                      ·
                        rfl

theorem cell23_3862575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 2, 2].length) (baseStart_3862575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862575 prefixEnd_3862575 := by exact prefixLift 3862575
  have htrace : WordTrace (prefixWord ++ tailWord_3862575) baseStart_3862575 baseEnd_3862575 := by
    simpa [prefixWord, tailWord_3862575, baseEnd_3862575] using wordTrace_append hprefix tailTrace_3862575
  have hstable : (prefixWord ++ tailWord_3862575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862575).length < 2 ^ (prefixWord ++ tailWord_3862575).sum := by decide
  have hdescent : baseEnd_3862575 < baseStart_3862575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862578 : List Nat := [3, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5]
def baseStart_3862578 : Nat := 118140960795 + 3862578 * 2 ^ 59
def prefixEnd_3862578 : Nat := 4983230072969 + 3 ^ 40 * 3862578 * 2
def baseEnd_3862578 : Nat := 1983359079482293879511333

theorem tailTrace_3862578 : CollatzResearch.WordTrace tailWord_3862578 prefixEnd_3862578 1983359079482293879511333 := by
  unfold tailWord_3862578
  simp only [CollatzResearch.WordTrace]
  refine ⟨35219948350136764162009097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93919862267031371098690925 35219948350136764162009097)
  ·
    refine ⟨26414961262602573121506823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35219948350136764162009097 26414961262602573121506823)
    ·
      refine ⟨39622441893903859682260235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26414961262602573121506823 39622441893903859682260235)
      ·
        refine ⟨59433662840855789523390353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39622441893903859682260235 59433662840855789523390353)
        ·
          refine ⟨44575247130641842142542765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59433662840855789523390353 44575247130641842142542765)
          ·
            refine ⟨16715717673990690803453537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44575247130641842142542765 16715717673990690803453537)
            ·
              refine ⟨12536788255493018102590153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16715717673990690803453537 12536788255493018102590153)
              ·
                refine ⟨9402591191619763576942615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12536788255493018102590153 9402591191619763576942615)
                ·
                  refine ⟨14103886787429645365413923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9402591191619763576942615 14103886787429645365413923)
                  ·
                    refine ⟨21155830181144468048120885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14103886787429645365413923 21155830181144468048120885)
                    ·
                      refine ⟨1983359079482293879511333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21155830181144468048120885 1983359079482293879511333)
                      ·
                        rfl

theorem cell23_3862578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_3862578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862578 prefixEnd_3862578 := by exact prefixLift 3862578
  have htrace : WordTrace (prefixWord ++ tailWord_3862578) baseStart_3862578 baseEnd_3862578 := by
    simpa [prefixWord, tailWord_3862578, baseEnd_3862578] using wordTrace_append hprefix tailTrace_3862578
  have hstable : (prefixWord ++ tailWord_3862578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862578).length < 2 ^ (prefixWord ++ tailWord_3862578).sum := by decide
  have hdescent : baseEnd_3862578 < baseStart_3862578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862581 : List Nat := [1, 3, 3, 1, 1, 1, 3, 10]
def baseStart_3862581 : Nat := 118140960795 + 3862581 * 2 ^ 59
def prefixEnd_3862581 : Nat := 4983230072969 + 3 ^ 40 * 3862581 * 2
def baseEnd_3862581 : Nat := 73457800737935458065697

theorem tailTrace_3862581 : CollatzResearch.WordTrace tailWord_3862581 prefixEnd_3862581 73457800737935458065697 := by
  unfold tailWord_3862581
  simp only [CollatzResearch.WordTrace]
  refine ⟨140879902819536188160395597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93919935213024125440263731 140879902819536188160395597)
  ·
    refine ⟨52829963557326070560148349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140879902819536188160395597 52829963557326070560148349)
    ·
      refine ⟨19811236333997276460055631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52829963557326070560148349 19811236333997276460055631)
      ·
        refine ⟨29716854500995914690083447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19811236333997276460055631 29716854500995914690083447)
        ·
          refine ⟨44575281751493872035125171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29716854500995914690083447 44575281751493872035125171)
          ·
            refine ⟨66862922627240808052687757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44575281751493872035125171 66862922627240808052687757)
            ·
              refine ⟨25073595985215303019757909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66862922627240808052687757 25073595985215303019757909)
              ·
                refine ⟨73457800737935458065697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25073595985215303019757909 73457800737935458065697)
                ·
                  rfl

theorem cell23_3862581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 10].length) (baseStart_3862581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862581 prefixEnd_3862581 := by exact prefixLift 3862581
  have htrace : WordTrace (prefixWord ++ tailWord_3862581) baseStart_3862581 baseEnd_3862581 := by
    simpa [prefixWord, tailWord_3862581, baseEnd_3862581] using wordTrace_append hprefix tailTrace_3862581
  have hstable : (prefixWord ++ tailWord_3862581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862581).length < 2 ^ (prefixWord ++ tailWord_3862581).sum := by decide
  have hdescent : baseEnd_3862581 < baseStart_3862581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862588 : List Nat := [2, 2, 2, 2, 2, 1, 2, 3, 1, 2, 4]
def baseStart_3862588 : Nat := 118140960795 + 3862588 * 2 ^ 59
def prefixEnd_3862588 : Nat := 4983230072969 + 3 ^ 40 * 3862588 * 2
def baseEnd_3862588 : Nat := 1983364214288838840386287

theorem tailTrace_3862588 : CollatzResearch.WordTrace tailWord_3862588 prefixEnd_3862588 1983364214288838840386287 := by
  unfold tailWord_3862588
  simp only [CollatzResearch.WordTrace]
  refine ⟨70440079065255414177950209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93920105420340552237266945 70440079065255414177950209)
  ·
    refine ⟨52830059298941560633462657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70440079065255414177950209 52830059298941560633462657)
    ·
      refine ⟨39622544474206170475096993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52830059298941560633462657 39622544474206170475096993)
      ·
        refine ⟨29716908355654627856322745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39622544474206170475096993 29716908355654627856322745)
        ·
          refine ⟨22287681266740970892242059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29716908355654627856322745 22287681266740970892242059)
          ·
            refine ⟨33431521900111456338363089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22287681266740970892242059 33431521900111456338363089)
            ·
              refine ⟨25073641425083592253772317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33431521900111456338363089 25073641425083592253772317)
              ·
                refine ⟨9402615534406347095164619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25073641425083592253772317 9402615534406347095164619)
                ·
                  refine ⟨14103923301609520642746929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9402615534406347095164619 14103923301609520642746929)
                  ·
                    refine ⟨10577942476207140482060197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14103923301609520642746929 10577942476207140482060197)
                    ·
                      refine ⟨1983364214288838840386287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10577942476207140482060197 1983364214288838840386287)
                      ·
                        rfl

theorem cell23_3862588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_3862588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862588 prefixEnd_3862588 := by exact prefixLift 3862588
  have htrace : WordTrace (prefixWord ++ tailWord_3862588) baseStart_3862588 baseEnd_3862588 := by
    simpa [prefixWord, tailWord_3862588, baseEnd_3862588] using wordTrace_append hprefix tailTrace_3862588
  have hstable : (prefixWord ++ tailWord_3862588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862588).length < 2 ^ (prefixWord ++ tailWord_3862588).sum := by decide
  have hdescent : baseEnd_3862588 < baseStart_3862588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862605 : List Nat := [1, 6, 1, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_3862605 : Nat := 118140960795 + 3862605 * 2 ^ 59
def prefixEnd_3862605 : Nat := 4983230072969 + 3 ^ 40 * 3862605 * 2
def baseEnd_3862605 : Nat := 1983372943459965273873709

theorem tailTrace_3862605 : CollatzResearch.WordTrace tailWord_3862605 prefixEnd_3862605 1983372943459965273873709 := by
  unfold tailWord_3862605
  simp only [CollatzResearch.WordTrace]
  refine ⟨140880778171449240259269269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93920518780966160172846179 140880778171449240259269269)
  ·
    refine ⟨6603786476786683137153247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 140880778171449240259269269 6603786476786683137153247)
    ·
      refine ⟨9905679715180024705729871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6603786476786683137153247 9905679715180024705729871)
      ·
        refine ⟨14858519572770037058594807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9905679715180024705729871 14858519572770037058594807)
        ·
          refine ⟨22287779359155055587892211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14858519572770037058594807 22287779359155055587892211)
          ·
            refine ⟨33431669038732583381838317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22287779359155055587892211 33431669038732583381838317)
            ·
              refine ⟨12536875889524718768189369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33431669038732583381838317 12536875889524718768189369)
              ·
                refine ⟨9402656917143539076142027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12536875889524718768189369 9402656917143539076142027)
                ·
                  refine ⟨14103985375715308614213041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9402656917143539076142027 14103985375715308614213041)
                  ·
                    refine ⟨10577989031786481460659781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14103985375715308614213041 10577989031786481460659781)
                    ·
                      refine ⟨1983372943459965273873709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10577989031786481460659781 1983372943459965273873709)
                      ·
                        rfl

theorem cell23_3862605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_3862605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862605 prefixEnd_3862605 := by exact prefixLift 3862605
  have htrace : WordTrace (prefixWord ++ tailWord_3862605) baseStart_3862605 baseEnd_3862605 := by
    simpa [prefixWord, tailWord_3862605, baseEnd_3862605] using wordTrace_append hprefix tailTrace_3862605
  have hstable : (prefixWord ++ tailWord_3862605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862605).length < 2 ^ (prefixWord ++ tailWord_3862605).sum := by decide
  have hdescent : baseEnd_3862605 < baseStart_3862605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862642 : List Nat := [3, 2, 1, 2, 2, 2, 2, 3, 2, 1, 3]
def baseStart_3862642 : Nat := 118140960795 + 3862642 * 2 ^ 59
def prefixEnd_3862642 : Nat := 4983230072969 + 3 ^ 40 * 3862642 * 2
def baseEnd_3862642 : Nat := 1983391942244181629111039

theorem tailTrace_3862642 : CollatzResearch.WordTrace tailWord_3862642 prefixEnd_3862642 1983391942244181629111039 := by
  unfold tailWord_3862642
  simp only [CollatzResearch.WordTrace]
  refine ⟨35220531918078798894591545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93921418448210130385577453 35220531918078798894591545)
  ·
    refine ⟨26415398938559099170943659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35220531918078798894591545 26415398938559099170943659)
    ·
      refine ⟨39623098407838648756415489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26415398938559099170943659 39623098407838648756415489)
      ·
        refine ⟨29717323805878986567311617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39623098407838648756415489 29717323805878986567311617)
        ·
          refine ⟨22287992854409239925483713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29717323805878986567311617 22287992854409239925483713)
          ·
            refine ⟨16715994640806929944112785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22287992854409239925483713 16715994640806929944112785)
            ·
              refine ⟨12536995980605197458084589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16715994640806929944112785 12536995980605197458084589)
              ·
                refine ⟨4701373492726949046781721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12536995980605197458084589 4701373492726949046781721)
                ·
                  refine ⟨3526030119545211785086291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4701373492726949046781721 3526030119545211785086291)
                  ·
                    refine ⟨5289045179317817677629437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3526030119545211785086291 5289045179317817677629437)
                    ·
                      refine ⟨1983391942244181629111039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5289045179317817677629437 1983391942244181629111039)
                      ·
                        rfl

theorem cell23_3862642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_3862642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862642 prefixEnd_3862642 := by exact prefixLift 3862642
  have htrace : WordTrace (prefixWord ++ tailWord_3862642) baseStart_3862642 baseEnd_3862642 := by
    simpa [prefixWord, tailWord_3862642, baseEnd_3862642] using wordTrace_append hprefix tailTrace_3862642
  have hstable : (prefixWord ++ tailWord_3862642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862642).length < 2 ^ (prefixWord ++ tailWord_3862642).sum := by decide
  have hdescent : baseEnd_3862642 < baseStart_3862642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862665 : List Nat := [1, 2, 1, 1, 4, 2, 1, 4, 1, 4, 2]
def baseStart_3862665 : Nat := 118140960795 + 3862665 * 2 ^ 59
def prefixEnd_3862665 : Nat := 4983230072969 + 3 ^ 40 * 3862665 * 2
def baseEnd_3862665 : Nat := 1983403752299235039123433

theorem tailTrace_3862665 : CollatzResearch.WordTrace tailWord_3862665 prefixEnd_3862665 1983403752299235039123433 := by
  unfold tailWord_3862665
  simp only [CollatzResearch.WordTrace]
  refine ⟨140882966551231870506453449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93921977700821247004302299 140882966551231870506453449)
  ·
    refine ⟨105662224913423902879840087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140882966551231870506453449 105662224913423902879840087)
    ·
      refine ⟨158493337370135854319760131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105662224913423902879840087 158493337370135854319760131)
      ·
        refine ⟨237740006055203781479640197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158493337370135854319760131 237740006055203781479640197)
        ·
          refine ⟨44576251135350709027432537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237740006055203781479640197 44576251135350709027432537)
          ·
            refine ⟨33432188351513031770574403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44576251135350709027432537 33432188351513031770574403)
            ·
              refine ⟨50148282527269547655861605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33432188351513031770574403 50148282527269547655861605)
              ·
                refine ⟨9402802973863040185474051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50148282527269547655861605 9402802973863040185474051)
                ·
                  refine ⟨14104204460794560278211077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9402802973863040185474051 14104204460794560278211077)
                  ·
                    refine ⟨2644538336398980052164577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14104204460794560278211077 2644538336398980052164577)
                    ·
                      refine ⟨1983403752299235039123433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2644538336398980052164577 1983403752299235039123433)
                      ·
                        rfl

theorem cell23_3862665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 4, 2].length) (baseStart_3862665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862665 prefixEnd_3862665 := by exact prefixLift 3862665
  have htrace : WordTrace (prefixWord ++ tailWord_3862665) baseStart_3862665 baseEnd_3862665 := by
    simpa [prefixWord, tailWord_3862665, baseEnd_3862665] using wordTrace_append hprefix tailTrace_3862665
  have hstable : (prefixWord ++ tailWord_3862665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862665).length < 2 ^ (prefixWord ++ tailWord_3862665).sum := by decide
  have hdescent : baseEnd_3862665 < baseStart_3862665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862688 : List Nat := [2, 1, 1, 4, 2, 2, 1, 3, 7]
def baseStart_3862688 : Nat := 118140960795 + 3862688 * 2 ^ 59
def prefixEnd_3862688 : Nat := 4983230072969 + 3 ^ 40 * 3862688 * 2
def baseEnd_3862688 : Nat := 220379506928254272126203

theorem tailTrace_3862688 : CollatzResearch.WordTrace tailWord_3862688 prefixEnd_3862688 220379506928254272126203 := by
  unfold tailWord_3862688
  simp only [CollatzResearch.WordTrace]
  refine ⟨70441902715074272717270359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93922536953432363623027145 70441902715074272717270359)
  ·
    refine ⟨105662854072611409075905539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70441902715074272717270359 105662854072611409075905539)
    ·
      refine ⟨158494281108917113613858309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105662854072611409075905539 158494281108917113613858309)
      ·
        refine ⟨29717677707921958802598433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158494281108917113613858309 29717677707921958802598433)
        ·
          refine ⟨22288258280941469101948825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29717677707921958802598433 22288258280941469101948825)
          ·
            refine ⟨16716193710706101826461619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22288258280941469101948825 16716193710706101826461619)
            ·
              refine ⟨25074290566059152739692429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16716193710706101826461619 25074290566059152739692429)
              ·
                refine ⟨9402858962272182277384661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25074290566059152739692429 9402858962272182277384661)
                ·
                  refine ⟨220379506928254272126203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9402858962272182277384661 220379506928254272126203)
                  ·
                    rfl

theorem cell23_3862688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 7].length) (baseStart_3862688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862688 prefixEnd_3862688 := by exact prefixLift 3862688
  have htrace : WordTrace (prefixWord ++ tailWord_3862688) baseStart_3862688 baseEnd_3862688 := by
    simpa [prefixWord, tailWord_3862688, baseEnd_3862688] using wordTrace_append hprefix tailTrace_3862688
  have hstable : (prefixWord ++ tailWord_3862688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862688).length < 2 ^ (prefixWord ++ tailWord_3862688).sum := by decide
  have hdescent : baseEnd_3862688 < baseStart_3862688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862728 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 1, 2, 5]
def baseStart_3862728 : Nat := 118140960795 + 3862728 * 2 ^ 59
def prefixEnd_3862728 : Nat := 4983230072969 + 3 ^ 40 * 3862728 * 2
def baseEnd_3862728 : Nat := 1983436101580468292635643

theorem tailTrace_3862728 : CollatzResearch.WordTrace tailWord_3862728 prefixEnd_3862728 1983436101580468292635643 := by
  unfold tailWord_3862728
  simp only [CollatzResearch.WordTrace]
  refine ⟨70442632175001816132998419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93923509566669088177331225 70442632175001816132998419)
  ·
    refine ⟨105663948262502724199497629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70442632175001816132998419 105663948262502724199497629)
    ·
      refine ⟨39623980598438521574811611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105663948262502724199497629 39623980598438521574811611)
      ·
        refine ⟨59435970897657782362217417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39623980598438521574811611 59435970897657782362217417)
        ·
          refine ⟨44576978173243336771663063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59435970897657782362217417 44576978173243336771663063)
          ·
            refine ⟨66865467259865005157494595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44576978173243336771663063 66865467259865005157494595)
            ·
              refine ⟨100298200889797507736241893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66865467259865005157494595 100298200889797507736241893)
              ·
                refine ⟨18805912666837032700545355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100298200889797507736241893 18805912666837032700545355)
                ·
                  refine ⟨28208869000255549050818033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18805912666837032700545355 28208869000255549050818033)
                  ·
                    refine ⟨21156651750191661788113525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28208869000255549050818033 21156651750191661788113525)
                    ·
                      refine ⟨1983436101580468292635643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21156651750191661788113525 1983436101580468292635643)
                      ·
                        rfl

theorem cell23_3862728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_3862728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862728 prefixEnd_3862728 := by exact prefixLift 3862728
  have htrace : WordTrace (prefixWord ++ tailWord_3862728) baseStart_3862728 baseEnd_3862728 := by
    simpa [prefixWord, tailWord_3862728, baseEnd_3862728] using wordTrace_append hprefix tailTrace_3862728
  have hstable : (prefixWord ++ tailWord_3862728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862728).length < 2 ^ (prefixWord ++ tailWord_3862728).sum := by decide
  have hdescent : baseEnd_3862728 < baseStart_3862728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862768 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 4]
def baseStart_3862768 : Nat := 118140960795 + 3862768 * 2 ^ 59
def prefixEnd_3862768 : Nat := 4983230072969 + 3 ^ 40 * 3862768 * 2
def baseEnd_3862768 : Nat := 1983456640806648136135459

theorem tailTrace_3862768 : CollatzResearch.WordTrace tailWord_3862768 prefixEnd_3862768 1983456640806648136135459 := by
  unfold tailWord_3862768
  simp only [CollatzResearch.WordTrace]
  refine ⟨70443361634929359548726479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93924482179905812731635305 70443361634929359548726479)
  ·
    refine ⟨105665042452394039323089719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70443361634929359548726479 105665042452394039323089719)
    ·
      refine ⟨158497563678591058984634579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105665042452394039323089719 158497563678591058984634579)
      ·
        refine ⟨237746345517886588476951869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158497563678591058984634579 237746345517886588476951869)
        ·
          refine ⟨89154879569207470678856951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237746345517886588476951869 89154879569207470678856951)
          ·
            refine ⟨133732319353811206018285427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89154879569207470678856951 133732319353811206018285427)
            ·
              refine ⟨200598479030716809027428141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133732319353811206018285427 200598479030716809027428141)
              ·
                refine ⟨75224429636518803385285553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200598479030716809027428141 75224429636518803385285553)
                ·
                  refine ⟨56418322227389102538964165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75224429636518803385285553 56418322227389102538964165)
                  ·
                    refine ⟨10578435417635456726055781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56418322227389102538964165 10578435417635456726055781)
                    ·
                      refine ⟨1983456640806648136135459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10578435417635456726055781 1983456640806648136135459)
                      ·
                        rfl

theorem cell23_3862768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 4].length) (baseStart_3862768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862768 prefixEnd_3862768 := by exact prefixLift 3862768
  have htrace : WordTrace (prefixWord ++ tailWord_3862768) baseStart_3862768 baseEnd_3862768 := by
    simpa [prefixWord, tailWord_3862768, baseEnd_3862768] using wordTrace_append hprefix tailTrace_3862768
  have hstable : (prefixWord ++ tailWord_3862768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862768).length < 2 ^ (prefixWord ++ tailWord_3862768).sum := by decide
  have hdescent : baseEnd_3862768 < baseStart_3862768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862792 : List Nat := [2, 1, 3, 2, 3, 1, 2, 2, 2, 2, 3]
def baseStart_3862792 : Nat := 118140960795 + 3862792 * 2 ^ 59
def prefixEnd_3862792 : Nat := 4983230072969 + 3 ^ 40 * 3862792 * 2
def baseEnd_3862792 : Nat := 1983468964342356042235349

theorem tailTrace_3862792 : CollatzResearch.WordTrace tailWord_3862792 prefixEnd_3862792 1983468964342356042235349 := by
  unfold tailWord_3862792
  simp only [CollatzResearch.WordTrace]
  refine ⟨70443799310885885598163315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93925065747847847464217753 70443799310885885598163315)
  ·
    refine ⟨105665698966328828397244973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70443799310885885598163315 105665698966328828397244973)
    ·
      refine ⟨39624637112373310648966865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105665698966328828397244973 39624637112373310648966865)
      ·
        refine ⟨29718477834279982986725149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39624637112373310648966865 29718477834279982986725149)
        ·
          refine ⟨11144429187854993620021931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29718477834279982986725149 11144429187854993620021931)
          ·
            refine ⟨16716643781782490430032897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11144429187854993620021931 16716643781782490430032897)
            ·
              refine ⟨12537482836336867822524673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16716643781782490430032897 12537482836336867822524673)
              ·
                refine ⟨9403112127252650866893505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12537482836336867822524673 9403112127252650866893505)
                ·
                  refine ⟨7052334095439488150170129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9403112127252650866893505 7052334095439488150170129)
                  ·
                    refine ⟨5289250571579616112627597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7052334095439488150170129 5289250571579616112627597)
                    ·
                      refine ⟨1983468964342356042235349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5289250571579616112627597 1983468964342356042235349)
                      ·
                        rfl

theorem cell23_3862792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_3862792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862792 prefixEnd_3862792 := by exact prefixLift 3862792
  have htrace : WordTrace (prefixWord ++ tailWord_3862792) baseStart_3862792 baseEnd_3862792 := by
    simpa [prefixWord, tailWord_3862792, baseEnd_3862792] using wordTrace_append hprefix tailTrace_3862792
  have hstable : (prefixWord ++ tailWord_3862792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862792).length < 2 ^ (prefixWord ++ tailWord_3862792).sum := by decide
  have hdescent : baseEnd_3862792 < baseStart_3862792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862795 : List Nat := [1, 1, 1, 1, 5, 2, 4, 2, 6]
def baseStart_3862795 : Nat := 118140960795 + 3862795 * 2 ^ 59
def prefixEnd_3862795 : Nat := 4983230072969 + 3 ^ 40 * 3862795 * 2
def baseEnd_3862795 : Nat := 220385611642702170055315

theorem tailTrace_3862795 : CollatzResearch.WordTrace tailWord_3862795 prefixEnd_3862795 220385611642702170055315 := by
  unfold tailWord_3862795
  simp only [CollatzResearch.WordTrace]
  refine ⟨140887708040760902708685839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93925138693840601805790559 140887708040760902708685839)
  ·
    refine ⟨211331562061141354063028759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140887708040760902708685839 211331562061141354063028759)
    ·
      refine ⟨316997343091712031094543139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211331562061141354063028759 316997343091712031094543139)
      ·
        refine ⟨475496014637568046641814709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316997343091712031094543139 475496014637568046641814709)
        ·
          refine ⟨44577751372272004372670129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 475496014637568046641814709 44577751372272004372670129)
          ·
            refine ⟨33433313529204003279502597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44577751372272004372670129 33433313529204003279502597)
            ·
              refine ⟨6268746286725750614906737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33433313529204003279502597 6268746286725750614906737)
              ·
                refine ⟨4701559715044312961180053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6268746286725750614906737 4701559715044312961180053)
                ·
                  refine ⟨220385611642702170055315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4701559715044312961180053 220385611642702170055315)
                  ·
                    rfl

theorem cell23_3862795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 6].length) (baseStart_3862795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862795 prefixEnd_3862795 := by exact prefixLift 3862795
  have htrace : WordTrace (prefixWord ++ tailWord_3862795) baseStart_3862795 baseEnd_3862795 := by
    simpa [prefixWord, tailWord_3862795, baseEnd_3862795] using wordTrace_append hprefix tailTrace_3862795
  have hstable : (prefixWord ++ tailWord_3862795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862795).length < 2 ^ (prefixWord ++ tailWord_3862795).sum := by decide
  have hdescent : baseEnd_3862795 < baseStart_3862795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862823 : List Nat := [1, 1, 8, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_3862823 : Nat := 118140960795 + 3862823 * 2 ^ 59
def prefixEnd_3862823 : Nat := 4983230072969 + 3 ^ 40 * 3862823 * 2
def baseEnd_3862823 : Nat := 1983484882242645420947707

theorem tailTrace_3862823 : CollatzResearch.WordTrace tailWord_3862823 prefixEnd_3862823 1983484882242645420947707 := by
  unfold tailWord_3862823
  simp only [CollatzResearch.WordTrace]
  refine ⟨140888729284659463490705123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93925819523106308993803415 140888729284659463490705123)
  ·
    refine ⟨211333093926989195236057685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140888729284659463490705123 211333093926989195236057685)
    ·
      refine ⟨2476559694456904631672551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 211333093926989195236057685 2476559694456904631672551)
      ·
        refine ⟨3714839541685356947508827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2476559694456904631672551 3714839541685356947508827)
        ·
          refine ⟨5572259312528035421263241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3714839541685356947508827 5572259312528035421263241)
          ·
            refine ⟨4179194484396026565947431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5572259312528035421263241 4179194484396026565947431)
            ·
              refine ⟨6268791726594039848921147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4179194484396026565947431 6268791726594039848921147)
              ·
                refine ⟨9403187589891059773381721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6268791726594039848921147 9403187589891059773381721)
                ·
                  refine ⟨7052390692418294830036291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9403187589891059773381721 7052390692418294830036291)
                  ·
                    refine ⟨10578586038627442245054437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7052390692418294830036291 10578586038627442245054437)
                    ·
                      refine ⟨1983484882242645420947707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10578586038627442245054437 1983484882242645420947707)
                      ·
                        rfl

theorem cell23_3862823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_3862823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862823 prefixEnd_3862823 := by exact prefixLift 3862823
  have htrace : WordTrace (prefixWord ++ tailWord_3862823) baseStart_3862823 baseEnd_3862823 := by
    simpa [prefixWord, tailWord_3862823, baseEnd_3862823] using wordTrace_append hprefix tailTrace_3862823
  have hstable : (prefixWord ++ tailWord_3862823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862823).length < 2 ^ (prefixWord ++ tailWord_3862823).sum := by decide
  have hdescent : baseEnd_3862823 < baseStart_3862823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862826 : List Nat := [3, 1, 4, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_3862826 : Nat := 118140960795 + 3862826 * 2 ^ 59
def prefixEnd_3862826 : Nat := 4983230072969 + 3 ^ 40 * 3862826 * 2
def baseEnd_3862826 : Nat := 1983486422684608909210193

theorem tailTrace_3862826 : CollatzResearch.WordTrace tailWord_3862826 prefixEnd_3862826 1983486422684608909210193 := by
  unfold tailWord_3862826
  simp only [CollatzResearch.WordTrace]
  refine ⟨35222209675912148750766083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93925892469099063335376221 35222209675912148750766083)
  ·
    refine ⟨52833314513868223126149125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35222209675912148750766083 52833314513868223126149125)
    ·
      refine ⟨9906246471350291836152961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52833314513868223126149125 9906246471350291836152961)
      ·
        refine ⟨7429684853512718877114721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9906246471350291836152961 7429684853512718877114721)
        ·
          refine ⟨5572263640134539157836041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7429684853512718877114721 5572263640134539157836041)
          ·
            refine ⟨4179197730100904368377031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5572263640134539157836041 4179197730100904368377031)
            ·
              refine ⟨6268796595151356552565547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4179197730100904368377031 6268796595151356552565547)
              ·
                refine ⟨9403194892727034828848321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6268796595151356552565547 9403194892727034828848321)
                ·
                  refine ⟨7052396169545276121636241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9403194892727034828848321 7052396169545276121636241)
                  ·
                    refine ⟨5289297127158957091227181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7052396169545276121636241 5289297127158957091227181)
                    ·
                      refine ⟨1983486422684608909210193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5289297127158957091227181 1983486422684608909210193)
                      ·
                        rfl

theorem cell23_3862826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_3862826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862826 prefixEnd_3862826 := by exact prefixLift 3862826
  have htrace : WordTrace (prefixWord ++ tailWord_3862826) baseStart_3862826 baseEnd_3862826 := by
    simpa [prefixWord, tailWord_3862826, baseEnd_3862826] using wordTrace_append hprefix tailTrace_3862826
  have hstable : (prefixWord ++ tailWord_3862826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862826).length < 2 ^ (prefixWord ++ tailWord_3862826).sum := by decide
  have hdescent : baseEnd_3862826 < baseStart_3862826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862832 : List Nat := [2, 1, 1, 1, 2, 2, 2, 5, 2, 3, 2]
def baseStart_3862832 : Nat := 118140960795 + 3862832 * 2 ^ 59
def prefixEnd_3862832 : Nat := 4983230072969 + 3 ^ 40 * 3862832 * 2
def baseEnd_3862832 : Nat := 1983489503568535885735165

theorem tailTrace_3862832 : CollatzResearch.WordTrace tailWord_3862832 prefixEnd_3862832 1983489503568535885735165 := by
  unfold tailWord_3862832
  simp only [CollatzResearch.WordTrace]
  refine ⟨70444528770813429013891375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93926038361084572018521833 70444528770813429013891375)
  ·
    refine ⟨105666793156220143520837063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70444528770813429013891375 105666793156220143520837063)
    ·
      refine ⟨158500189734330215281255595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105666793156220143520837063 158500189734330215281255595)
      ·
        refine ⟨237750284601495322921883393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158500189734330215281255595 237750284601495322921883393)
        ·
          refine ⟨178312713451121492191412545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237750284601495322921883393 178312713451121492191412545)
          ·
            refine ⟨133734535088341119143559409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178312713451121492191412545 133734535088341119143559409)
            ·
              refine ⟨100300901316255839357669557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133734535088341119143559409 100300901316255839357669557)
              ·
                refine ⟨9403209498398984939781521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100300901316255839357669557 9403209498398984939781521)
                ·
                  refine ⟨7052407123799238704836141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9403209498398984939781521 7052407123799238704836141)
                  ·
                    refine ⟨2644652671424714514313553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7052407123799238704836141 2644652671424714514313553)
                    ·
                      refine ⟨1983489503568535885735165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2644652671424714514313553 1983489503568535885735165)
                      ·
                        rfl

theorem cell23_3862832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 2, 3, 2].length) (baseStart_3862832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862832 prefixEnd_3862832 := by exact prefixLift 3862832
  have htrace : WordTrace (prefixWord ++ tailWord_3862832) baseStart_3862832 baseEnd_3862832 := by
    simpa [prefixWord, tailWord_3862832, baseEnd_3862832] using wordTrace_append hprefix tailTrace_3862832
  have hstable : (prefixWord ++ tailWord_3862832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862832).length < 2 ^ (prefixWord ++ tailWord_3862832).sum := by decide
  have hdescent : baseEnd_3862832 < baseStart_3862832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862842 : List Nat := [3, 1, 1, 1, 4, 3, 1, 3, 1, 5]
def baseStart_3862842 : Nat := 118140960795 + 3862842 * 2 ^ 59
def prefixEnd_3862842 : Nat := 4983230072969 + 3 ^ 40 * 3862842 * 2
def baseEnd_3862842 : Nat := 661164879458360282203373

theorem tailTrace_3862842 : CollatzResearch.WordTrace tailWord_3862842 prefixEnd_3862842 661164879458360282203373 := by
  unfold tailWord_3862842
  simp only [CollatzResearch.WordTrace]
  refine ⟨35222355567897657433911695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93926281514393753157097853 35222355567897657433911695)
  ·
    refine ⟨52833533351846486150867543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35222355567897657433911695 52833533351846486150867543)
    ·
      refine ⟨79250300027769729226301315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52833533351846486150867543 79250300027769729226301315)
      ·
        refine ⟨118875450041654593839451973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79250300027769729226301315 118875450041654593839451973)
        ·
          refine ⟨22289146882810236344897245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118875450041654593839451973 22289146882810236344897245)
          ·
            refine ⟨8358430081053838629336467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22289146882810236344897245 8358430081053838629336467)
            ·
              refine ⟨12537645121580757944004701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8358430081053838629336467 12537645121580757944004701)
              ·
                refine ⟨4701616920592784229001763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12537645121580757944004701 4701616920592784229001763)
                ·
                  refine ⟨7052425380889176343502645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4701616920592784229001763 7052425380889176343502645)
                  ·
                    refine ⟨661164879458360282203373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7052425380889176343502645 661164879458360282203373)
                    ·
                      rfl

theorem cell23_3862842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 1, 5].length) (baseStart_3862842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862842 prefixEnd_3862842 := by exact prefixLift 3862842
  have htrace : WordTrace (prefixWord ++ tailWord_3862842) baseStart_3862842 baseEnd_3862842 := by
    simpa [prefixWord, tailWord_3862842, baseEnd_3862842] using wordTrace_append hprefix tailTrace_3862842
  have hstable : (prefixWord ++ tailWord_3862842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862842).length < 2 ^ (prefixWord ++ tailWord_3862842).sum := by decide
  have hdescent : baseEnd_3862842 < baseStart_3862842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862865 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 3, 1, 5]
def baseStart_3862865 : Nat := 118140960795 + 3862865 * 2 ^ 59
def prefixEnd_3862865 : Nat := 4983230072969 + 3 ^ 40 * 3862865 * 2
def baseEnd_3862865 : Nat := 1983506448430134256622513

theorem tailTrace_3862865 : CollatzResearch.WordTrace tailWord_3862865 prefixEnd_3862865 1983506448430134256622513 := by
  unfold tailWord_3862865
  simp only [CollatzResearch.WordTrace]
  refine ⟨140890261150507304663734049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93926840767004869775822699 140890261150507304663734049)
  ·
    refine ⟨105667695862880478497800537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140890261150507304663734049 105667695862880478497800537)
    ·
      refine ⟨79250771897160358873350403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105667695862880478497800537 79250771897160358873350403)
      ·
        refine ⟨118876157845740538310025605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79250771897160358873350403 118876157845740538310025605)
        ·
          refine ⟨22289279596076350933129801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118876157845740538310025605 22289279596076350933129801)
          ·
            refine ⟨16716959697057263199847351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22289279596076350933129801 16716959697057263199847351)
            ·
              refine ⟨25075439545585894799771027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16716959697057263199847351 25075439545585894799771027)
              ·
                refine ⟨37613159318378842199656541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25075439545585894799771027 37613159318378842199656541)
                ·
                  refine ⟨14104934744392065824871203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37613159318378842199656541 14104934744392065824871203)
                  ·
                    refine ⟨21157402116588098737306805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14104934744392065824871203 21157402116588098737306805)
                    ·
                      refine ⟨1983506448430134256622513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21157402116588098737306805 1983506448430134256622513)
                      ·
                        rfl

theorem cell23_3862865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_3862865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862865 prefixEnd_3862865 := by exact prefixLift 3862865
  have htrace : WordTrace (prefixWord ++ tailWord_3862865) baseStart_3862865 baseEnd_3862865 := by
    simpa [prefixWord, tailWord_3862865, baseEnd_3862865] using wordTrace_append hprefix tailTrace_3862865
  have hstable : (prefixWord ++ tailWord_3862865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862865).length < 2 ^ (prefixWord ++ tailWord_3862865).sum := by decide
  have hdescent : baseEnd_3862865 < baseStart_3862865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862876 : List Nat := [2, 2, 4, 3, 1, 1, 2, 2, 1, 5]
def baseStart_3862876 : Nat := 118140960795 + 3862876 * 2 ^ 59
def prefixEnd_3862876 : Nat := 4983230072969 + 3 ^ 40 * 3862876 * 2
def baseEnd_3862876 : Nat := 661170698905777904528321

theorem tailTrace_3862876 : CollatzResearch.WordTrace tailWord_3862876 prefixEnd_3862876 661170698905777904528321 := by
  unfold tailWord_3862876
  simp only [CollatzResearch.WordTrace]
  refine ⟨70445331176733726771192241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93927108235644969028256321 70445331176733726771192241)
  ·
    refine ⟨52833998382550295078394181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70445331176733726771192241 52833998382550295078394181)
    ·
      refine ⟨9906374696728180327198909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52833998382550295078394181 9906374696728180327198909)
      ·
        refine ⟨3714890511273067622699591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9906374696728180327198909 3714890511273067622699591)
        ·
          refine ⟨5572335766909601434049387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3714890511273067622699591 5572335766909601434049387)
          ·
            refine ⟨8358503650364402151074081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5572335766909601434049387 8358503650364402151074081)
            ·
              refine ⟨6268877737773301613305561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8358503650364402151074081 6268877737773301613305561)
              ·
                refine ⟨4701658303329976209979171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6268877737773301613305561 4701658303329976209979171)
                ·
                  refine ⟨7052487454994964314968757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4701658303329976209979171 7052487454994964314968757)
                  ·
                    refine ⟨661170698905777904528321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7052487454994964314968757 661170698905777904528321)
                    ·
                      rfl

theorem cell23_3862876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_3862876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862876 prefixEnd_3862876 := by exact prefixLift 3862876
  have htrace : WordTrace (prefixWord ++ tailWord_3862876) baseStart_3862876 baseEnd_3862876 := by
    simpa [prefixWord, tailWord_3862876, baseEnd_3862876] using wordTrace_append hprefix tailTrace_3862876
  have hstable : (prefixWord ++ tailWord_3862876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862876).length < 2 ^ (prefixWord ++ tailWord_3862876).sum := by decide
  have hdescent : baseEnd_3862876 < baseStart_3862876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862879 : List Nat := [1, 1, 2, 3, 1, 2, 4, 2, 3, 2, 2]
def baseStart_3862879 : Nat := 118140960795 + 3862879 * 2 ^ 59
def prefixEnd_3862879 : Nat := 4983230072969 + 3 ^ 40 * 3862879 * 2
def baseEnd_3862879 : Nat := 1983513637159297201847449

theorem tailTrace_3862879 : CollatzResearch.WordTrace tailWord_3862879 prefixEnd_3862879 1983513637159297201847449 := by
  unfold tailWord_3862879
  simp only [CollatzResearch.WordTrace]
  refine ⟨140890771772456585054743691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93927181181637723369829127 140890771772456585054743691)
  ·
    refine ⟨211336157658684877582115537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140890771772456585054743691 211336157658684877582115537)
    ·
      refine ⟨158502118244013658186586653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211336157658684877582115537 158502118244013658186586653)
      ·
        refine ⟨59438294341505121819969995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158502118244013658186586653 59438294341505121819969995)
        ·
          refine ⟨89157441512257682729954993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59438294341505121819969995 89157441512257682729954993)
          ·
            refine ⟨66868081134193262047466245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89157441512257682729954993 66868081134193262047466245)
            ·
              refine ⟨12537765212661236633899921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66868081134193262047466245 12537765212661236633899921)
              ·
                refine ⟨9403323909495927475424941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12537765212661236633899921 9403323909495927475424941)
                ·
                  refine ⟨3526246466060972803284353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9403323909495927475424941 3526246466060972803284353)
                  ·
                    refine ⟨2644684849545729602463265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3526246466060972803284353 2644684849545729602463265)
                    ·
                      refine ⟨1983513637159297201847449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2644684849545729602463265 1983513637159297201847449)
                      ·
                        rfl

theorem cell23_3862879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 2, 2].length) (baseStart_3862879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862879 prefixEnd_3862879 := by exact prefixLift 3862879
  have htrace : WordTrace (prefixWord ++ tailWord_3862879) baseStart_3862879 baseEnd_3862879 := by
    simpa [prefixWord, tailWord_3862879, baseEnd_3862879] using wordTrace_append hprefix tailTrace_3862879
  have hstable : (prefixWord ++ tailWord_3862879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862879).length < 2 ^ (prefixWord ++ tailWord_3862879).sum := by decide
  have hdescent : baseEnd_3862879 < baseStart_3862879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862885 : List Nat := [1, 3, 1, 3, 1, 4, 1, 9]
def baseStart_3862885 : Nat := 118140960795 + 3862885 * 2 ^ 59
def prefixEnd_3862885 : Nat := 4983230072969 + 3 ^ 40 * 3862885 * 2
def baseEnd_3862885 : Nat := 73463582149749043643423

theorem tailTrace_3862885 : CollatzResearch.WordTrace tailWord_3862885 prefixEnd_3862885 73463582149749043643423 := by
  unfold tailWord_3862885
  simp only [CollatzResearch.WordTrace]
  refine ⟨140890990610434848079462109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93927327073623232052974739 140890990610434848079462109)
  ·
    refine ⟨52834121478913068029798291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140890990610434848079462109 52834121478913068029798291)
    ·
      refine ⟨79251182218369602044697437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52834121478913068029798291 79251182218369602044697437)
      ·
        refine ⟨29719193331888600766761539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79251182218369602044697437 29719193331888600766761539)
        ·
          refine ⟨44578789997832901150142309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29719193331888600766761539 44578789997832901150142309)
          ·
            refine ⟨8358523124593668965651683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44578789997832901150142309 8358523124593668965651683)
            ·
              refine ⟨12537784686890503448477525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8358523124593668965651683 12537784686890503448477525)
              ·
                refine ⟨73463582149749043643423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12537784686890503448477525 73463582149749043643423)
                ·
                  rfl

theorem cell23_3862885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 9].length) (baseStart_3862885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862885 prefixEnd_3862885 := by exact prefixLift 3862885
  have htrace : WordTrace (prefixWord ++ tailWord_3862885) baseStart_3862885 baseEnd_3862885 := by
    simpa [prefixWord, tailWord_3862885, baseEnd_3862885] using wordTrace_append hprefix tailTrace_3862885
  have hstable : (prefixWord ++ tailWord_3862885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862885).length < 2 ^ (prefixWord ++ tailWord_3862885).sum := by decide
  have hdescent : baseEnd_3862885 < baseStart_3862885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862913 : List Nat := [1, 2, 4, 3, 1, 3, 1, 1, 3, 2, 2]
def baseStart_3862913 : Nat := 118140960795 + 3862913 * 2 ^ 59
def prefixEnd_3862913 : Nat := 4983230072969 + 3 ^ 40 * 3862913 * 2
def baseEnd_3862913 : Nat := 1983531095501550068822293

theorem tailTrace_3862913 : CollatzResearch.WordTrace tailWord_3862913 prefixEnd_3862913 1983531095501550068822293 := by
  unfold tailWord_3862913
  simp only [CollatzResearch.WordTrace]
  refine ⟨140892011854333408861481393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93928007902888939240987595 140892011854333408861481393)
  ·
    refine ⟨105669008890750056646111045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140892011854333408861481393 105669008890750056646111045)
    ·
      refine ⟨19812939167015635621145821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105669008890750056646111045 19812939167015635621145821)
      ·
        refine ⟨7429852187630863357929683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19812939167015635621145821 7429852187630863357929683)
        ·
          refine ⟨11144778281446295036894525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7429852187630863357929683 11144778281446295036894525)
          ·
            refine ⟨4179291855542360638835447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11144778281446295036894525 4179291855542360638835447)
            ·
              refine ⟨6268937783313540958253171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4179291855542360638835447 6268937783313540958253171)
              ·
                refine ⟨9403406674970311437379757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6268937783313540958253171 9403406674970311437379757)
                ·
                  refine ⟨3526277503113866789017409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9403406674970311437379757 3526277503113866789017409)
                  ·
                    refine ⟨2644708127335400091763057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3526277503113866789017409 2644708127335400091763057)
                    ·
                      refine ⟨1983531095501550068822293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2644708127335400091763057 1983531095501550068822293)
                      ·
                        rfl

theorem cell23_3862913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_3862913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862913 prefixEnd_3862913 := by exact prefixLift 3862913
  have htrace : WordTrace (prefixWord ++ tailWord_3862913) baseStart_3862913 baseEnd_3862913 := by
    simpa [prefixWord, tailWord_3862913, baseEnd_3862913] using wordTrace_append hprefix tailTrace_3862913
  have hstable : (prefixWord ++ tailWord_3862913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862913).length < 2 ^ (prefixWord ++ tailWord_3862913).sum := by decide
  have hdescent : baseEnd_3862913 < baseStart_3862913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862986 : List Nat := [3, 1, 2, 1, 2, 2, 1, 5, 2, 2, 2]
def baseStart_3862986 : Nat := 118140960795 + 3862986 * 2 ^ 59
def prefixEnd_3862986 : Nat := 4983230072969 + 3 ^ 40 * 3862986 * 2
def baseEnd_3862986 : Nat := 1983568579589328283209457

theorem tailTrace_3862986 : CollatzResearch.WordTrace tailWord_3862986 prefixEnd_3862986 1983568579589328283209457 := by
  unfold tailWord_3862986
  simp only [CollatzResearch.WordTrace]
  refine ⟨35223668595767235582222203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93929782922045961552592541 35223668595767235582222203)
  ·
    refine ⟨52835502893650853373333305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35223668595767235582222203 52835502893650853373333305)
    ·
      refine ⟨39626627170238140029999979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52835502893650853373333305 39626627170238140029999979)
      ·
        refine ⟨59439940755357210044999969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39626627170238140029999979 59439940755357210044999969)
        ·
          refine ⟨44579955566517907533749977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59439940755357210044999969 44579955566517907533749977)
          ·
            refine ⟨33434966674888430650312483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44579955566517907533749977 33434966674888430650312483)
            ·
              refine ⟨50152450012332645975468725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33434966674888430650312483 50152450012332645975468725)
              ·
                refine ⟨4701792188656185560200193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50152450012332645975468725 4701792188656185560200193)
                ·
                  refine ⟨3526344141492139170150145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4701792188656185560200193 3526344141492139170150145)
                  ·
                    refine ⟨2644758106119104377612609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3526344141492139170150145 2644758106119104377612609)
                    ·
                      refine ⟨1983568579589328283209457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2644758106119104377612609 1983568579589328283209457)
                      ·
                        rfl

theorem cell23_3862986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 2, 2, 2].length) (baseStart_3862986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3862986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3862986 prefixEnd_3862986 := by exact prefixLift 3862986
  have htrace : WordTrace (prefixWord ++ tailWord_3862986) baseStart_3862986 baseEnd_3862986 := by
    simpa [prefixWord, tailWord_3862986, baseEnd_3862986] using wordTrace_append hprefix tailTrace_3862986
  have hstable : (prefixWord ++ tailWord_3862986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862986).length < 2 ^ (prefixWord ++ tailWord_3862986).sum := by decide
  have hdescent : baseEnd_3862986 < baseStart_3862986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863002 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3]
def baseStart_3863002 : Nat := 118140960795 + 3863002 * 2 ^ 59
def prefixEnd_3863002 : Nat := 4983230072969 + 3 ^ 40 * 3863002 * 2
def baseEnd_3863002 : Nat := 1983576795279800220609383

theorem tailTrace_3863002 : CollatzResearch.WordTrace tailWord_3863002 prefixEnd_3863002 1983576795279800220609383 := by
  unfold tailWord_3863002
  simp only [CollatzResearch.WordTrace]
  refine ⟨35223814487752744265367815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93930171967340651374314173 35223814487752744265367815)
  ·
    refine ⟨52835721731629116398051723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35223814487752744265367815 52835721731629116398051723)
    ·
      refine ⟨79253582597443674597077585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52835721731629116398051723 79253582597443674597077585)
      ·
        refine ⟨59440186948082755947808189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79253582597443674597077585 59440186948082755947808189)
        ·
          refine ⟨22290070105531033480428071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59440186948082755947808189 22290070105531033480428071)
          ·
            refine ⟨33435105158296550220642107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22290070105531033480428071 33435105158296550220642107)
            ·
              refine ⟨50152657737444825330963161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33435105158296550220642107 50152657737444825330963161)
              ·
                refine ⟨37614493303083618998222371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50152657737444825330963161 37614493303083618998222371)
                ·
                  refine ⟨56421739954625428497333557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37614493303083618998222371 56421739954625428497333557)
                  ·
                    refine ⟨5289538120746133921625021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56421739954625428497333557 5289538120746133921625021)
                    ·
                      refine ⟨1983576795279800220609383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5289538120746133921625021 1983576795279800220609383)
                      ·
                        rfl

theorem cell23_3863002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_3863002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863002 prefixEnd_3863002 := by exact prefixLift 3863002
  have htrace : WordTrace (prefixWord ++ tailWord_3863002) baseStart_3863002 baseEnd_3863002 := by
    simpa [prefixWord, tailWord_3863002, baseEnd_3863002] using wordTrace_append hprefix tailTrace_3863002
  have hstable : (prefixWord ++ tailWord_3863002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863002).length < 2 ^ (prefixWord ++ tailWord_3863002).sum := by decide
  have hdescent : baseEnd_3863002 < baseStart_3863002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863009 : List Nat := [1, 2, 3, 1, 2, 2, 4, 3, 5]
def baseStart_3863009 : Nat := 118140960795 + 3863009 * 2 ^ 59
def prefixEnd_3863009 : Nat := 4983230072969 + 3 ^ 40 * 3863009 * 2
def baseEnd_3863009 : Nat := 220397821071597965913539

theorem tailTrace_3863009 : CollatzResearch.WordTrace tailWord_3863009 prefixEnd_3863009 220397821071597965913539 := by
  unfold tailWord_3863009
  simp only [CollatzResearch.WordTrace]
  refine ⟨140895513261985617256976081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93930342174657078171317387 140895513261985617256976081)
  ·
    refine ⟨105671634946489212942732061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140895513261985617256976081 105671634946489212942732061)
    ·
      refine ⟨39626863104933454853524523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105671634946489212942732061 39626863104933454853524523)
      ·
        refine ⟨59440294657400182280286785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39626863104933454853524523 59440294657400182280286785)
        ·
          refine ⟨44580220993050136710215089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59440294657400182280286785 44580220993050136710215089)
          ·
            refine ⟨33435165744787602532661317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44580220993050136710215089 33435165744787602532661317)
            ·
              refine ⟨6269093577147675474873997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33435165744787602532661317 6269093577147675474873997)
              ·
                refine ⟨2350910091430378303077749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6269093577147675474873997 2350910091430378303077749)
                ·
                  refine ⟨220397821071597965913539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2350910091430378303077749 220397821071597965913539)
                  ·
                    rfl

theorem cell23_3863009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 5].length) (baseStart_3863009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863009 prefixEnd_3863009 := by exact prefixLift 3863009
  have htrace : WordTrace (prefixWord ++ tailWord_3863009) baseStart_3863009 baseEnd_3863009 := by
    simpa [prefixWord, tailWord_3863009, baseEnd_3863009] using wordTrace_append hprefix tailTrace_3863009
  have hstable : (prefixWord ++ tailWord_3863009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863009).length < 2 ^ (prefixWord ++ tailWord_3863009).sum := by decide
  have hdescent : baseEnd_3863009 < baseStart_3863009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863035 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 4, 8]
def baseStart_3863035 : Nat := 118140960795 + 3863035 * 2 ^ 59
def prefixEnd_3863035 : Nat := 4983230072969 + 3 ^ 40 * 3863035 * 2
def baseEnd_3863035 : Nat := 661197913380466197165577

theorem tailTrace_3863035 : CollatzResearch.WordTrace tailWord_3863035 prefixEnd_3863035 661197913380466197165577 := by
  unfold tailWord_3863035
  simp only [CollatzResearch.WordTrace]
  refine ⟨140896461559891423697422559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93930974373260949131615039 140896461559891423697422559)
  ·
    refine ⟨211344692339837135546133839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140896461559891423697422559 211344692339837135546133839)
    ·
      refine ⟨317017038509755703319200759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211344692339837135546133839 317017038509755703319200759)
      ·
        refine ⟨475525557764633554978801139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317017038509755703319200759 475525557764633554978801139)
        ·
          refine ⟨713288336646950332468201709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475525557764633554978801139 713288336646950332468201709)
          ·
            refine ⟨267483126242606374675575641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 713288336646950332468201709 267483126242606374675575641)
            ·
              refine ⟨200612344681954781006681731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267483126242606374675575641 200612344681954781006681731)
              ·
                refine ⟨300918517022932171510022597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200612344681954781006681731 300918517022932171510022597)
                ·
                  refine ⟨56422221941799782158129237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 300918517022932171510022597 56422221941799782158129237)
                  ·
                    refine ⟨661197913380466197165577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56422221941799782158129237 661197913380466197165577)
                    ·
                      rfl

theorem cell23_3863035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 8].length) (baseStart_3863035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863035 prefixEnd_3863035 := by exact prefixLift 3863035
  have htrace : WordTrace (prefixWord ++ tailWord_3863035) baseStart_3863035 baseEnd_3863035 := by
    simpa [prefixWord, tailWord_3863035, baseEnd_3863035] using wordTrace_append hprefix tailTrace_3863035
  have hstable : (prefixWord ++ tailWord_3863035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863035).length < 2 ^ (prefixWord ++ tailWord_3863035).sum := by decide
  have hdescent : baseEnd_3863035 < baseStart_3863035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863119 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 1, 5, 2]
def baseStart_3863119 : Nat := 118140960795 + 3863119 * 2 ^ 59
def prefixEnd_3863119 : Nat := 4983230072969 + 3 ^ 40 * 3863119 * 2
def baseEnd_3863119 : Nat := 1983636872516376262846345

theorem tailTrace_3863119 : CollatzResearch.WordTrace tailWord_3863119 prefixEnd_3863119 1983636872516376262846345 := by
  unfold tailWord_3863119
  simp only [CollatzResearch.WordTrace]
  refine ⟨140899525291587106043480411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93933016861058070695653607 140899525291587106043480411)
  ·
    refine ⟨211349287937380659065220617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140899525291587106043480411 211349287937380659065220617)
    ·
      refine ⟨158511965953035494298915463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211349287937380659065220617 158511965953035494298915463)
      ·
        refine ⟨237767948929553241448373195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158511965953035494298915463 237767948929553241448373195)
        ·
          refine ⟨356651923394329862172559793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237767948929553241448373195 356651923394329862172559793)
          ·
            refine ⟨267488942545747396629419845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356651923394329862172559793 267488942545747396629419845)
            ·
              refine ⟨50154176727327636868016221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 267488942545747396629419845 50154176727327636868016221)
              ·
                refine ⟨18807816272747863825506083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50154176727327636868016221 18807816272747863825506083)
                ·
                  refine ⟨28211724409121795738259125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18807816272747863825506083 28211724409121795738259125)
                  ·
                    refine ⟨2644849163355168350461793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28211724409121795738259125 2644849163355168350461793)
                    ·
                      refine ⟨1983636872516376262846345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2644849163355168350461793 1983636872516376262846345)
                      ·
                        rfl

theorem cell23_3863119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 5, 2].length) (baseStart_3863119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863119 prefixEnd_3863119 := by exact prefixLift 3863119
  have htrace : WordTrace (prefixWord ++ tailWord_3863119) baseStart_3863119 baseEnd_3863119 := by
    simpa [prefixWord, tailWord_3863119, baseEnd_3863119] using wordTrace_append hprefix tailTrace_3863119
  have hstable : (prefixWord ++ tailWord_3863119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863119).length < 2 ^ (prefixWord ++ tailWord_3863119).sum := by decide
  have hdescent : baseEnd_3863119 < baseStart_3863119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863136 : List Nat := [2, 1, 1, 3, 2, 1, 4, 2, 2, 3, 2]
def baseStart_3863136 : Nat := 118140960795 + 3863136 * 2 ^ 59
def prefixEnd_3863136 : Nat := 4983230072969 + 3 ^ 40 * 3863136 * 2
def baseEnd_3863136 : Nat := 1983645601687502696333767

theorem tailTrace_3863136 : CollatzResearch.WordTrace tailWord_3863136 prefixEnd_3863136 1983645601687502696333767 := by
  unfold tailWord_3863136
  simp only [CollatzResearch.WordTrace]
  refine ⟨70450072666262758973424631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93933430221683678631232841 70450072666262758973424631)
  ·
    refine ⟨105675108999394138460136947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70450072666262758973424631 105675108999394138460136947)
    ·
      refine ⟨158512663499091207690205421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105675108999394138460136947 158512663499091207690205421)
      ·
        refine ⟨59442248812159202883827033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158512663499091207690205421 59442248812159202883827033)
        ·
          refine ⟨44581686609119402162870275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59442248812159202883827033 44581686609119402162870275)
          ·
            refine ⟨66872529913679103244305413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44581686609119402162870275 66872529913679103244305413)
            ·
              refine ⟨12538599358814831858307265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66872529913679103244305413 12538599358814831858307265)
              ·
                refine ⟨9403949519111123893730449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12538599358814831858307265 9403949519111123893730449)
                ·
                  refine ⟨7052962139333342920297837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9403949519111123893730449 7052962139333342920297837)
                  ·
                    refine ⟨2644860802250003595111689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7052962139333342920297837 2644860802250003595111689)
                    ·
                      refine ⟨1983645601687502696333767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2644860802250003595111689 1983645601687502696333767)
                      ·
                        rfl

theorem cell23_3863136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 2, 3, 2].length) (baseStart_3863136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863136 prefixEnd_3863136 := by exact prefixLift 3863136
  have htrace : WordTrace (prefixWord ++ tailWord_3863136) baseStart_3863136 baseEnd_3863136 := by
    simpa [prefixWord, tailWord_3863136, baseEnd_3863136] using wordTrace_append hprefix tailTrace_3863136
  have hstable : (prefixWord ++ tailWord_3863136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863136).length < 2 ^ (prefixWord ++ tailWord_3863136).sum := by decide
  have hdescent : baseEnd_3863136 < baseStart_3863136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863162 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6]
def baseStart_3863162 : Nat := 118140960795 + 3863162 * 2 ^ 59
def prefixEnd_3863162 : Nat := 4983230072969 + 3 ^ 40 * 3863162 * 2
def baseEnd_3863162 : Nat := 1983658952184519594608647

theorem tailTrace_3863162 : CollatzResearch.WordTrace tailWord_3863162 prefixEnd_3863162 1983658952184519594608647 := by
  unfold tailWord_3863162
  simp only [CollatzResearch.WordTrace]
  refine ⟨35225273407607831096823935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93934062420287549591530493 35225273407607831096823935)
  ·
    refine ⟨52837910111411746645235903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35225273407607831096823935 52837910111411746645235903)
    ·
      refine ⟨79256865167117619967853855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52837910111411746645235903 79256865167117619967853855)
      ·
        refine ⟨118885297750676429951780783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79256865167117619967853855 118885297750676429951780783)
        ·
          refine ⟨178327946626014644927671175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118885297750676429951780783 178327946626014644927671175)
          ·
            refine ⟨267491919939021967391506763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178327946626014644927671175 267491919939021967391506763)
            ·
              refine ⟨401237879908532951087260145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267491919939021967391506763 401237879908532951087260145)
              ·
                refine ⟨300928409931399713315445109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401237879908532951087260145 300928409931399713315445109)
                ·
                  refine ⟨28212038431068723123322979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 300928409931399713315445109 28212038431068723123322979)
                  ·
                    refine ⟨42318057646603084684984469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28212038431068723123322979 42318057646603084684984469)
                    ·
                      refine ⟨1983658952184519594608647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42318057646603084684984469 1983658952184519594608647)
                      ·
                        rfl

theorem cell23_3863162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_3863162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863162 prefixEnd_3863162 := by exact prefixLift 3863162
  have htrace : WordTrace (prefixWord ++ tailWord_3863162) baseStart_3863162 baseEnd_3863162 := by
    simpa [prefixWord, tailWord_3863162, baseEnd_3863162] using wordTrace_append hprefix tailTrace_3863162
  have hstable : (prefixWord ++ tailWord_3863162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863162).length < 2 ^ (prefixWord ++ tailWord_3863162).sum := by decide
  have hdescent : baseEnd_3863162 < baseStart_3863162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863200 : List Nat := [2, 1, 1, 4, 4, 1, 2, 1, 3, 2, 2]
def baseStart_3863200 : Nat := 118140960795 + 3863200 * 2 ^ 59
def prefixEnd_3863200 : Nat := 4983230072969 + 3 ^ 40 * 3863200 * 2
def baseEnd_3863200 : Nat := 1983678464449390445933473

theorem tailTrace_3863200 : CollatzResearch.WordTrace tailWord_3863200 prefixEnd_3863200 1983678464449390445933473 := by
  unfold tailWord_3863200
  simp only [CollatzResearch.WordTrace]
  refine ⟨70451239802146828438589527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93934986402862437918119369 70451239802146828438589527)
  ·
    refine ⟨105676859703220242657884291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70451239802146828438589527 105676859703220242657884291)
    ·
      refine ⟨158515289554830363986826437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105676859703220242657884291 158515289554830363986826437)
      ·
        refine ⟨29721616791530693247529957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158515289554830363986826437 29721616791530693247529957)
        ·
          refine ⟨5572803148412004983911867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29721616791530693247529957 5572803148412004983911867)
          ·
            refine ⟨8359204722618007475867801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5572803148412004983911867 8359204722618007475867801)
            ·
              refine ⟨6269403541963505606900851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8359204722618007475867801 6269403541963505606900851)
              ·
                refine ⟨9404105312945258410351277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6269403541963505606900851 9404105312945258410351277)
                ·
                  refine ⟨3526539492354471903881729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9404105312945258410351277 3526539492354471903881729)
                  ·
                    refine ⟨2644904619265853927911297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3526539492354471903881729 2644904619265853927911297)
                    ·
                      refine ⟨1983678464449390445933473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2644904619265853927911297 1983678464449390445933473)
                      ·
                        rfl

theorem cell23_3863200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_3863200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863200 prefixEnd_3863200 := by exact prefixLift 3863200
  have htrace : WordTrace (prefixWord ++ tailWord_3863200) baseStart_3863200 baseEnd_3863200 := by
    simpa [prefixWord, tailWord_3863200, baseEnd_3863200] using wordTrace_append hprefix tailTrace_3863200
  have hstable : (prefixWord ++ tailWord_3863200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863200).length < 2 ^ (prefixWord ++ tailWord_3863200).sum := by decide
  have hdescent : baseEnd_3863200 < baseStart_3863200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863210 : List Nat := [3, 1, 5, 2, 1, 2, 1, 1, 1, 6]
def baseStart_3863210 : Nat := 118140960795 + 3863210 * 2 ^ 59
def prefixEnd_3863210 : Nat := 4983230072969 + 3 ^ 40 * 3863210 * 2
def baseEnd_3863210 : Nat := 661227866418645135602809

theorem tailTrace_3863210 : CollatzResearch.WordTrace tailWord_3863210 prefixEnd_3863210 661227866418645135602809 := by
  unfold tailWord_3863210
  simp only [CollatzResearch.WordTrace]
  refine ⟨35225711083564357146260771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93935229556171619056695389 35225711083564357146260771)
  ·
    refine ⟨52838566625346535719391157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35225711083564357146260771 52838566625346535719391157)
    ·
      refine ⟨4953615621126237723692921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52838566625346535719391157 4953615621126237723692921)
      ·
        refine ⟨3715211715844678292769691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4953615621126237723692921 3715211715844678292769691)
        ·
          refine ⟨5572817573767017439154537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3715211715844678292769691 5572817573767017439154537)
          ·
            refine ⟨4179613180325263079365903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5572817573767017439154537 4179613180325263079365903)
            ·
              refine ⟨6269419770487894619048855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4179613180325263079365903 6269419770487894619048855)
              ·
                refine ⟨9404129655731841928573283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6269419770487894619048855 9404129655731841928573283)
                ·
                  refine ⟨14106194483597762892859925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9404129655731841928573283 14106194483597762892859925)
                  ·
                    refine ⟨661227866418645135602809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14106194483597762892859925 661227866418645135602809)
                    ·
                      rfl

theorem cell23_3863210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_3863210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863210 prefixEnd_3863210 := by exact prefixLift 3863210
  have htrace : WordTrace (prefixWord ++ tailWord_3863210) baseStart_3863210 baseEnd_3863210 := by
    simpa [prefixWord, tailWord_3863210, baseEnd_3863210] using wordTrace_append hprefix tailTrace_3863210
  have hstable : (prefixWord ++ tailWord_3863210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863210).length < 2 ^ (prefixWord ++ tailWord_3863210).sum := by decide
  have hdescent : baseEnd_3863210 < baseStart_3863210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863213 : List Nat := [1, 5, 2, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_3863213 : Nat := 118140960795 + 3863213 * 2 ^ 59
def prefixEnd_3863213 : Nat := 4983230072969 + 3 ^ 40 * 3863213 * 2
def baseEnd_3863213 : Nat := 1983685139697898895070913

theorem tailTrace_3863213 : CollatzResearch.WordTrace tailWord_3863213 prefixEnd_3863213 1983685139697898895070913 := by
  unfold tailWord_3863213
  simp only [CollatzResearch.WordTrace]
  refine ⟨140902953753246560097402293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93935302502164373398268195 140902953753246560097402293)
  ·
    refine ⟨13209651914366865009131465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140902953753246560097402293 13209651914366865009131465)
    ·
      refine ⟨9907238935775148756848599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13209651914366865009131465 9907238935775148756848599)
      ·
        refine ⟨14860858403662723135272899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9907238935775148756848599 14860858403662723135272899)
        ·
          refine ⟨22291287605494084702909349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14860858403662723135272899 22291287605494084702909349)
          ·
            refine ⟨4179616426030140881795503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22291287605494084702909349 4179616426030140881795503)
            ·
              refine ⟨6269424639045211322693255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4179616426030140881795503 6269424639045211322693255)
              ·
                refine ⟨9404136958567816984039883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6269424639045211322693255 9404136958567816984039883)
                ·
                  refine ⟨14106205437851725476059825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9404136958567816984039883 14106205437851725476059825)
                  ·
                    refine ⟨10579654078388794107044869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14106205437851725476059825 10579654078388794107044869)
                    ·
                      refine ⟨1983685139697898895070913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10579654078388794107044869 1983685139697898895070913)
                      ·
                        rfl

theorem cell23_3863213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_3863213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863213 prefixEnd_3863213 := by exact prefixLift 3863213
  have htrace : WordTrace (prefixWord ++ tailWord_3863213) baseStart_3863213 baseEnd_3863213 := by
    simpa [prefixWord, tailWord_3863213, baseEnd_3863213] using wordTrace_append hprefix tailTrace_3863213
  have hstable : (prefixWord ++ tailWord_3863213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863213).length < 2 ^ (prefixWord ++ tailWord_3863213).sum := by decide
  have hdescent : baseEnd_3863213 < baseStart_3863213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863223 : List Nat := [1, 1, 3, 1, 7, 1, 2, 7]
def baseStart_3863223 : Nat := 118140960795 + 3863223 * 2 ^ 59
def prefixEnd_3863223 : Nat := 4983230072969 + 3 ^ 40 * 3863223 * 2
def baseEnd_3863223 : Nat := 73470010166831253923921

theorem tailTrace_3863223 : CollatzResearch.WordTrace tailWord_3863223 prefixEnd_3863223 73470010166831253923921 := by
  unfold tailWord_3863223
  simp only [CollatzResearch.WordTrace]
  refine ⟨140903318483210331805266323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93935545655473554536844215 140903318483210331805266323)
  ·
    refine ⟨211354977724815497707899485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140903318483210331805266323 211354977724815497707899485)
    ·
      refine ⟨79258116646805811640462307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211354977724815497707899485 79258116646805811640462307)
      ·
        refine ⟨118887174970208717460693461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79258116646805811640462307 118887174970208717460693461)
        ·
          refine ⟨2786418163364266815485003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 118887174970208717460693461 2786418163364266815485003)
          ·
            refine ⟨4179627245046400223227505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2786418163364266815485003 4179627245046400223227505)
            ·
              refine ⟨3134720433784800167420629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4179627245046400223227505 3134720433784800167420629)
              ·
                refine ⟨73470010166831253923921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3134720433784800167420629 73470010166831253923921)
                ·
                  rfl

theorem cell23_3863223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 7].length) (baseStart_3863223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863223 prefixEnd_3863223 := by exact prefixLift 3863223
  have htrace : WordTrace (prefixWord ++ tailWord_3863223) baseStart_3863223 baseEnd_3863223 := by
    simpa [prefixWord, tailWord_3863223, baseEnd_3863223] using wordTrace_append hprefix tailTrace_3863223
  have hstable : (prefixWord ++ tailWord_3863223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863223).length < 2 ^ (prefixWord ++ tailWord_3863223).sum := by decide
  have hdescent : baseEnd_3863223 < baseStart_3863223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863229 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 2, 2, 5]
def baseStart_3863229 : Nat := 118140960795 + 3863229 * 2 ^ 59
def prefixEnd_3863229 : Nat := 4983230072969 + 3 ^ 40 * 3863229 * 2
def baseEnd_3863229 : Nat := 1983693355388370832470839

theorem tailTrace_3863229 : CollatzResearch.WordTrace tailWord_3863229 prefixEnd_3863229 1983693355388370832470839 := by
  unfold tailWord_3863229
  simp only [CollatzResearch.WordTrace]
  refine ⟨140903537321188594829984741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93935691547459063219989827 140903537321188594829984741)
  ·
    refine ⟨26419413247722861530622139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140903537321188594829984741 26419413247722861530622139)
    ·
      refine ⟨39629119871584292295933209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26419413247722861530622139 39629119871584292295933209)
      ·
        refine ⟨29721839903688219221949907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39629119871584292295933209 29721839903688219221949907)
        ·
          refine ⟨44582759855532328832924861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29721839903688219221949907 44582759855532328832924861)
          ·
            refine ⟨16718534945824623312346823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44582759855532328832924861 16718534945824623312346823)
            ·
              refine ⟨25077802418736934968520235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16718534945824623312346823 25077802418736934968520235)
              ·
                refine ⟨37616703628105402452780353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25077802418736934968520235 37616703628105402452780353)
                ·
                  refine ⟨28212527721079051839585265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37616703628105402452780353 28212527721079051839585265)
                  ·
                    refine ⟨21159395790809288879688949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28212527721079051839585265 21159395790809288879688949)
                    ·
                      refine ⟨1983693355388370832470839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21159395790809288879688949 1983693355388370832470839)
                      ·
                        rfl

theorem cell23_3863229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_3863229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863229 prefixEnd_3863229 := by exact prefixLift 3863229
  have htrace : WordTrace (prefixWord ++ tailWord_3863229) baseStart_3863229 baseEnd_3863229 := by
    simpa [prefixWord, tailWord_3863229, baseEnd_3863229] using wordTrace_append hprefix tailTrace_3863229
  have hstable : (prefixWord ++ tailWord_3863229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863229).length < 2 ^ (prefixWord ++ tailWord_3863229).sum := by decide
  have hdescent : baseEnd_3863229 < baseStart_3863229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863267 : List Nat := [1, 1, 1, 7, 1, 3, 2, 1, 2, 1, 3]
def baseStart_3863267 : Nat := 118140960795 + 3863267 * 2 ^ 59
def prefixEnd_3863267 : Nat := 4983230072969 + 3 ^ 40 * 3863267 * 2
def baseEnd_3863267 : Nat := 1983712867653241683795665

theorem tailTrace_3863267 : CollatzResearch.WordTrace tailWord_3863267 prefixEnd_3863267 1983712867653241683795665 := by
  unfold tailWord_3863267
  simp only [CollatzResearch.WordTrace]
  refine ⟨140904923295050927319868055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93936615530033951546578703 140904923295050927319868055)
  ·
    refine ⟨211357384942576390979802083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140904923295050927319868055 211357384942576390979802083)
    ·
      refine ⟨317036077413864586469703125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211357384942576390979802083 317036077413864586469703125)
      ·
        refine ⟨7430533064387451245383667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 317036077413864586469703125 7430533064387451245383667)
        ·
          refine ⟨11145799596581176868075501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7430533064387451245383667 11145799596581176868075501)
          ·
            refine ⟨4179674848717941325528313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11145799596581176868075501 4179674848717941325528313)
            ·
              refine ⟨3134756136538455994146235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4179674848717941325528313 3134756136538455994146235)
              ·
                refine ⟨4702134204807683991219353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3134756136538455994146235 4702134204807683991219353)
                ·
                  refine ⟨3526600653605762993414515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4702134204807683991219353 3526600653605762993414515)
                  ·
                    refine ⟨5289900980408644490121773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3526600653605762993414515 5289900980408644490121773)
                    ·
                      refine ⟨1983712867653241683795665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5289900980408644490121773 1983712867653241683795665)
                      ·
                        rfl

theorem cell23_3863267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_3863267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863267 prefixEnd_3863267 := by exact prefixLift 3863267
  have htrace : WordTrace (prefixWord ++ tailWord_3863267) baseStart_3863267 baseEnd_3863267 := by
    simpa [prefixWord, tailWord_3863267, baseEnd_3863267] using wordTrace_append hprefix tailTrace_3863267
  have hstable : (prefixWord ++ tailWord_3863267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863267).length < 2 ^ (prefixWord ++ tailWord_3863267).sum := by decide
  have hdescent : baseEnd_3863267 < baseStart_3863267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863306 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 2, 3, 3]
def baseStart_3863306 : Nat := 118140960795 + 3863306 * 2 ^ 59
def prefixEnd_3863306 : Nat := 4983230072969 + 3 ^ 40 * 3863306 * 2
def baseEnd_3863306 : Nat := 1983732893398767031207985

theorem tailTrace_3863306 : CollatzResearch.WordTrace tailWord_3863306 prefixEnd_3863306 1983732893398767031207985 := by
  unfold tailWord_3863306
  simp only [CollatzResearch.WordTrace]
  refine ⟨35226586435477409245134443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93937563827939757987025181 35226586435477409245134443)
  ·
    refine ⟨52839879653216113867701665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35226586435477409245134443 52839879653216113867701665)
    ·
      refine ⟨39629909739912085400776249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52839879653216113867701665 39629909739912085400776249)
      ·
        refine ⟨29722432304934064050582187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39629909739912085400776249 29722432304934064050582187)
        ·
          refine ⟨44583648457401096075873281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29722432304934064050582187 44583648457401096075873281)
          ·
            refine ⟨33437736343050822056904961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44583648457401096075873281 33437736343050822056904961)
            ·
              refine ⟨25078302257288116542678721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33437736343050822056904961 25078302257288116542678721)
              ·
                refine ⟨18808726692966087407009041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25078302257288116542678721 18808726692966087407009041)
                ·
                  refine ⟨14106545019724565555256781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18808726692966087407009041 14106545019724565555256781)
                  ·
                    refine ⟨5289954382396712083221293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14106545019724565555256781 5289954382396712083221293)
                    ·
                      refine ⟨1983732893398767031207985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5289954382396712083221293 1983732893398767031207985)
                      ·
                        rfl

theorem cell23_3863306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_3863306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863306 prefixEnd_3863306 := by exact prefixLift 3863306
  have htrace : WordTrace (prefixWord ++ tailWord_3863306) baseStart_3863306 baseEnd_3863306 := by
    simpa [prefixWord, tailWord_3863306, baseEnd_3863306] using wordTrace_append hprefix tailTrace_3863306
  have hstable : (prefixWord ++ tailWord_3863306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863306).length < 2 ^ (prefixWord ++ tailWord_3863306).sum := by decide
  have hdescent : baseEnd_3863306 < baseStart_3863306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863313 : List Nat := [1, 2, 2, 1, 1, 3, 6, 2, 5]
def baseStart_3863313 : Nat := 118140960795 + 3863313 * 2 ^ 59
def prefixEnd_3863313 : Nat := 4983230072969 + 3 ^ 40 * 3863313 * 2
def baseEnd_3863313 : Nat := 220415165307038722646717

theorem tailTrace_3863313 : CollatzResearch.WordTrace tailWord_3863313 prefixEnd_3863313 220415165307038722646717 := by
  unfold tailWord_3863313
  simp only [CollatzResearch.WordTrace]
  refine ⟨140906601052884277176042593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93937734035256184784028395 140906601052884277176042593)
  ·
    refine ⟨105679950789663207882031945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140906601052884277176042593 105679950789663207882031945)
    ·
      refine ⟨79259963092247405911523959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105679950789663207882031945 79259963092247405911523959)
      ·
        refine ⟨118889944638371108867285939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79259963092247405911523959 118889944638371108867285939)
        ·
          refine ⟨178334916957556663300928909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118889944638371108867285939 178334916957556663300928909)
          ·
            refine ⟨66875593859083748737848341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178334916957556663300928909 66875593859083748737848341)
            ·
              refine ⟨3134793462144550722086641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66875593859083748737848341 3134793462144550722086641)
              ·
                refine ⟨2351095096608413041564981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3134793462144550722086641 2351095096608413041564981)
                ·
                  refine ⟨220415165307038722646717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2351095096608413041564981 220415165307038722646717)
                  ·
                    rfl

theorem cell23_3863313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 5].length) (baseStart_3863313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863313 prefixEnd_3863313 := by exact prefixLift 3863313
  have htrace : WordTrace (prefixWord ++ tailWord_3863313) baseStart_3863313 baseEnd_3863313 := by
    simpa [prefixWord, tailWord_3863313, baseEnd_3863313] using wordTrace_append hprefix tailTrace_3863313
  have hstable : (prefixWord ++ tailWord_3863313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863313).length < 2 ^ (prefixWord ++ tailWord_3863313).sum := by decide
  have hdescent : baseEnd_3863313 < baseStart_3863313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863346 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4]
def baseStart_3863346 : Nat := 118140960795 + 3863346 * 2 ^ 59
def prefixEnd_3863346 : Nat := 4983230072969 + 3 ^ 40 * 3863346 * 2
def baseEnd_3863346 : Nat := 1983753432624946874707801

theorem tailTrace_3863346 : CollatzResearch.WordTrace tailWord_3863346 prefixEnd_3863346 1983753432624946874707801 := by
  unfold tailWord_3863346
  simp only [CollatzResearch.WordTrace]
  refine ⟨35226951165441180952998473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93938536441176482541329261 35226951165441180952998473)
  ·
    refine ⟨26420213374080885714748855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35226951165441180952998473 26420213374080885714748855)
    ·
      refine ⟨39630320061121328572123283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26420213374080885714748855 39630320061121328572123283)
      ·
        refine ⟨59445480091681992858184925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39630320061121328572123283 59445480091681992858184925)
        ·
          refine ⟨22292055034380747321819347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59445480091681992858184925 22292055034380747321819347)
          ·
            refine ⟨33438082551571120982729021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22292055034380747321819347 33438082551571120982729021)
            ·
              refine ⟨12539280956839170368523383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33438082551571120982729021 12539280956839170368523383)
              ·
                refine ⟨18808921435258755552785075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12539280956839170368523383 18808921435258755552785075)
                ·
                  refine ⟨28213382152888133329177613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18808921435258755552785075 28213382152888133329177613)
                  ·
                    refine ⟨10580018307333049998441605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28213382152888133329177613 10580018307333049998441605)
                    ·
                      refine ⟨1983753432624946874707801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10580018307333049998441605 1983753432624946874707801)
                      ·
                        rfl

theorem cell23_3863346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_3863346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863346 prefixEnd_3863346 := by exact prefixLift 3863346
  have htrace : WordTrace (prefixWord ++ tailWord_3863346) baseStart_3863346 baseEnd_3863346 := by
    simpa [prefixWord, tailWord_3863346, baseEnd_3863346] using wordTrace_append hprefix tailTrace_3863346
  have hstable : (prefixWord ++ tailWord_3863346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863346).length < 2 ^ (prefixWord ++ tailWord_3863346).sum := by decide
  have hdescent : baseEnd_3863346 < baseStart_3863346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863356 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 7, 4]
def baseStart_3863356 : Nat := 118140960795 + 3863356 * 2 ^ 59
def prefixEnd_3863356 : Nat := 4983230072969 + 3 ^ 40 * 3863356 * 2
def baseEnd_3863356 : Nat := 661252855810497278527585

theorem tailTrace_3863356 : CollatzResearch.WordTrace tailWord_3863356 prefixEnd_3863356 661252855810497278527585 := by
  unfold tailWord_3863356
  simp only [CollatzResearch.WordTrace]
  refine ⟨70454084695864247759928961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93938779594485663679905281 70454084695864247759928961)
  ·
    refine ⟨52840563521898185819946721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70454084695864247759928961 52840563521898185819946721)
    ·
      refine ⟨39630422641423639364960041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52840563521898185819946721 39630422641423639364960041)
      ·
        refine ⟨29722816981067729523720031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39630422641423639364960041 29722816981067729523720031)
        ·
          refine ⟨44584225471601594285580047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29722816981067729523720031 44584225471601594285580047)
          ·
            refine ⟨66876338207402391428370071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44584225471601594285580047 66876338207402391428370071)
            ·
              refine ⟨100314507311103587142555107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66876338207402391428370071 100314507311103587142555107)
              ·
                refine ⟨150471760966655380713832661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100314507311103587142555107 150471760966655380713832661)
                ·
                  refine ⟨3526681897655985485480453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 150471760966655380713832661 3526681897655985485480453)
                  ·
                    refine ⟨661252855810497278527585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3526681897655985485480453 661252855810497278527585)
                    ·
                      rfl

theorem cell23_3863356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_3863356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863356 prefixEnd_3863356 := by exact prefixLift 3863356
  have htrace : WordTrace (prefixWord ++ tailWord_3863356) baseStart_3863356 baseEnd_3863356 := by
    simpa [prefixWord, tailWord_3863356, baseEnd_3863356] using wordTrace_append hprefix tailTrace_3863356
  have hstable : (prefixWord ++ tailWord_3863356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863356).length < 2 ^ (prefixWord ++ tailWord_3863356).sum := by decide
  have hdescent : baseEnd_3863356 < baseStart_3863356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863423 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 4, 3, 2]
def baseStart_3863423 : Nat := 118140960795 + 3863423 * 2 ^ 59
def prefixEnd_3863423 : Nat := 4983230072969 + 3 ^ 40 * 3863423 * 2
def baseEnd_3863423 : Nat := 1983792970635343073444947

theorem tailTrace_3863423 : CollatzResearch.WordTrace tailWord_3863423 prefixEnd_3863423 1983792970635343073444947 := by
  unfold tailWord_3863423
  simp only [CollatzResearch.WordTrace]
  refine ⟨140910613082485765962546923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93940408721657177308364615 140910613082485765962546923)
  ·
    refine ⟨211365919623728648943820385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140910613082485765962546923 211365919623728648943820385)
    ·
      refine ⟨158524439717796486707865289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211365919623728648943820385 158524439717796486707865289)
      ·
        refine ⟨118893329788347365030898967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158524439717796486707865289 118893329788347365030898967)
        ·
          refine ⟨178339994682521047546348451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118893329788347365030898967 178339994682521047546348451)
          ·
            refine ⟨267509992023781571319522677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178339994682521047546348451 267509992023781571319522677)
            ·
              refine ⟨25079061752229522311205251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 267509992023781571319522677 25079061752229522311205251)
              ·
                refine ⟨37618592628344283466807877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25079061752229522311205251 37618592628344283466807877)
                ·
                  refine ⟨7053486117814553150026477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37618592628344283466807877 7053486117814553150026477)
                  ·
                    refine ⟨2645057294180457431259929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7053486117814553150026477 2645057294180457431259929)
                    ·
                      refine ⟨1983792970635343073444947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2645057294180457431259929 1983792970635343073444947)
                      ·
                        rfl

theorem cell23_3863423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 3, 2].length) (baseStart_3863423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863423 prefixEnd_3863423 := by exact prefixLift 3863423
  have htrace : WordTrace (prefixWord ++ tailWord_3863423) baseStart_3863423 baseEnd_3863423 := by
    simpa [prefixWord, tailWord_3863423, baseEnd_3863423] using wordTrace_append hprefix tailTrace_3863423
  have hstable : (prefixWord ++ tailWord_3863423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863423).length < 2 ^ (prefixWord ++ tailWord_3863423).sum := by decide
  have hdescent : baseEnd_3863423 < baseStart_3863423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863453 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_3863453 : Nat := 118140960795 + 3863453 * 2 ^ 59
def prefixEnd_3863453 : Nat := 4983230072969 + 3 ^ 40 * 3863453 * 2
def baseEnd_3863453 : Nat := 1983808375054977956069809

theorem tailTrace_3863453 : CollatzResearch.WordTrace tailWord_3863453 prefixEnd_3863453 1983808375054977956069809 := by
  unfold tailWord_3863453
  simp only [CollatzResearch.WordTrace]
  refine ⟨140911707272377081086139013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93941138181584720724092675 140911707272377081086139013)
  ·
    refine ⟨26420945113570702703651065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140911707272377081086139013 26420945113570702703651065)
    ·
      refine ⟨19815708835178027027738299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26420945113570702703651065 19815708835178027027738299)
      ·
        refine ⟨29723563252767040541607449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19815708835178027027738299 29723563252767040541607449)
        ·
          refine ⟨22292672439575280406205587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29723563252767040541607449 22292672439575280406205587)
          ·
            refine ⟨33439008659362920609308381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22292672439575280406205587 33439008659362920609308381)
            ·
              refine ⟨12539628247261095228490643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33439008659362920609308381 12539628247261095228490643)
              ·
                refine ⟨18809442370891642842735965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12539628247261095228490643 18809442370891642842735965)
                ·
                  refine ⟨7053540889084366066025987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18809442370891642842735965 7053540889084366066025987)
                  ·
                    refine ⟨10580311333626549099038981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7053540889084366066025987 10580311333626549099038981)
                    ·
                      refine ⟨1983808375054977956069809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10580311333626549099038981 1983808375054977956069809)
                      ·
                        rfl

theorem cell23_3863453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_3863453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863453 prefixEnd_3863453 := by exact prefixLift 3863453
  have htrace : WordTrace (prefixWord ++ tailWord_3863453) baseStart_3863453 baseEnd_3863453 := by
    simpa [prefixWord, tailWord_3863453, baseEnd_3863453] using wordTrace_append hprefix tailTrace_3863453
  have hstable : (prefixWord ++ tailWord_3863453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863453).length < 2 ^ (prefixWord ++ tailWord_3863453).sum := by decide
  have hdescent : baseEnd_3863453 < baseStart_3863453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863456 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 5]
def baseStart_3863456 : Nat := 118140960795 + 3863456 * 2 ^ 59
def prefixEnd_3863456 : Nat := 4983230072969 + 3 ^ 40 * 3863456 * 2
def baseEnd_3863456 : Nat := 1983809915496941444332295

theorem tailTrace_3863456 : CollatzResearch.WordTrace tailWord_3863456 prefixEnd_3863456 1983809915496941444332295 := by
  unfold tailWord_3863456
  simp only [CollatzResearch.WordTrace]
  refine ⟨70455908345683106299249111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93941211127577475065665481 70455908345683106299249111)
  ·
    refine ⟨105683862518524659448873667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70455908345683106299249111 105683862518524659448873667)
    ·
      refine ⟨158525793777786989173310501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105683862518524659448873667 158525793777786989173310501)
      ·
        refine ⟨29723586333335060469995719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158525793777786989173310501 29723586333335060469995719)
        ·
          refine ⟨44585379500002590704993579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29723586333335060469995719 44585379500002590704993579)
          ·
            refine ⟨66878069250003886057490369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44585379500002590704993579 66878069250003886057490369)
            ·
              refine ⟨50158551937502914543117777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66878069250003886057490369 50158551937502914543117777)
              ·
                refine ⟨37618913953127185907338333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50158551937502914543117777 37618913953127185907338333)
                ·
                  refine ⟨14107092732422694715251875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37618913953127185907338333 14107092732422694715251875)
                  ·
                    refine ⟨21160639098634042072877813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14107092732422694715251875 21160639098634042072877813)
                    ·
                      refine ⟨1983809915496941444332295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21160639098634042072877813 1983809915496941444332295)
                      ·
                        rfl

theorem cell23_3863456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_3863456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863456 prefixEnd_3863456 := by exact prefixLift 3863456
  have htrace : WordTrace (prefixWord ++ tailWord_3863456) baseStart_3863456 baseEnd_3863456 := by
    simpa [prefixWord, tailWord_3863456, baseEnd_3863456] using wordTrace_append hprefix tailTrace_3863456
  have hstable : (prefixWord ++ tailWord_3863456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863456).length < 2 ^ (prefixWord ++ tailWord_3863456).sum := by decide
  have hdescent : baseEnd_3863456 < baseStart_3863456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863457 : List Nat := [1, 2, 3, 4, 1, 2, 2, 1, 2, 3, 2]
def baseStart_3863457 : Nat := 118140960795 + 3863457 * 2 ^ 59
def prefixEnd_3863457 : Nat := 4983230072969 + 3 ^ 40 * 3863457 * 2
def baseEnd_3863457 : Nat := 1983810428977595940419791

theorem tailTrace_3863457 : CollatzResearch.WordTrace tailWord_3863457 prefixEnd_3863457 1983810428977595940419791 := by
  unfold tailWord_3863457
  simp only [CollatzResearch.WordTrace]
  refine ⟨140911853164362589769284625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93941235442908393179523083 140911853164362589769284625)
  ·
    refine ⟨105683889873271942326963469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140911853164362589769284625 105683889873271942326963469)
    ·
      refine ⟨39631458702476978372611301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105683889873271942326963469 39631458702476978372611301)
      ·
        refine ⟨7430898506714433444864619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39631458702476978372611301 7430898506714433444864619)
        ·
          refine ⟨11146347760071650167296929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7430898506714433444864619 11146347760071650167296929)
          ·
            refine ⟨8359760820053737625472697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11146347760071650167296929 8359760820053737625472697)
            ·
              refine ⟨6269820615040303219104523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8359760820053737625472697 6269820615040303219104523)
              ·
                refine ⟨9404730922560454828656785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6269820615040303219104523 9404730922560454828656785)
                ·
                  refine ⟨7053548191920341121492589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9404730922560454828656785 7053548191920341121492589)
                  ·
                    refine ⟨2645080571970127920559721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7053548191920341121492589 2645080571970127920559721)
                    ·
                      refine ⟨1983810428977595940419791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2645080571970127920559721 1983810428977595940419791)
                      ·
                        rfl

theorem cell23_3863457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_3863457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863457 prefixEnd_3863457 := by exact prefixLift 3863457
  have htrace : WordTrace (prefixWord ++ tailWord_3863457) baseStart_3863457 baseEnd_3863457 := by
    simpa [prefixWord, tailWord_3863457, baseEnd_3863457] using wordTrace_append hprefix tailTrace_3863457
  have hstable : (prefixWord ++ tailWord_3863457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863457).length < 2 ^ (prefixWord ++ tailWord_3863457).sum := by decide
  have hdescent : baseEnd_3863457 < baseStart_3863457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863480 : List Nat := [2, 1, 2, 1, 2, 5, 2, 2, 2, 4]
def baseStart_3863480 : Nat := 118140960795 + 3863480 * 2 ^ 59
def prefixEnd_3863480 : Nat := 4983230072969 + 3 ^ 40 * 3863480 * 2
def baseEnd_3863480 : Nat := 661274079677549783477395

theorem tailTrace_3863480 : CollatzResearch.WordTrace tailWord_3863480 prefixEnd_3863480 661274079677549783477395 := by
  unfold tailWord_3863480
  simp only [CollatzResearch.WordTrace]
  refine ⟨70456346021639632348685947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93941794695519509798247929 70456346021639632348685947)
  ·
    refine ⟨105684519032459448523028921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70456346021639632348685947 105684519032459448523028921)
    ·
      refine ⟨79263389274344586392271691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105684519032459448523028921 79263389274344586392271691)
      ·
        refine ⟨118895083911516879588407537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79263389274344586392271691 118895083911516879588407537)
        ·
          refine ⟨89171312933637659691305653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118895083911516879588407537 89171312933637659691305653)
          ·
            refine ⟨8359810587528530596059905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89171312933637659691305653 8359810587528530596059905)
            ·
              refine ⟨6269857940646397947044929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8359810587528530596059905 6269857940646397947044929)
              ·
                refine ⟨4702393455484798460283697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6269857940646397947044929 4702393455484798460283697)
                ·
                  refine ⟨3526795091613598845212773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4702393455484798460283697 3526795091613598845212773)
                  ·
                    refine ⟨661274079677549783477395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3526795091613598845212773 661274079677549783477395)
                    ·
                      rfl

theorem cell23_3863480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 2, 4].length) (baseStart_3863480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863480 prefixEnd_3863480 := by exact prefixLift 3863480
  have htrace : WordTrace (prefixWord ++ tailWord_3863480) baseStart_3863480 baseEnd_3863480 := by
    simpa [prefixWord, tailWord_3863480, baseEnd_3863480] using wordTrace_append hprefix tailTrace_3863480
  have hstable : (prefixWord ++ tailWord_3863480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863480).length < 2 ^ (prefixWord ++ tailWord_3863480).sum := by decide
  have hdescent : baseEnd_3863480 < baseStart_3863480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863503 : List Nat := [1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 3]
def baseStart_3863503 : Nat := 118140960795 + 3863503 * 2 ^ 59
def prefixEnd_3863503 : Nat := 4983230072969 + 3 ^ 40 * 3863503 * 2
def baseEnd_3863503 : Nat := 1983834049087702760444579

theorem tailTrace_3863503 : CollatzResearch.WordTrace tailWord_3863503 prefixEnd_3863503 1983834049087702760444579 := by
  unfold tailWord_3863503
  simp only [CollatzResearch.WordTrace]
  refine ⟨140913530922195939625459163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93942353948130626416972775 140913530922195939625459163)
  ·
    refine ⟨211370296383293909438188745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140913530922195939625459163 211370296383293909438188745)
    ·
      refine ⟨158527722287470432078641559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211370296383293909438188745 158527722287470432078641559)
      ·
        refine ⟨237791583431205648117962339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158527722287470432078641559 237791583431205648117962339)
        ·
          refine ⟨356687375146808472176943509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237791583431205648117962339 356687375146808472176943509)
          ·
            refine ⟨16719720710006647133294227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 356687375146808472176943509 16719720710006647133294227)
            ·
              refine ⟨25079581065009970699941341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16719720710006647133294227 25079581065009970699941341)
              ·
                refine ⟨9404842899378739012478003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25079581065009970699941341 9404842899378739012478003)
                ·
                  refine ⟨14107264349068108518717005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9404842899378739012478003 14107264349068108518717005)
                  ·
                    refine ⟨5290224130900540694518877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14107264349068108518717005 5290224130900540694518877)
                    ·
                      refine ⟨1983834049087702760444579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5290224130900540694518877 1983834049087702760444579)
                      ·
                        rfl

theorem cell23_3863503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 3].length) (baseStart_3863503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863503 prefixEnd_3863503 := by exact prefixLift 3863503
  have htrace : WordTrace (prefixWord ++ tailWord_3863503) baseStart_3863503 baseEnd_3863503 := by
    simpa [prefixWord, tailWord_3863503, baseEnd_3863503] using wordTrace_append hprefix tailTrace_3863503
  have hstable : (prefixWord ++ tailWord_3863503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863503).length < 2 ^ (prefixWord ++ tailWord_3863503).sum := by decide
  have hdescent : baseEnd_3863503 < baseStart_3863503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863537 : List Nat := [1, 2, 2, 2, 4, 1, 3, 2, 2, 1, 3]
def baseStart_3863537 : Nat := 118140960795 + 3863537 * 2 ^ 59
def prefixEnd_3863537 : Nat := 4983230072969 + 3 ^ 40 * 3863537 * 2
def baseEnd_3863537 : Nat := 1983851507429955627419423

theorem tailTrace_3863537 : CollatzResearch.WordTrace tailWord_3863537 prefixEnd_3863537 1983851507429955627419423 := by
  unfold tailWord_3863537
  simp only [CollatzResearch.WordTrace]
  refine ⟨140914771004072763432196865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93943180669381842288131243 140914771004072763432196865)
  ·
    refine ⟨105686078253054572574147649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140914771004072763432196865 105686078253054572574147649)
    ·
      refine ⟨79264558689790929430610737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105686078253054572574147649 79264558689790929430610737)
      ·
        refine ⟨59448419017343197072958053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79264558689790929430610737 59448419017343197072958053)
        ·
          refine ⟨11146578565751849451179635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59448419017343197072958053 11146578565751849451179635)
          ·
            refine ⟨16719867848627774176769453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11146578565751849451179635 16719867848627774176769453)
            ·
              refine ⟨6269950443235415316288545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16719867848627774176769453 6269950443235415316288545)
              ·
                refine ⟨4702462832426561487216409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6269950443235415316288545 4702462832426561487216409)
                ·
                  refine ⟨3526847124319921115412307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4702462832426561487216409 3526847124319921115412307)
                  ·
                    refine ⟨5290270686479881673118461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3526847124319921115412307 5290270686479881673118461)
                    ·
                      refine ⟨1983851507429955627419423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5290270686479881673118461 1983851507429955627419423)
                      ·
                        rfl

theorem cell23_3863537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_3863537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863537 prefixEnd_3863537 := by exact prefixLift 3863537
  have htrace : WordTrace (prefixWord ++ tailWord_3863537) baseStart_3863537 baseEnd_3863537 := by
    simpa [prefixWord, tailWord_3863537, baseEnd_3863537] using wordTrace_append hprefix tailTrace_3863537
  have hstable : (prefixWord ++ tailWord_3863537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863537).length < 2 ^ (prefixWord ++ tailWord_3863537).sum := by decide
  have hdescent : baseEnd_3863537 < baseStart_3863537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863543 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 1, 10, 2]
def baseStart_3863543 : Nat := 118140960795 + 3863543 * 2 ^ 59
def prefixEnd_3863543 : Nat := 4983230072969 + 3 ^ 40 * 3863543 * 2
def baseEnd_3863543 : Nat := 1983854588313882603944395

theorem tailTrace_3863543 : CollatzResearch.WordTrace tailWord_3863543 prefixEnd_3863543 1983854588313882603944395 := by
  unfold tailWord_3863543
  simp only [CollatzResearch.WordTrace]
  refine ⟨140914989842051026456915283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93943326561367350971276855 140914989842051026456915283)
  ·
    refine ⟨211372484763076539685372925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140914989842051026456915283 211372484763076539685372925)
    ·
      refine ⟨79264681786153702382014847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211372484763076539685372925 79264681786153702382014847)
      ·
        refine ⟨118897022679230553573022271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79264681786153702382014847 118897022679230553573022271)
        ·
          refine ⟨178345534018845830359533407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118897022679230553573022271 178345534018845830359533407)
          ·
            refine ⟨267518301028268745539300111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178345534018845830359533407 267518301028268745539300111)
            ·
              refine ⟨401277451542403118308950167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267518301028268745539300111 401277451542403118308950167)
              ·
                refine ⟨601916177313604677463425251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401277451542403118308950167 601916177313604677463425251)
                ·
                  refine ⟨902874265970407016195137877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601916177313604677463425251 902874265970407016195137877)
                  ·
                    refine ⟨2645139451085176805259193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 902874265970407016195137877 2645139451085176805259193)
                    ·
                      refine ⟨1983854588313882603944395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2645139451085176805259193 1983854588313882603944395)
                      ·
                        rfl

theorem cell23_3863543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 10, 2].length) (baseStart_3863543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863543 prefixEnd_3863543 := by exact prefixLift 3863543
  have htrace : WordTrace (prefixWord ++ tailWord_3863543) baseStart_3863543 baseEnd_3863543 := by
    simpa [prefixWord, tailWord_3863543, baseEnd_3863543] using wordTrace_append hprefix tailTrace_3863543
  have hstable : (prefixWord ++ tailWord_3863543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863543).length < 2 ^ (prefixWord ++ tailWord_3863543).sum := by decide
  have hdescent : baseEnd_3863543 < baseStart_3863543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863553 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 2, 6]
def baseStart_3863553 : Nat := 118140960795 + 3863553 * 2 ^ 59
def prefixEnd_3863553 : Nat := 4983230072969 + 3 ^ 40 * 3863553 * 2
def baseEnd_3863553 : Nat := 661286574373475854939783

theorem tailTrace_3863553 : CollatzResearch.WordTrace tailWord_3863553 prefixEnd_3863553 661286574373475854939783 := by
  unfold tailWord_3863553
  simp only [CollatzResearch.WordTrace]
  refine ⟨140915354572014798164779313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93943569714676532109852875 140915354572014798164779313)
  ·
    refine ⟨105686515929011098623584485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140915354572014798164779313 105686515929011098623584485)
    ·
      refine ⟨19816221736689580991922091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105686515929011098623584485 19816221736689580991922091)
      ·
        refine ⟨29724332605034371487883137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19816221736689580991922091 29724332605034371487883137)
        ·
          refine ⟨22293249453775778615912353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29724332605034371487883137 22293249453775778615912353)
          ·
            refine ⟨16719937090331833961934265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22293249453775778615912353 16719937090331833961934265)
            ·
              refine ⟨12539952817748875471450699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16719937090331833961934265 12539952817748875471450699)
              ·
                refine ⟨18809929226623313207176049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12539952817748875471450699 18809929226623313207176049)
                ·
                  refine ⟨14107446919967484905382037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18809929226623313207176049 14107446919967484905382037)
                  ·
                    refine ⟨661286574373475854939783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14107446919967484905382037 661286574373475854939783)
                    ·
                      rfl

theorem cell23_3863553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_3863553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863553 prefixEnd_3863553 := by exact prefixLift 3863553
  have htrace : WordTrace (prefixWord ++ tailWord_3863553) baseStart_3863553 baseEnd_3863553 := by
    simpa [prefixWord, tailWord_3863553, baseEnd_3863553] using wordTrace_append hprefix tailTrace_3863553
  have hstable : (prefixWord ++ tailWord_3863553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863553).length < 2 ^ (prefixWord ++ tailWord_3863553).sum := by decide
  have hdescent : baseEnd_3863553 < baseStart_3863553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863580 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 2, 1, 5]
def baseStart_3863580 : Nat := 118140960795 + 3863580 * 2 ^ 59
def prefixEnd_3863580 : Nat := 4983230072969 + 3 ^ 40 * 3863580 * 2
def baseEnd_3863580 : Nat := 1983873587098098959181725

theorem tailTrace_3863580 : CollatzResearch.WordTrace tailWord_3863580 prefixEnd_3863580 1983873587098098959181725 := by
  unfold tailWord_3863580
  simp only [CollatzResearch.WordTrace]
  refine ⟨70458169671458490888006097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93944226228611321184008129 70458169671458490888006097)
  ·
    refine ⟨52843627253593868166004573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70458169671458490888006097 52843627253593868166004573)
    ·
      refine ⟨19816360220097700562251715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52843627253593868166004573 19816360220097700562251715)
      ·
        refine ⟨29724540330146550843377573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19816360220097700562251715 29724540330146550843377573)
        ·
          refine ⟨5573351311902478283133295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29724540330146550843377573 5573351311902478283133295)
          ·
            refine ⟨8360026967853717424699943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5573351311902478283133295 8360026967853717424699943)
            ·
              refine ⟨12540040451780576137049915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8360026967853717424699943 12540040451780576137049915)
              ·
                refine ⟨18810060677670864205574873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12540040451780576137049915 18810060677670864205574873)
                ·
                  refine ⟨14107545508253148154181155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18810060677670864205574873 14107545508253148154181155)
                  ·
                    refine ⟨21161318262379722231271733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14107545508253148154181155 21161318262379722231271733)
                    ·
                      refine ⟨1983873587098098959181725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21161318262379722231271733 1983873587098098959181725)
                      ·
                        rfl

theorem cell23_3863580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_3863580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863580 prefixEnd_3863580 := by exact prefixLift 3863580
  have htrace : WordTrace (prefixWord ++ tailWord_3863580) baseStart_3863580 baseEnd_3863580 := by
    simpa [prefixWord, tailWord_3863580, baseEnd_3863580] using wordTrace_append hprefix tailTrace_3863580
  have hstable : (prefixWord ++ tailWord_3863580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863580).length < 2 ^ (prefixWord ++ tailWord_3863580).sum := by decide
  have hdescent : baseEnd_3863580 < baseStart_3863580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863630 : List Nat := [4, 1, 1, 1, 1, 3, 4, 1, 2, 5]
def baseStart_3863630 : Nat := 118140960795 + 3863630 * 2 ^ 59
def prefixEnd_3863630 : Nat := 4983230072969 + 3 ^ 40 * 3863630 * 2
def baseEnd_3863630 : Nat := 661299753710274587852165

theorem tailTrace_3863630 : CollatzResearch.WordTrace tailWord_3863630 prefixEnd_3863630 661299753710274587852165 := by
  unfold tailWord_3863630
  simp only [CollatzResearch.WordTrace]
  refine ⟨17614770374091980039416543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93945441995157226876888229 17614770374091980039416543)
  ·
    refine ⟨26422155561137970059124815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17614770374091980039416543 26422155561137970059124815)
    ·
      refine ⟨39633233341706955088687223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26422155561137970059124815 39633233341706955088687223)
      ·
        refine ⟨59449850012560432633030835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39633233341706955088687223 59449850012560432633030835)
        ·
          refine ⟨89174775018840648949546253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59449850012560432633030835 89174775018840648949546253)
          ·
            refine ⟨33440540632065243356079845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89174775018840648949546253 33440540632065243356079845)
            ·
              refine ⟨6270101368512233129264971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33440540632065243356079845 6270101368512233129264971)
              ·
                refine ⟨9405152052768349693897457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6270101368512233129264971 9405152052768349693897457)
                ·
                  refine ⟨7053864039576262270423093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9405152052768349693897457 7053864039576262270423093)
                  ·
                    refine ⟨661299753710274587852165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7053864039576262270423093 661299753710274587852165)
                    ·
                      rfl

theorem cell23_3863630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_3863630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863630 prefixEnd_3863630 := by exact prefixLift 3863630
  have htrace : WordTrace (prefixWord ++ tailWord_3863630) baseStart_3863630 baseEnd_3863630 := by
    simpa [prefixWord, tailWord_3863630, baseEnd_3863630] using wordTrace_append hprefix tailTrace_3863630
  have hstable : (prefixWord ++ tailWord_3863630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863630).length < 2 ^ (prefixWord ++ tailWord_3863630).sum := by decide
  have hdescent : baseEnd_3863630 < baseStart_3863630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863633 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 1, 3, 4]
def baseStart_3863633 : Nat := 118140960795 + 3863633 * 2 ^ 59
def prefixEnd_3863633 : Nat := 4983230072969 + 3 ^ 40 * 3863633 * 2
def baseEnd_3863633 : Nat := 1983900801572787251818981

theorem tailTrace_3863633 : CollatzResearch.WordTrace tailWord_3863633 prefixEnd_3863633 1983900801572787251818981 := by
  unfold tailWord_3863633
  simp only [CollatzResearch.WordTrace]
  refine ⟨140918272411724971827691553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93945514941149981218461035 140918272411724971827691553)
  ·
    refine ⟨105688704308793728870768665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140918272411724971827691553 105688704308793728870768665)
    ·
      refine ⟨79266528231595296653076499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105688704308793728870768665 79266528231595296653076499)
      ·
        refine ⟨118899792347392944979614749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79266528231595296653076499 118899792347392944979614749)
        ·
          refine ⟨44587422130272354367355531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118899792347392944979614749 44587422130272354367355531)
          ·
            refine ⟨66881133195408531551033297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44587422130272354367355531 66881133195408531551033297)
            ·
              refine ⟨50160849896556398663274973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66881133195408531551033297 50160849896556398663274973)
              ·
                refine ⟨18810318711208649498728115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50160849896556398663274973 18810318711208649498728115)
                ·
                  refine ⟨28215478066812974248092173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18810318711208649498728115 28215478066812974248092173)
                  ·
                    refine ⟨10580804275054865343034565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28215478066812974248092173 10580804275054865343034565)
                    ·
                      refine ⟨1983900801572787251818981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10580804275054865343034565 1983900801572787251818981)
                      ·
                        rfl

theorem cell23_3863633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_3863633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863633 prefixEnd_3863633 := by exact prefixLift 3863633
  have htrace : WordTrace (prefixWord ++ tailWord_3863633) baseStart_3863633 baseEnd_3863633 := by
    simpa [prefixWord, tailWord_3863633, baseEnd_3863633] using wordTrace_append hprefix tailTrace_3863633
  have hstable : (prefixWord ++ tailWord_3863633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863633).length < 2 ^ (prefixWord ++ tailWord_3863633).sum := by decide
  have hdescent : baseEnd_3863633 < baseStart_3863633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863653 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 2, 3, 5]
def baseStart_3863653 : Nat := 118140960795 + 3863653 * 2 ^ 59
def prefixEnd_3863653 : Nat := 4983230072969 + 3 ^ 40 * 3863653 * 2
def baseEnd_3863653 : Nat := 1983911071185877173568889

theorem tailTrace_3863653 : CollatzResearch.WordTrace tailWord_3863653 prefixEnd_3863653 1983911071185877173568889 := by
  unfold tailWord_3863653
  simp only [CollatzResearch.WordTrace]
  refine ⟨140919001871652515243419613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93946001247768343495613075 140919001871652515243419613)
  ·
    refine ⟨52844625701869693216282355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140919001871652515243419613 52844625701869693216282355)
    ·
      refine ⟨79266938552804539824423533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52844625701869693216282355 79266938552804539824423533)
      ·
        refine ⟨29725101957301702434158825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79266938552804539824423533 29725101957301702434158825)
        ·
          refine ⟨22293826467976276825619119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29725101957301702434158825 22293826467976276825619119)
          ·
            refine ⟨33440739701964415238428679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22293826467976276825619119 33440739701964415238428679)
            ·
              refine ⟨50161109552946622857643019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33440739701964415238428679 50161109552946622857643019)
              ·
                refine ⟨75241664329419934286464529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50161109552946622857643019 75241664329419934286464529)
                ·
                  refine ⟨56431248247064950714848397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75241664329419934286464529 56431248247064950714848397)
                  ·
                    refine ⟨21161718092649356518068149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56431248247064950714848397 21161718092649356518068149)
                    ·
                      refine ⟨1983911071185877173568889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21161718092649356518068149 1983911071185877173568889)
                      ·
                        rfl

theorem cell23_3863653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_3863653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863653 prefixEnd_3863653 := by exact prefixLift 3863653
  have htrace : WordTrace (prefixWord ++ tailWord_3863653) baseStart_3863653 baseEnd_3863653 := by
    simpa [prefixWord, tailWord_3863653, baseEnd_3863653] using wordTrace_append hprefix tailTrace_3863653
  have hstable : (prefixWord ++ tailWord_3863653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863653).length < 2 ^ (prefixWord ++ tailWord_3863653).sum := by decide
  have hdescent : baseEnd_3863653 < baseStart_3863653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863660 : List Nat := [2, 2, 1, 1, 3, 2, 2, 3, 3, 4]
def baseStart_3863660 : Nat := 118140960795 + 3863660 * 2 ^ 59
def prefixEnd_3863660 : Nat := 4983230072969 + 3 ^ 40 * 3863660 * 2
def baseEnd_3863660 : Nat := 661304888516819548727119

theorem tailTrace_3863660 : CollatzResearch.WordTrace tailWord_3863660 prefixEnd_3863660 661304888516819548727119 := by
  unfold tailWord_3863660
  simp only [CollatzResearch.WordTrace]
  refine ⟨70459628591313577719462217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93946171455084770292616289 70459628591313577719462217)
  ·
    refine ⟨52844721443485183289596663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70459628591313577719462217 52844721443485183289596663)
    ·
      refine ⟨79267082165227774934394995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52844721443485183289596663 79267082165227774934394995)
      ·
        refine ⟨118900623247841662401592493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79267082165227774934394995 118900623247841662401592493)
        ·
          refine ⟨44587733717940623400597185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118900623247841662401592493 44587733717940623400597185)
          ·
            refine ⟨33440800288455467550447889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44587733717940623400597185 33440800288455467550447889)
            ·
              refine ⟨25080600216341600662835917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33440800288455467550447889 25080600216341600662835917)
              ·
                refine ⟨9405225081128100248563469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25080600216341600662835917 9405225081128100248563469)
                ·
                  refine ⟨3526959405423037593211301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9405225081128100248563469 3526959405423037593211301)
                  ·
                    refine ⟨661304888516819548727119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3526959405423037593211301 661304888516819548727119)
                    ·
                      rfl

theorem cell23_3863660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 4].length) (baseStart_3863660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863660 prefixEnd_3863660 := by exact prefixLift 3863660
  have htrace : WordTrace (prefixWord ++ tailWord_3863660) baseStart_3863660 baseEnd_3863660 := by
    simpa [prefixWord, tailWord_3863660, baseEnd_3863660] using wordTrace_append hprefix tailTrace_3863660
  have hstable : (prefixWord ++ tailWord_3863660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863660).length < 2 ^ (prefixWord ++ tailWord_3863660).sum := by decide
  have hdescent : baseEnd_3863660 < baseStart_3863660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863694 : List Nat := [4, 1, 1, 3, 2, 1, 1, 5, 1, 4]
def baseStart_3863694 : Nat := 118140960795 + 3863694 * 2 ^ 59
def prefixEnd_3863694 : Nat := 4983230072969 + 3 ^ 40 * 3863694 * 2
def baseEnd_3863694 : Nat := 661310707964237171052067

theorem tailTrace_3863694 : CollatzResearch.WordTrace tailWord_3863694 prefixEnd_3863694 661310707964237171052067 := by
  unfold tailWord_3863694
  simp only [CollatzResearch.WordTrace]
  refine ⟨17615062158062997405707767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93946998176335986163774757 17615062158062997405707767)
  ·
    refine ⟨26422593237094496108561651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17615062158062997405707767 26422593237094496108561651)
    ·
      refine ⟨39633889855641744162842477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26422593237094496108561651 39633889855641744162842477)
      ·
        refine ⟨14862708695865654061065929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39633889855641744162842477 14862708695865654061065929)
        ·
          refine ⟨11147031521899240545799447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14862708695865654061065929 11147031521899240545799447)
          ·
            refine ⟨16720547282848860818699171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11147031521899240545799447 16720547282848860818699171)
            ·
              refine ⟨25080820924273291228048757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16720547282848860818699171 25080820924273291228048757)
              ·
                refine ⟨2351326961650621052629571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25080820924273291228048757 2351326961650621052629571)
                ·
                  refine ⟨3526990442475931578944357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2351326961650621052629571 3526990442475931578944357)
                  ·
                    refine ⟨661310707964237171052067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3526990442475931578944357 661310707964237171052067)
                    ·
                      rfl

theorem cell23_3863694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_3863694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863694 prefixEnd_3863694 := by exact prefixLift 3863694
  have htrace : WordTrace (prefixWord ++ tailWord_3863694) baseStart_3863694 baseEnd_3863694 := by
    simpa [prefixWord, tailWord_3863694, baseEnd_3863694] using wordTrace_append hprefix tailTrace_3863694
  have hstable : (prefixWord ++ tailWord_3863694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863694).length < 2 ^ (prefixWord ++ tailWord_3863694).sum := by decide
  have hdescent : baseEnd_3863694 < baseStart_3863694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863717 : List Nat := [1, 3, 1, 2, 1, 4, 1, 3, 3, 1, 3]
def baseStart_3863717 : Nat := 118140960795 + 3863717 * 2 ^ 59
def prefixEnd_3863717 : Nat := 4983230072969 + 3 ^ 40 * 3863717 * 2
def baseEnd_3863717 : Nat := 1983943933947764923168595

theorem tailTrace_3863717 : CollatzResearch.WordTrace tailWord_3863717 prefixEnd_3863717 1983943933947764923168595 := by
  unfold tailWord_3863717
  simp only [CollatzResearch.WordTrace]
  refine ⟨140921336143420654173749405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93947557428947102782499603 140921336143420654173749405)
  ·
    refine ⟨52845501053782745315156027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140921336143420654173749405 52845501053782745315156027)
    ·
      refine ⟨79268251580674117972734041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52845501053782745315156027 79268251580674117972734041)
      ·
        refine ⟨59451188685505588479550531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79268251580674117972734041 59451188685505588479550531)
        ·
          refine ⟨89176783028258382719325797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59451188685505588479550531 89176783028258382719325797)
          ·
            refine ⟨16720646817798446759873587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89176783028258382719325797 16720646817798446759873587)
            ·
              refine ⟨25080970226697670139810381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16720646817798446759873587 25080970226697670139810381)
              ·
                refine ⟨9405363835011626302428893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25080970226697670139810381 9405363835011626302428893)
                ·
                  refine ⟨3527011438129359863410835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9405363835011626302428893 3527011438129359863410835)
                  ·
                    refine ⟨5290517157194039795116253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3527011438129359863410835 5290517157194039795116253)
                    ·
                      refine ⟨1983943933947764923168595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5290517157194039795116253 1983943933947764923168595)
                      ·
                        rfl

theorem cell23_3863717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_3863717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863717 prefixEnd_3863717 := by exact prefixLift 3863717
  have htrace : WordTrace (prefixWord ++ tailWord_3863717) baseStart_3863717 baseEnd_3863717 := by
    simpa [prefixWord, tailWord_3863717, baseEnd_3863717] using wordTrace_append hprefix tailTrace_3863717
  have hstable : (prefixWord ++ tailWord_3863717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863717).length < 2 ^ (prefixWord ++ tailWord_3863717).sum := by decide
  have hdescent : baseEnd_3863717 < baseStart_3863717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863737 : List Nat := [1, 2, 1, 4, 1, 4, 2, 2, 1, 5]
def baseStart_3863737 : Nat := 118140960795 + 3863737 * 2 ^ 59
def prefixEnd_3863737 : Nat := 4983230072969 + 3 ^ 40 * 3863737 * 2
def baseEnd_3863737 : Nat := 661318067853618281639501

theorem tailTrace_3863737 : CollatzResearch.WordTrace tailWord_3863737 prefixEnd_3863737 661318067853618281639501 := by
  unfold tailWord_3863737
  simp only [CollatzResearch.WordTrace]
  refine ⟨140922065603348197589477465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93948043735565465059651643 140922065603348197589477465)
  ·
    refine ⟨105691549202511148192108099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140922065603348197589477465 105691549202511148192108099)
    ·
      refine ⟨158537323803766722288162149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105691549202511148192108099 158537323803766722288162149)
      ·
        refine ⟨29725748213206260429030403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158537323803766722288162149 29725748213206260429030403)
        ·
          refine ⟨44588622319809390643545605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29725748213206260429030403 44588622319809390643545605)
          ·
            refine ⟨8360366684964260745664801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44588622319809390643545605 8360366684964260745664801)
            ·
              refine ⟨6270275013723195559248601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8360366684964260745664801 6270275013723195559248601)
              ·
                refine ⟨4702706260292396669436451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6270275013723195559248601 4702706260292396669436451)
                ·
                  refine ⟨7054059390438595004154677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4702706260292396669436451 7054059390438595004154677)
                  ·
                    refine ⟨661318067853618281639501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7054059390438595004154677 661318067853618281639501)
                    ·
                      rfl

theorem cell23_3863737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 5].length) (baseStart_3863737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863737 prefixEnd_3863737 := by exact prefixLift 3863737
  have htrace : WordTrace (prefixWord ++ tailWord_3863737) baseStart_3863737 baseEnd_3863737 := by
    simpa [prefixWord, tailWord_3863737, baseEnd_3863737] using wordTrace_append hprefix tailTrace_3863737
  have hstable : (prefixWord ++ tailWord_3863737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863737).length < 2 ^ (prefixWord ++ tailWord_3863737).sum := by decide
  have hdescent : baseEnd_3863737 < baseStart_3863737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863768 : List Nat := [2, 1, 2, 2, 5, 1, 3, 2, 1, 1, 3]
def baseStart_3863768 : Nat := 118140960795 + 3863768 * 2 ^ 59
def prefixEnd_3863768 : Nat := 4983230072969 + 3 ^ 40 * 3863768 * 2
def baseEnd_3863768 : Nat := 1983970121461144223630861

theorem tailTrace_3863768 : CollatzResearch.WordTrace tailWord_3863768 prefixEnd_3863768 1983970121461144223630861 := by
  unfold tailWord_3863768
  simp only [CollatzResearch.WordTrace]
  refine ⟨70461598133117944941927979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93948797510823926589237305 70461598133117944941927979)
  ·
    refine ⟨105692397199676917412891969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70461598133117944941927979 105692397199676917412891969)
    ·
      refine ⟨79269297899757688059668977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105692397199676917412891969 79269297899757688059668977)
      ·
        refine ⟨59451973424818266044751733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79269297899757688059668977 59451973424818266044751733)
        ·
          refine ⟨5573622508576712441695475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59451973424818266044751733 5573622508576712441695475)
          ·
            refine ⟨8360433762865068662543213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5573622508576712441695475 8360433762865068662543213)
            ·
              refine ⟨3135162661074400748453705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8360433762865068662543213 3135162661074400748453705)
              ·
                refine ⟨2351371995805800561340279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3135162661074400748453705 2351371995805800561340279)
                ·
                  refine ⟨3527057993708700842010419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2351371995805800561340279 3527057993708700842010419)
                  ·
                    refine ⟨5290586990563051263015629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3527057993708700842010419 5290586990563051263015629)
                    ·
                      refine ⟨1983970121461144223630861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5290586990563051263015629 1983970121461144223630861)
                      ·
                        rfl

theorem cell23_3863768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 1, 1, 3].length) (baseStart_3863768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863768 prefixEnd_3863768 := by exact prefixLift 3863768
  have htrace : WordTrace (prefixWord ++ tailWord_3863768) baseStart_3863768 baseEnd_3863768 := by
    simpa [prefixWord, tailWord_3863768, baseEnd_3863768] using wordTrace_append hprefix tailTrace_3863768
  have hstable : (prefixWord ++ tailWord_3863768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863768).length < 2 ^ (prefixWord ++ tailWord_3863768).sum := by decide
  have hdescent : baseEnd_3863768 < baseStart_3863768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863791 : List Nat := [1, 1, 2, 1, 8, 1, 1, 2, 1, 1, 4]
def baseStart_3863791 : Nat := 118140960795 + 3863791 * 2 ^ 59
def prefixEnd_3863791 : Nat := 4983230072969 + 3 ^ 40 * 3863791 * 2
def baseEnd_3863791 : Nat := 1983981931516197633643255

theorem tailTrace_3863791 : CollatzResearch.WordTrace tailWord_3863791 prefixEnd_3863791 1983981931516197633643255 := by
  unfold tailWord_3863791
  simp only [CollatzResearch.WordTrace]
  refine ⟨140924035145152564811943227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93949356763435043207962151 140924035145152564811943227)
  ·
    refine ⟨211386052717728847217914841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140924035145152564811943227 211386052717728847217914841)
    ·
      refine ⟨158539539538296635413436131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211386052717728847217914841 158539539538296635413436131)
      ·
        refine ⟨237809309307444953120154197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158539539538296635413436131 237809309307444953120154197)
        ·
          refine ⟨2786827843446620544376807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 237809309307444953120154197 2786827843446620544376807)
          ·
            refine ⟨4180241765169930816565211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2786827843446620544376807 4180241765169930816565211)
            ·
              refine ⟨6270362647754896224847817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4180241765169930816565211 6270362647754896224847817)
              ·
                refine ⟨4702771985816172168635863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6270362647754896224847817 4702771985816172168635863)
                ·
                  refine ⟨7054157978724258252953795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4702771985816172168635863 7054157978724258252953795)
                  ·
                    refine ⟨10581236968086387379430693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7054157978724258252953795 10581236968086387379430693)
                    ·
                      refine ⟨1983981931516197633643255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10581236968086387379430693 1983981931516197633643255)
                      ·
                        rfl

theorem cell23_3863791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 1, 1, 4].length) (baseStart_3863791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863791 prefixEnd_3863791 := by exact prefixLift 3863791
  have htrace : WordTrace (prefixWord ++ tailWord_3863791) baseStart_3863791 baseEnd_3863791 := by
    simpa [prefixWord, tailWord_3863791, baseEnd_3863791] using wordTrace_append hprefix tailTrace_3863791
  have hstable : (prefixWord ++ tailWord_3863791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863791).length < 2 ^ (prefixWord ++ tailWord_3863791).sum := by decide
  have hdescent : baseEnd_3863791 < baseStart_3863791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863794 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 3, 2, 3]
def baseStart_3863794 : Nat := 118140960795 + 3863794 * 2 ^ 59
def prefixEnd_3863794 : Nat := 4983230072969 + 3 ^ 40 * 3863794 * 2
def baseEnd_3863794 : Nat := 1983983471958161121905741

theorem tailTrace_3863794 : CollatzResearch.WordTrace tailWord_3863794 prefixEnd_3863794 1983983471958161121905741 := by
  unfold tailWord_3863794
  simp only [CollatzResearch.WordTrace]
  refine ⟨35231036141035424081075609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93949429709427797549534957 35231036141035424081075609)
  ·
    refine ⟨26423277105776568060806707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35231036141035424081075609 26423277105776568060806707)
    ·
      refine ⟨39634915658664852091210061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26423277105776568060806707 39634915658664852091210061)
      ·
        refine ⟨14863093371999319534203773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39634915658664852091210061 14863093371999319534203773)
        ·
          refine ⟨5573660014499744825326415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14863093371999319534203773 5573660014499744825326415)
          ·
            refine ⟨8360490021749617237989623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5573660014499744825326415 8360490021749617237989623)
            ·
              refine ⟨12540735032624425856984435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8360490021749617237989623 12540735032624425856984435)
              ·
                refine ⟨18811102548936638785476653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12540735032624425856984435 18811102548936638785476653)
                ·
                  refine ⟨7054163455851239544553745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18811102548936638785476653 7054163455851239544553745)
                  ·
                    refine ⟨5290622591888429658415309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7054163455851239544553745 5290622591888429658415309)
                    ·
                      refine ⟨1983983471958161121905741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5290622591888429658415309 1983983471958161121905741)
                      ·
                        rfl

theorem cell23_3863794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_3863794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863794 prefixEnd_3863794 := by exact prefixLift 3863794
  have htrace : WordTrace (prefixWord ++ tailWord_3863794) baseStart_3863794 baseEnd_3863794 := by
    simpa [prefixWord, tailWord_3863794, baseEnd_3863794] using wordTrace_append hprefix tailTrace_3863794
  have hstable : (prefixWord ++ tailWord_3863794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863794).length < 2 ^ (prefixWord ++ tailWord_3863794).sum := by decide
  have hdescent : baseEnd_3863794 < baseStart_3863794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863807 : List Nat := [1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 3]
def baseStart_3863807 : Nat := 118140960795 + 3863807 * 2 ^ 59
def prefixEnd_3863807 : Nat := 4983230072969 + 3 ^ 40 * 3863807 * 2
def baseEnd_3863807 : Nat := 1983990147206669571043181

theorem tailTrace_3863807 : CollatzResearch.WordTrace tailWord_3863807 prefixEnd_3863807 1983990147206669571043181 := by
  unfold tailWord_3863807
  simp only [CollatzResearch.WordTrace]
  refine ⟨140924618713094599544525675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93949745808729733029683783 140924618713094599544525675)
  ·
    refine ⟨211386928069641899316788513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140924618713094599544525675 211386928069641899316788513)
    ·
      refine ⟨158540196052231424487591385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211386928069641899316788513 158540196052231424487591385)
      ·
        refine ⟨118905147039173568365693539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158540196052231424487591385 118905147039173568365693539)
        ·
          refine ⟨178357720558760352548540309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118905147039173568365693539 178357720558760352548540309)
          ·
            refine ⟨8360518151191891525712827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 178357720558760352548540309 8360518151191891525712827)
            ·
              refine ⟨12540777226787837288569241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8360518151191891525712827 12540777226787837288569241)
              ·
                refine ⟨9405582920090877966426931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12540777226787837288569241 9405582920090877966426931)
                ·
                  refine ⟨14108374380136316949640397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9405582920090877966426931 14108374380136316949640397)
                  ·
                    refine ⟨5290640392551118856115149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14108374380136316949640397 5290640392551118856115149)
                    ·
                      refine ⟨1983990147206669571043181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5290640392551118856115149 1983990147206669571043181)
                      ·
                        rfl

theorem cell23_3863807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 3].length) (baseStart_3863807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863807 prefixEnd_3863807 := by exact prefixLift 3863807
  have htrace : WordTrace (prefixWord ++ tailWord_3863807) baseStart_3863807 baseEnd_3863807 := by
    simpa [prefixWord, tailWord_3863807, baseEnd_3863807] using wordTrace_append hprefix tailTrace_3863807
  have hstable : (prefixWord ++ tailWord_3863807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863807).length < 2 ^ (prefixWord ++ tailWord_3863807).sum := by decide
  have hdescent : baseEnd_3863807 < baseStart_3863807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863834 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2]
def baseStart_3863834 : Nat := 118140960795 + 3863834 * 2 ^ 59
def prefixEnd_3863834 : Nat := 4983230072969 + 3 ^ 40 * 3863834 * 2
def baseEnd_3863834 : Nat := 1984004011184340965405557

theorem tailTrace_3863834 : CollatzResearch.WordTrace tailWord_3863834 prefixEnd_3863834 1984004011184340965405557 := by
  unfold tailWord_3863834
  simp only [CollatzResearch.WordTrace]
  refine ⟨35231400870999195788939639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93950402322664522103839037 35231400870999195788939639)
  ·
    refine ⟨52847101306498793683409459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35231400870999195788939639 52847101306498793683409459)
    ·
      refine ⟨79270651959748190525114189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52847101306498793683409459 79270651959748190525114189)
      ·
        refine ⟨29726494484905571446917821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79270651959748190525114189 29726494484905571446917821)
        ·
          refine ⟨11147435431839589292594183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29726494484905571446917821 11147435431839589292594183)
          ·
            refine ⟨16721153147759383938891275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11147435431839589292594183 16721153147759383938891275)
            ·
              refine ⟨25081729721639075908336913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16721153147759383938891275 25081729721639075908336913)
              ·
                refine ⟨18811297291229306931252685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25081729721639075908336913 18811297291229306931252685)
                ·
                  refine ⟨7054236484210990099219757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18811297291229306931252685 7054236484210990099219757)
                  ·
                    refine ⟨2645338681579121287207409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7054236484210990099219757 2645338681579121287207409)
                    ·
                      refine ⟨1984004011184340965405557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2645338681579121287207409 1984004011184340965405557)
                      ·
                        rfl

theorem cell23_3863834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_3863834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863834 prefixEnd_3863834 := by exact prefixLift 3863834
  have htrace : WordTrace (prefixWord ++ tailWord_3863834) baseStart_3863834 baseEnd_3863834 := by
    simpa [prefixWord, tailWord_3863834, baseEnd_3863834] using wordTrace_append hprefix tailTrace_3863834
  have hstable : (prefixWord ++ tailWord_3863834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863834).length < 2 ^ (prefixWord ++ tailWord_3863834).sum := by decide
  have hdescent : baseEnd_3863834 < baseStart_3863834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863862 : List Nat := [5, 1, 2, 3, 2, 1, 2, 1, 1, 2, 3]
def baseStart_3863862 : Nat := 118140960795 + 3863862 * 2 ^ 59
def prefixEnd_3863862 : Nat := 4983230072969 + 3 ^ 40 * 3863862 * 2
def baseEnd_3863862 : Nat := 1984018388642666855855429

theorem tailTrace_3863862 : CollatzResearch.WordTrace tailWord_3863862 prefixEnd_3863862 1984018388642666855855429 := by
  unfold tailWord_3863862
  simp only [CollatzResearch.WordTrace]
  refine ⟨8807914045493458996111115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93951083151930229291851893 8807914045493458996111115)
  ·
    refine ⟨13211871068240188494166673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8807914045493458996111115 13211871068240188494166673)
    ·
      refine ⟨9908903301180141370625005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13211871068240188494166673 9908903301180141370625005)
      ·
        refine ⟨3715838737942553013984377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9908903301180141370625005 3715838737942553013984377)
        ·
          refine ⟨2786879053456914760488283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3715838737942553013984377 2786879053456914760488283)
          ·
            refine ⟨4180318580185372140732425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2786879053456914760488283 4180318580185372140732425)
            ·
              refine ⟨3135238935139029105549319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4180318580185372140732425 3135238935139029105549319)
              ·
                refine ⟨4702858402708543658323979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135238935139029105549319 4702858402708543658323979)
                ·
                  refine ⟨7054287604062815487485969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4702858402708543658323979 7054287604062815487485969)
                  ·
                    refine ⟨5290715703047111615614477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7054287604062815487485969 5290715703047111615614477)
                    ·
                      refine ⟨1984018388642666855855429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5290715703047111615614477 1984018388642666855855429)
                      ·
                        rfl

theorem cell23_3863862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_3863862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863862 prefixEnd_3863862 := by exact prefixLift 3863862
  have htrace : WordTrace (prefixWord ++ tailWord_3863862) baseStart_3863862 baseEnd_3863862 := by
    simpa [prefixWord, tailWord_3863862, baseEnd_3863862] using wordTrace_append hprefix tailTrace_3863862
  have hstable : (prefixWord ++ tailWord_3863862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863862).length < 2 ^ (prefixWord ++ tailWord_3863862).sum := by decide
  have hdescent : baseEnd_3863862 < baseStart_3863862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863864 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 4, 2, 2]
def baseStart_3863864 : Nat := 118140960795 + 3863864 * 2 ^ 59
def prefixEnd_3863864 : Nat := 4983230072969 + 3 ^ 40 * 3863864 * 2
def baseEnd_3863864 : Nat := 1984019415603975848030419

theorem tailTrace_3863864 : CollatzResearch.WordTrace tailWord_3863864 prefixEnd_3863864 1984019415603975848030419 := by
  unfold tailWord_3863864
  simp only [CollatzResearch.WordTrace]
  refine ⟨70463348836944049139675323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93951131782592065519567097 70463348836944049139675323)
  ·
    refine ⟨105695023255416073709512985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70463348836944049139675323 105695023255416073709512985)
    ·
      refine ⟨79271267441562055282134739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105695023255416073709512985 79271267441562055282134739)
      ·
        refine ⟨118906901162343082923202109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79271267441562055282134739 118906901162343082923202109)
        ·
          refine ⟨44590087935878656096200791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118906901162343082923202109 44590087935878656096200791)
          ·
            refine ⟨66885131903817984144301187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44590087935878656096200791 66885131903817984144301187)
            ·
              refine ⟨100327697855726976216451781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66885131903817984144301187 100327697855726976216451781)
              ·
                refine ⟨18811443347948808040584709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100327697855726976216451781 18811443347948808040584709)
                ·
                  refine ⟨3527145627740401507609633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18811443347948808040584709 3527145627740401507609633)
                  ·
                    refine ⟨2645359220805301130707225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3527145627740401507609633 2645359220805301130707225)
                    ·
                      refine ⟨1984019415603975848030419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2645359220805301130707225 1984019415603975848030419)
                      ·
                        rfl

theorem cell23_3863864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 4, 2, 2].length) (baseStart_3863864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863864 prefixEnd_3863864 := by exact prefixLift 3863864
  have htrace : WordTrace (prefixWord ++ tailWord_3863864) baseStart_3863864 baseEnd_3863864 := by
    simpa [prefixWord, tailWord_3863864, baseEnd_3863864] using wordTrace_append hprefix tailTrace_3863864
  have hstable : (prefixWord ++ tailWord_3863864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863864).length < 2 ^ (prefixWord ++ tailWord_3863864).sum := by decide
  have hdescent : baseEnd_3863864 < baseStart_3863864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863868 : List Nat := [2, 2, 2, 2, 1, 5, 2, 1, 1, 3, 2]
def baseStart_3863868 : Nat := 118140960795 + 3863868 * 2 ^ 59
def prefixEnd_3863868 : Nat := 4983230072969 + 3 ^ 40 * 3863868 * 2
def baseEnd_3863868 : Nat := 1984021469526593832380401

theorem tailTrace_3863868 : CollatzResearch.WordTrace tailWord_3863868 prefixEnd_3863868 1984021469526593832380401 := by
  unfold tailWord_3863868
  simp only [CollatzResearch.WordTrace]
  refine ⟨70463421782936803481248129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93951229043915737974997505 70463421782936803481248129)
  ·
    refine ⟨52847566337202602610936097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70463421782936803481248129 52847566337202602610936097)
    ·
      refine ⟨39635674752901951958202073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52847566337202602610936097 39635674752901951958202073)
      ·
        refine ⟨29726756064676463968651555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39635674752901951958202073 29726756064676463968651555)
        ·
          refine ⟨44590134097014695952977333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29726756064676463968651555 44590134097014695952977333)
          ·
            refine ⟨4180325071595127745591625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44590134097014695952977333 4180325071595127745591625)
            ·
              refine ⟨3135243803696345809193719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4180325071595127745591625 3135243803696345809193719)
              ·
                refine ⟨4702865705544518713790579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135243803696345809193719 4702865705544518713790579)
                ·
                  refine ⟨7054298558316778070685869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4702865705544518713790579 7054298558316778070685869)
                  ·
                    refine ⟨2645361959368791776507201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7054298558316778070685869 2645361959368791776507201)
                    ·
                      refine ⟨1984021469526593832380401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2645361959368791776507201 1984021469526593832380401)
                      ·
                        rfl

theorem cell23_3863868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_3863868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863868 prefixEnd_3863868 := by exact prefixLift 3863868
  have htrace : WordTrace (prefixWord ++ tailWord_3863868) baseStart_3863868 baseEnd_3863868 := by
    simpa [prefixWord, tailWord_3863868, baseEnd_3863868] using wordTrace_append hprefix tailTrace_3863868
  have hstable : (prefixWord ++ tailWord_3863868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863868).length < 2 ^ (prefixWord ++ tailWord_3863868).sum := by decide
  have hdescent : baseEnd_3863868 < baseStart_3863868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863881 : List Nat := [1, 2, 1, 1, 2, 3, 5, 2, 2, 2, 2]
def baseStart_3863881 : Nat := 118140960795 + 3863881 * 2 ^ 59
def prefixEnd_3863881 : Nat := 4983230072969 + 3 ^ 40 * 3863881 * 2
def baseEnd_3863881 : Nat := 1984028144775102281517841

theorem tailTrace_3863881 : CollatzResearch.WordTrace tailWord_3863881 prefixEnd_3863881 1984028144775102281517841 := by
  unfold tailWord_3863881
  simp only [CollatzResearch.WordTrace]
  refine ⟨140927317714826510182719497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93951545143217673455146331 140927317714826510182719497)
  ·
    refine ⟨105695488286119882637039623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140927317714826510182719497 105695488286119882637039623)
    ·
      refine ⟨158543232429179823955559435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105695488286119882637039623 158543232429179823955559435)
      ·
        refine ⟨237814848643769735933339153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158543232429179823955559435 237814848643769735933339153)
        ·
          refine ⟨178361136482827301950004365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237814848643769735933339153 178361136482827301950004365)
          ·
            refine ⟨66885426181060238231251637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178361136482827301950004365 66885426181060238231251637)
            ·
              refine ⟨6270508704474397334179841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66885426181060238231251637 6270508704474397334179841)
              ·
                refine ⟨4702881528355798000634881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6270508704474397334179841 4702881528355798000634881)
                ·
                  refine ⟨3527161146266848500476161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4702881528355798000634881 3527161146266848500476161)
                  ·
                    refine ⟨2645370859700136375357121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3527161146266848500476161 2645370859700136375357121)
                    ·
                      refine ⟨1984028144775102281517841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2645370859700136375357121 1984028144775102281517841)
                      ·
                        rfl

theorem cell23_3863881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 2, 2].length) (baseStart_3863881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863881 prefixEnd_3863881 := by exact prefixLift 3863881
  have htrace : WordTrace (prefixWord ++ tailWord_3863881) baseStart_3863881 baseEnd_3863881 := by
    simpa [prefixWord, tailWord_3863881, baseEnd_3863881] using wordTrace_append hprefix tailTrace_3863881
  have hstable : (prefixWord ++ tailWord_3863881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863881).length < 2 ^ (prefixWord ++ tailWord_3863881).sum := by decide
  have hdescent : baseEnd_3863881 < baseStart_3863881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863897 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 2, 3, 3]
def baseStart_3863897 : Nat := 118140960795 + 3863897 * 2 ^ 59
def prefixEnd_3863897 : Nat := 4983230072969 + 3 ^ 40 * 3863897 * 2
def baseEnd_3863897 : Nat := 1984036360465574218917767

theorem tailTrace_3863897 : CollatzResearch.WordTrace tailWord_3863897 prefixEnd_3863897 1984036360465574218917767 := by
  unfold tailWord_3863897
  simp only [CollatzResearch.WordTrace]
  refine ⟨140927901282768544915301945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93951934188512363276867963 140927901282768544915301945)
  ·
    refine ⟨105695925962076408686476459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140927901282768544915301945 105695925962076408686476459)
    ·
      refine ⟨158543888943114613029714689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105695925962076408686476459 158543888943114613029714689)
      ·
        refine ⟨118907916707335959772286017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158543888943114613029714689 118907916707335959772286017)
        ·
          refine ⟨89180937530501969829214513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118907916707335959772286017 89180937530501969829214513)
          ·
            refine ⟨66885703147876477371910885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89180937530501969829214513 66885703147876477371910885)
            ·
              refine ⟨12541069340226839507233291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66885703147876477371910885 12541069340226839507233291)
              ·
                refine ⟨18811604010340259260849937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12541069340226839507233291 18811604010340259260849937)
                ·
                  refine ⟨14108703007755194445637453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18811604010340259260849937 14108703007755194445637453)
                  ·
                    refine ⟨5290763627908197917114045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14108703007755194445637453 5290763627908197917114045)
                    ·
                      refine ⟨1984036360465574218917767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5290763627908197917114045 1984036360465574218917767)
                      ·
                        rfl

theorem cell23_3863897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 3, 3].length) (baseStart_3863897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863897 prefixEnd_3863897 := by exact prefixLift 3863897
  have htrace : WordTrace (prefixWord ++ tailWord_3863897) baseStart_3863897 baseEnd_3863897 := by
    simpa [prefixWord, tailWord_3863897, baseEnd_3863897] using wordTrace_append hprefix tailTrace_3863897
  have hstable : (prefixWord ++ tailWord_3863897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863897).length < 2 ^ (prefixWord ++ tailWord_3863897).sum := by decide
  have hdescent : baseEnd_3863897 < baseStart_3863897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863917 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 1, 7]
def baseStart_3863917 : Nat := 118140960795 + 3863917 * 2 ^ 59
def prefixEnd_3863917 : Nat := 4983230072969 + 3 ^ 40 * 3863917 * 2
def baseEnd_3863917 : Nat := 661348876692888046889225

theorem tailTrace_3863917 : CollatzResearch.WordTrace tailWord_3863917 prefixEnd_3863917 661348876692888046889225 := by
  unfold tailWord_3863917
  simp only [CollatzResearch.WordTrace]
  refine ⟨140928630742696088331030005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93952420495130725554020003 140928630742696088331030005)
  ·
    refine ⟨13212059132127758281034063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140928630742696088331030005 13212059132127758281034063)
    ·
      refine ⟨19818088698191637421551095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13212059132127758281034063 19818088698191637421551095)
      ·
        refine ⟨29727133047287456132326643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19818088698191637421551095 29727133047287456132326643)
        ·
          refine ⟨44590699570931184198489965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29727133047287456132326643 44590699570931184198489965)
          ·
            refine ⟨16721512339099194074433737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44590699570931184198489965 16721512339099194074433737)
            ·
              refine ⟨12541134254324395555825303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16721512339099194074433737 12541134254324395555825303)
              ·
                refine ⟨18811701381486593333737955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12541134254324395555825303 18811701381486593333737955)
                ·
                  refine ⟨28217552072229890000606933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18811701381486593333737955 28217552072229890000606933)
                  ·
                    refine ⟨661348876692888046889225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28217552072229890000606933 661348876692888046889225)
                    ·
                      rfl

theorem cell23_3863917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_3863917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863917 prefixEnd_3863917 := by exact prefixLift 3863917
  have htrace : WordTrace (prefixWord ++ tailWord_3863917) baseStart_3863917 baseEnd_3863917 := by
    simpa [prefixWord, tailWord_3863917, baseEnd_3863917] using wordTrace_append hprefix tailTrace_3863917
  have hstable : (prefixWord ++ tailWord_3863917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863917).length < 2 ^ (prefixWord ++ tailWord_3863917).sum := by decide
  have hdescent : baseEnd_3863917 < baseStart_3863917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863930 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 1, 10]
def baseStart_3863930 : Nat := 118140960795 + 3863930 * 2 ^ 59
def prefixEnd_3863930 : Nat := 4983230072969 + 3 ^ 40 * 3863930 * 2
def baseEnd_3863930 : Nat := 661351101775724196601705

theorem tailTrace_3863930 : CollatzResearch.WordTrace tailWord_3863930 prefixEnd_3863930 661351101775724196601705 := by
  unfold tailWord_3863930
  simp only [CollatzResearch.WordTrace]
  refine ⟨35232276222912247887813311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93952736594432661034168829 35232276222912247887813311)
  ·
    refine ⟨52848414334368371831719967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35232276222912247887813311 52848414334368371831719967)
    ·
      refine ⟨79272621501552557747579951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52848414334368371831719967 79272621501552557747579951)
      ·
        refine ⟨118908932252328836621369927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79272621501552557747579951 118908932252328836621369927)
        ·
          refine ⟨178363398378493254932054891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118908932252328836621369927 178363398378493254932054891)
          ·
            refine ⟨267545097567739882398082337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178363398378493254932054891 267545097567739882398082337)
            ·
              refine ⟨200658823175804911798561753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267545097567739882398082337 200658823175804911798561753)
              ·
                refine ⟨150494117381853683848921315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200658823175804911798561753 150494117381853683848921315)
                ·
                  refine ⟨225741176072780525773381973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150494117381853683848921315 225741176072780525773381973)
                  ·
                    refine ⟨661351101775724196601705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 225741176072780525773381973 661351101775724196601705)
                    ·
                      rfl

theorem cell23_3863930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_3863930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863930 prefixEnd_3863930 := by exact prefixLift 3863930
  have htrace : WordTrace (prefixWord ++ tailWord_3863930) baseStart_3863930 baseEnd_3863930 := by
    simpa [prefixWord, tailWord_3863930, baseEnd_3863930] using wordTrace_append hprefix tailTrace_3863930
  have hstable : (prefixWord ++ tailWord_3863930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863930).length < 2 ^ (prefixWord ++ tailWord_3863930).sum := by decide
  have hdescent : baseEnd_3863930 < baseStart_3863930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863957 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 3, 4, 3]
def baseStart_3863957 : Nat := 118140960795 + 3863957 * 2 ^ 59
def prefixEnd_3863957 : Nat := 4983230072969 + 3 ^ 40 * 3863957 * 2
def baseEnd_3863957 : Nat := 1984067169304843984167491

theorem tailTrace_3863957 : CollatzResearch.WordTrace tailWord_3863957 prefixEnd_3863957 1984067169304843984167491 := by
  unfold tailWord_3863957
  simp only [CollatzResearch.WordTrace]
  refine ⟨140930089662551175162486125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93953393108367450108324083 140930089662551175162486125)
  ·
    refine ⟨52848783623456690685932297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140930089662551175162486125 52848783623456690685932297)
    ·
      refine ⟨39636587717592518014449223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52848783623456690685932297 39636587717592518014449223)
      ·
        refine ⟨59454881576388777021673835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39636587717592518014449223 59454881576388777021673835)
        ·
          refine ⟨89182322364583165532510753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59454881576388777021673835 89182322364583165532510753)
          ·
            refine ⟨66886741773437374149383065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89182322364583165532510753 66886741773437374149383065)
            ·
              refine ⟨50165056330078030612037299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66886741773437374149383065 50165056330078030612037299)
              ·
                refine ⟨75247584495117045918055949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50165056330078030612037299 75247584495117045918055949)
                ·
                  refine ⟨28217844185668892219270981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75247584495117045918055949 28217844185668892219270981)
                  ·
                    refine ⟨5290845784812917291113309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28217844185668892219270981 5290845784812917291113309)
                    ·
                      refine ⟨1984067169304843984167491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5290845784812917291113309 1984067169304843984167491)
                      ·
                        rfl

theorem cell23_3863957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_3863957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863957 prefixEnd_3863957 := by exact prefixLift 3863957
  have htrace : WordTrace (prefixWord ++ tailWord_3863957) baseStart_3863957 baseEnd_3863957 := by
    simpa [prefixWord, tailWord_3863957, baseEnd_3863957] using wordTrace_append hprefix tailTrace_3863957
  have hstable : (prefixWord ++ tailWord_3863957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863957).length < 2 ^ (prefixWord ++ tailWord_3863957).sum := by decide
  have hdescent : baseEnd_3863957 < baseStart_3863957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3863997 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 1, 2, 6]
def baseStart_3863997 : Nat := 118140960795 + 3863997 * 2 ^ 59
def prefixEnd_3863997 : Nat := 4983230072969 + 3 ^ 40 * 3863997 * 2
def baseEnd_3863997 : Nat := 1984087708531023827667307

theorem tailTrace_3863997 : CollatzResearch.WordTrace tailWord_3863997 prefixEnd_3863997 1984087708531023827667307 := by
  unfold tailWord_3863997
  simp only [CollatzResearch.WordTrace]
  refine ⟨140931548582406261993942245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93954365721604174662628163 140931548582406261993942245)
  ·
    refine ⟨26424665359201174123864171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140931548582406261993942245 26424665359201174123864171)
    ·
      refine ⟨39636998038801761185796257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26424665359201174123864171 39636998038801761185796257)
      ·
        refine ⟨29727748529101320889347193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39636998038801761185796257 29727748529101320889347193)
        ·
          refine ⟨22295811396825990667010395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29727748529101320889347193 22295811396825990667010395)
          ·
            refine ⟨33443717095238986000515593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22295811396825990667010395 33443717095238986000515593)
            ·
              refine ⟨25082787821429239500386695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33443717095238986000515593 25082787821429239500386695)
              ·
                refine ⟨37624181732143859250580043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25082787821429239500386695 37624181732143859250580043)
                ·
                  refine ⟨56436272598215788875870065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37624181732143859250580043 56436272598215788875870065)
                  ·
                    refine ⟨42327204448661841656902549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56436272598215788875870065 42327204448661841656902549)
                    ·
                      refine ⟨1984087708531023827667307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42327204448661841656902549 1984087708531023827667307)
                      ·
                        rfl

theorem cell23_3863997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_3863997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3863997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3863997 prefixEnd_3863997 := by exact prefixLift 3863997
  have htrace : WordTrace (prefixWord ++ tailWord_3863997) baseStart_3863997 baseEnd_3863997 := by
    simpa [prefixWord, tailWord_3863997, baseEnd_3863997] using wordTrace_append hprefix tailTrace_3863997
  have hstable : (prefixWord ++ tailWord_3863997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3863997).length < 2 ^ (prefixWord ++ tailWord_3863997).sum := by decide
  have hdescent : baseEnd_3863997 < baseStart_3863997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3863997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864007 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 5, 5]
def baseStart_3864007 : Nat := 118140960795 + 3864007 * 2 ^ 59
def prefixEnd_3864007 : Nat := 4983230072969 + 3 ^ 40 * 3864007 * 2
def baseEnd_3864007 : Nat := 661364281112522929514087

theorem tailTrace_3864007 : CollatzResearch.WordTrace tailWord_3864007 prefixEnd_3864007 661364281112522929514087 := by
  unfold tailWord_3864007
  simp only [CollatzResearch.WordTrace]
  refine ⟨140931913312370033701806275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93954608874913355801204183 140931913312370033701806275)
  ·
    refine ⟨211397869968555050552709413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140931913312370033701806275 211397869968555050552709413)
    ·
      refine ⟨39637100619104071978633015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211397869968555050552709413 39637100619104071978633015)
      ·
        refine ⟨59455650928656107967949523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39637100619104071978633015 59455650928656107967949523)
        ·
          refine ⟨89183476392984161951924285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59455650928656107967949523 89183476392984161951924285)
          ·
            refine ⟨33443803647369060731971607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89183476392984161951924285 33443803647369060731971607)
            ·
              refine ⟨50165705471053591097957411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33443803647369060731971607 50165705471053591097957411)
              ·
                refine ⟨75248558206580386646936117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50165705471053591097957411 75248558206580386646936117)
                ·
                  refine ⟨7054552331866911248150261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75248558206580386646936117 7054552331866911248150261)
                  ·
                    refine ⟨661364281112522929514087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7054552331866911248150261 661364281112522929514087)
                    ·
                      rfl

theorem cell23_3864007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_3864007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864007 prefixEnd_3864007 := by exact prefixLift 3864007
  have htrace : WordTrace (prefixWord ++ tailWord_3864007) baseStart_3864007 baseEnd_3864007 := by
    simpa [prefixWord, tailWord_3864007, baseEnd_3864007] using wordTrace_append hprefix tailTrace_3864007
  have hstable : (prefixWord ++ tailWord_3864007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864007).length < 2 ^ (prefixWord ++ tailWord_3864007).sum := by decide
  have hdescent : baseEnd_3864007 < baseStart_3864007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864021 : List Nat := [1, 3, 2, 3, 1, 1, 3, 2, 3, 1, 3]
def baseStart_3864021 : Nat := 118140960795 + 3864021 * 2 ^ 59
def prefixEnd_3864021 : Nat := 4983230072969 + 3 ^ 40 * 3864021 * 2
def baseEnd_3864021 : Nat := 1984100032066731733767197

theorem tailTrace_3864021 : CollatzResearch.WordTrace tailWord_3864021 prefixEnd_3864021 1984100032066731733767197 := by
  unfold tailWord_3864021
  simp only [CollatzResearch.WordTrace]
  refine ⟨140932423934319314092815917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93954949289546209395210611 140932423934319314092815917)
  ·
    refine ⟨52849658975369742784805969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140932423934319314092815917 52849658975369742784805969)
    ·
      refine ⟨39637244231527307088604477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52849658975369742784805969 39637244231527307088604477)
      ·
        refine ⟨14863966586822740158226679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39637244231527307088604477 14863966586822740158226679)
        ·
          refine ⟨22295949880234110237340019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14863966586822740158226679 22295949880234110237340019)
          ·
            refine ⟨33443924820351165356010029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22295949880234110237340019 33443924820351165356010029)
            ·
              refine ⟨12541471807631687008503761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33443924820351165356010029 12541471807631687008503761)
              ·
                refine ⟨9406103855723765256377821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12541471807631687008503761 9406103855723765256377821)
                ·
                  refine ⟨3527288945896411971141683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9406103855723765256377821 3527288945896411971141683)
                  ·
                    refine ⟨5290933418844617956712525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3527288945896411971141683 5290933418844617956712525)
                    ·
                      refine ⟨1984100032066731733767197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5290933418844617956712525 1984100032066731733767197)
                      ·
                        rfl

theorem cell23_3864021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_3864021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864021 prefixEnd_3864021 := by exact prefixLift 3864021
  have htrace : WordTrace (prefixWord ++ tailWord_3864021) baseStart_3864021 baseEnd_3864021 := by
    simpa [prefixWord, tailWord_3864021, baseEnd_3864021] using wordTrace_append hprefix tailTrace_3864021
  have hstable : (prefixWord ++ tailWord_3864021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864021).length < 2 ^ (prefixWord ++ tailWord_3864021).sum := by decide
  have hdescent : baseEnd_3864021 < baseStart_3864021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864057 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 1, 1, 6]
def baseStart_3864057 : Nat := 118140960795 + 3864057 * 2 ^ 59
def prefixEnd_3864057 : Nat := 4983230072969 + 3 ^ 40 * 3864057 * 2
def baseEnd_3864057 : Nat := 1984118517370293592917031

theorem tailTrace_3864057 : CollatzResearch.WordTrace tailWord_3864057 prefixEnd_3864057 1984118517370293592917031 := by
  unfold tailWord_3864057
  simp only [CollatzResearch.WordTrace]
  refine ⟨140933736962188892241126425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93955824641459261494084283 140933736962188892241126425)
  ·
    refine ⟨105700302721641669180844819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140933736962188892241126425 105700302721641669180844819)
    ·
      refine ⟨158550454082462503771267229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105700302721641669180844819 158550454082462503771267229)
      ·
        refine ⟨59456420280923438914225211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158550454082462503771267229 59456420280923438914225211)
        ·
          refine ⟨89184630421385158371337817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59456420280923438914225211 89184630421385158371337817)
          ·
            refine ⟨66888472816038868778503363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89184630421385158371337817 66888472816038868778503363)
            ·
              refine ⟨100332709224058303167755045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66888472816038868778503363 100332709224058303167755045)
              ·
                refine ⟨18812382979510931843954071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100332709224058303167755045 18812382979510931843954071)
                ·
                  refine ⟨28218574469266397765931107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18812382979510931843954071 28218574469266397765931107)
                  ·
                    refine ⟨42327861703899596648896661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28218574469266397765931107 42327861703899596648896661)
                    ·
                      refine ⟨1984118517370293592917031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42327861703899596648896661 1984118517370293592917031)
                      ·
                        rfl

theorem cell23_3864057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_3864057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864057 prefixEnd_3864057 := by exact prefixLift 3864057
  have htrace : WordTrace (prefixWord ++ tailWord_3864057) baseStart_3864057 baseEnd_3864057 := by
    simpa [prefixWord, tailWord_3864057, baseEnd_3864057] using wordTrace_append hprefix tailTrace_3864057
  have hstable : (prefixWord ++ tailWord_3864057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864057).length < 2 ^ (prefixWord ++ tailWord_3864057).sum := by decide
  have hdescent : baseEnd_3864057 < baseStart_3864057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864071 : List Nat := [1, 1, 4, 3, 2, 3, 1, 1, 1, 6]
def baseStart_3864071 : Nat := 118140960795 + 3864071 * 2 ^ 59
def prefixEnd_3864071 : Nat := 4983230072969 + 3 ^ 40 * 3864071 * 2
def baseEnd_3864071 : Nat := 661375235366485512713989

theorem tailTrace_3864071 : CollatzResearch.WordTrace tailWord_3864071 prefixEnd_3864071 661375235366485512713989 := by
  unfold tailWord_3864071
  simp only [CollatzResearch.WordTrace]
  refine ⟨140934247584138172632136067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93956165056092115088090711 140934247584138172632136067)
  ·
    refine ⟨211401371376207258948204101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140934247584138172632136067 211401371376207258948204101)
    ·
      refine ⟨39637757133038861052788269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211401371376207258948204101 39637757133038861052788269)
      ·
        refine ⟨14864158924889572894795601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39637757133038861052788269 14864158924889572894795601)
        ·
          refine ⟨11148119193667179671096701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14864158924889572894795601 11148119193667179671096701)
          ·
            refine ⟨4180544697625192376661263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11148119193667179671096701 4180544697625192376661263)
            ·
              refine ⟨6270817046437788564991895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4180544697625192376661263 6270817046437788564991895)
              ·
                refine ⟨9406225569656682847487843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6270817046437788564991895 9406225569656682847487843)
                ·
                  refine ⟨14109338354485024271231765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9406225569656682847487843 14109338354485024271231765)
                  ·
                    refine ⟨661375235366485512713989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14109338354485024271231765 661375235366485512713989)
                    ·
                      rfl

theorem cell23_3864071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_3864071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864071 prefixEnd_3864071 := by exact prefixLift 3864071
  have htrace : WordTrace (prefixWord ++ tailWord_3864071) baseStart_3864071 baseEnd_3864071 := by
    simpa [prefixWord, tailWord_3864071, baseEnd_3864071] using wordTrace_append hprefix tailTrace_3864071
  have hstable : (prefixWord ++ tailWord_3864071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864071).length < 2 ^ (prefixWord ++ tailWord_3864071).sum := by decide
  have hdescent : baseEnd_3864071 < baseStart_3864071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864074 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 1, 1, 6]
def baseStart_3864074 : Nat := 118140960795 + 3864074 * 2 ^ 59
def prefixEnd_3864074 : Nat := 4983230072969 + 3 ^ 40 * 3864074 * 2
def baseEnd_3864074 : Nat := 1984127246541420026404453

theorem tailTrace_3864074 : CollatzResearch.WordTrace tailWord_3864074 prefixEnd_3864074 1984127246541420026404453 := by
  unfold tailWord_3864074
  simp only [CollatzResearch.WordTrace]
  refine ⟨35233589250781826036123819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93956238002084869429663517 35233589250781826036123819)
  ·
    refine ⟨52850383876172739054185729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35233589250781826036123819 52850383876172739054185729)
    ·
      refine ⟨39637787907129554290639297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52850383876172739054185729 39637787907129554290639297)
      ·
        refine ⟨29728340930347165717979473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39637787907129554290639297 29728340930347165717979473)
        ·
          refine ⟨22296255697760374288484605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29728340930347165717979473 22296255697760374288484605)
          ·
            refine ⟨8361095886660140358181727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22296255697760374288484605 8361095886660140358181727)
            ·
              refine ⟨12541643829990210537272591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8361095886660140358181727 12541643829990210537272591)
              ·
                refine ⟨18812465744985315805908887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12541643829990210537272591 18812465744985315805908887)
                ·
                  refine ⟨28218698617477973708863331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18812465744985315805908887 28218698617477973708863331)
                  ·
                    refine ⟨42328047926216960563294997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28218698617477973708863331 42328047926216960563294997)
                    ·
                      refine ⟨1984127246541420026404453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42328047926216960563294997 1984127246541420026404453)
                      ·
                        rfl

theorem cell23_3864074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_3864074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864074 prefixEnd_3864074 := by exact prefixLift 3864074
  have htrace : WordTrace (prefixWord ++ tailWord_3864074) baseStart_3864074 baseEnd_3864074 := by
    simpa [prefixWord, tailWord_3864074, baseEnd_3864074] using wordTrace_append hprefix tailTrace_3864074
  have hstable : (prefixWord ++ tailWord_3864074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864074).length < 2 ^ (prefixWord ++ tailWord_3864074).sum := by decide
  have hdescent : baseEnd_3864074 < baseStart_3864074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864078 : List Nat := [4, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4]
def baseStart_3864078 : Nat := 118140960795 + 3864078 * 2 ^ 59
def prefixEnd_3864078 : Nat := 4983230072969 + 3 ^ 40 * 3864078 * 2
def baseEnd_3864078 : Nat := 1984129300464038010754435

theorem tailTrace_3864078 : CollatzResearch.WordTrace tailWord_3864078 prefixEnd_3864078 1984129300464038010754435 := by
  unfold tailWord_3864078
  simp only [CollatzResearch.WordTrace]
  refine ⟨17616812861889101603455111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93956335263408541885093925 17616812861889101603455111)
  ·
    refine ⟨26425219292833652405182667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17616812861889101603455111 26425219292833652405182667)
    ·
      refine ⟨39637828939250478607774001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26425219292833652405182667 39637828939250478607774001)
      ·
        refine ⟨29728371704437858955830501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39637828939250478607774001 29728371704437858955830501)
        ·
          refine ⟨5574069694582098554218219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29728371704437858955830501 5574069694582098554218219)
          ·
            refine ⟨8361104541873147831327329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5574069694582098554218219 8361104541873147831327329)
            ·
              refine ⟨6270828406404860873495497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8361104541873147831327329 6270828406404860873495497)
              ·
                refine ⟨4703121304803645655121623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6270828406404860873495497 4703121304803645655121623)
                ·
                  refine ⟨7054681957205468482682435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4703121304803645655121623 7054681957205468482682435)
                  ·
                    refine ⟨10582022935808202724023653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7054681957205468482682435 10582022935808202724023653)
                    ·
                      refine ⟨1984129300464038010754435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10582022935808202724023653 1984129300464038010754435)
                      ·
                        rfl

theorem cell23_3864078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_3864078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864078 prefixEnd_3864078 := by exact prefixLift 3864078
  have htrace : WordTrace (prefixWord ++ tailWord_3864078) baseStart_3864078 baseEnd_3864078 := by
    simpa [prefixWord, tailWord_3864078, baseEnd_3864078] using wordTrace_append hprefix tailTrace_3864078
  have hstable : (prefixWord ++ tailWord_3864078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864078).length < 2 ^ (prefixWord ++ tailWord_3864078).sum := by decide
  have hdescent : baseEnd_3864078 < baseStart_3864078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864081 : List Nat := [1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 3]
def baseStart_3864081 : Nat := 118140960795 + 3864081 * 2 ^ 59
def prefixEnd_3864081 : Nat := 4983230072969 + 3 ^ 40 * 3864081 * 2
def baseEnd_3864081 : Nat := 1984130840906001499016921

theorem tailTrace_3864081 : CollatzResearch.WordTrace tailWord_3864081 prefixEnd_3864081 1984130840906001499016921 := by
  unfold tailWord_3864081
  simp only [CollatzResearch.WordTrace]
  refine ⟨140934612314101944340000097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93956408209401296226666731 140934612314101944340000097)
  ·
    refine ⟨105700959235576458255000073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140934612314101944340000097 105700959235576458255000073)
    ·
      refine ⟨79275719426682343691250055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105700959235576458255000073 79275719426682343691250055)
      ·
        refine ⟨118913579140023515536875083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79275719426682343691250055 118913579140023515536875083)
        ·
          refine ⟨178370368710035273305312625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118913579140023515536875083 178370368710035273305312625)
          ·
            refine ⟨133777776532526454978984469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178370368710035273305312625 133777776532526454978984469)
            ·
              refine ⟨6270833274962177577139897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133777776532526454978984469 6270833274962177577139897)
              ·
                refine ⟨4703124956221633182854923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6270833274962177577139897 4703124956221633182854923)
                ·
                  refine ⟨7054687434332449774282385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4703124956221633182854923 7054687434332449774282385)
                  ·
                    refine ⟨5291015575749337330711789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7054687434332449774282385 5291015575749337330711789)
                    ·
                      refine ⟨1984130840906001499016921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5291015575749337330711789 1984130840906001499016921)
                      ·
                        rfl

theorem cell23_3864081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 3].length) (baseStart_3864081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864081 prefixEnd_3864081 := by exact prefixLift 3864081
  have htrace : WordTrace (prefixWord ++ tailWord_3864081) baseStart_3864081 baseEnd_3864081 := by
    simpa [prefixWord, tailWord_3864081, baseEnd_3864081] using wordTrace_append hprefix tailTrace_3864081
  have hstable : (prefixWord ++ tailWord_3864081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864081).length < 2 ^ (prefixWord ++ tailWord_3864081).sum := by decide
  have hdescent : baseEnd_3864081 < baseStart_3864081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864095 : List Nat := [1, 1, 2, 4, 1, 1, 5, 3, 1, 2, 2]
def baseStart_3864095 : Nat := 118140960795 + 3864095 * 2 ^ 59
def prefixEnd_3864095 : Nat := 4983230072969 + 3 ^ 40 * 3864095 * 2
def baseEnd_3864095 : Nat := 1984138029635164444241857

theorem tailTrace_3864095 : CollatzResearch.WordTrace tailWord_3864095 prefixEnd_3864095 1984138029635164444241857 := by
  unfold tailWord_3864095
  simp only [CollatzResearch.WordTrace]
  refine ⟨140935122936051224731009739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93956748624034149820673159 140935122936051224731009739)
  ·
    refine ⟨211402684404076837096514609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140935122936051224731009739 211402684404076837096514609)
    ·
      refine ⟨158552013303057627822385957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211402684404076837096514609 158552013303057627822385957)
      ·
        refine ⟨29728502494323305216697367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158552013303057627822385957 29728502494323305216697367)
        ·
          refine ⟨44592753741484957825046051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29728502494323305216697367 44592753741484957825046051)
          ·
            refine ⟨66889130612227436737569077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44592753741484957825046051 66889130612227436737569077)
            ·
              refine ⟨6270855994896322194147101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66889130612227436737569077 6270855994896322194147101)
              ·
                refine ⟨2351570998086120822805163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6270855994896322194147101 2351570998086120822805163)
                ·
                  refine ⟨3527356497129181234207745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2351570998086120822805163 3527356497129181234207745)
                  ·
                    refine ⟨2645517372846885925655809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3527356497129181234207745 2645517372846885925655809)
                    ·
                      refine ⟨1984138029635164444241857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2645517372846885925655809 1984138029635164444241857)
                      ·
                        rfl

theorem cell23_3864095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_3864095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864095 prefixEnd_3864095 := by exact prefixLift 3864095
  have htrace : WordTrace (prefixWord ++ tailWord_3864095) baseStart_3864095 baseEnd_3864095 := by
    simpa [prefixWord, tailWord_3864095, baseEnd_3864095] using wordTrace_append hprefix tailTrace_3864095
  have hstable : (prefixWord ++ tailWord_3864095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864095).length < 2 ^ (prefixWord ++ tailWord_3864095).sum := by decide
  have hdescent : baseEnd_3864095 < baseStart_3864095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864151 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 3, 4, 2]
def baseStart_3864151 : Nat := 118140960795 + 3864151 * 2 ^ 59
def prefixEnd_3864151 : Nat := 4983230072969 + 3 ^ 40 * 3864151 * 2
def baseEnd_3864151 : Nat := 1984166784551816225141599

theorem tailTrace_3864151 : CollatzResearch.WordTrace tailWord_3864151 prefixEnd_3864151 1984166784551816225141599 := by
  unfold tailWord_3864151
  simp only [CollatzResearch.WordTrace]
  refine ⟨140937165423848346295048307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93958110282565564196698871 140937165423848346295048307)
  ·
    refine ⟨211405748135772519442572461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140937165423848346295048307 211405748135772519442572461)
    ·
      refine ⟨79277155550914694790964673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211405748135772519442572461 79277155550914694790964673)
      ·
        refine ⟨59457866663186021093223505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79277155550914694790964673 59457866663186021093223505)
        ·
          refine ⟨44593399997389515819917629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59457866663186021093223505 44593399997389515819917629)
          ·
            refine ⟨16722524999021068432469111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44593399997389515819917629 16722524999021068432469111)
            ·
              refine ⟨25083787498531602648703667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16722524999021068432469111 25083787498531602648703667)
              ·
                refine ⟨37625681247797403973055501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25083787498531602648703667 37625681247797403973055501)
                ·
                  refine ⟨14109630467924026489895813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37625681247797403973055501 14109630467924026489895813)
                  ·
                    refine ⟨2645555712735754966855465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14109630467924026489895813 2645555712735754966855465)
                    ·
                      refine ⟨1984166784551816225141599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2645555712735754966855465 1984166784551816225141599)
                      ·
                        rfl

theorem cell23_3864151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 4, 2].length) (baseStart_3864151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864151 prefixEnd_3864151 := by exact prefixLift 3864151
  have htrace : WordTrace (prefixWord ++ tailWord_3864151) baseStart_3864151 baseEnd_3864151 := by
    simpa [prefixWord, tailWord_3864151, baseEnd_3864151] using wordTrace_append hprefix tailTrace_3864151
  have hstable : (prefixWord ++ tailWord_3864151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864151).length < 2 ^ (prefixWord ++ tailWord_3864151).sum := by decide
  have hdescent : baseEnd_3864151 < baseStart_3864151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864154 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3]
def baseStart_3864154 : Nat := 118140960795 + 3864154 * 2 ^ 59
def prefixEnd_3864154 : Nat := 4983230072969 + 3 ^ 40 * 3864154 * 2
def baseEnd_3864154 : Nat := 1984168324993779713404085

theorem tailTrace_3864154 : CollatzResearch.WordTrace tailWord_3864154 prefixEnd_3864154 1984168324993779713404085 := by
  unfold tailWord_3864154
  simp only [CollatzResearch.WordTrace]
  refine ⟨35234318710709369451851879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93958183228558318538271677 35234318710709369451851879)
  ·
    refine ⟨52851478066064054177777819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35234318710709369451851879 52851478066064054177777819)
    ·
      refine ⟨79277217099096081266666729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52851478066064054177777819 79277217099096081266666729)
      ·
        refine ⟨59457912824322060950000047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79277217099096081266666729 59457912824322060950000047)
        ·
          refine ⟨89186869236483091425000071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59457912824322060950000047 89186869236483091425000071)
          ·
            refine ⟨133780303854724637137500107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89186869236483091425000071 133780303854724637137500107)
            ·
              refine ⟨200670455782086955706250161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133780303854724637137500107 200670455782086955706250161)
              ·
                refine ⟨150502841836565216779687621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200670455782086955706250161 150502841836565216779687621)
                ·
                  refine ⟨28219282844355978146191429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150502841836565216779687621 28219282844355978146191429)
                  ·
                    refine ⟨5291115533316745902410893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28219282844355978146191429 5291115533316745902410893)
                    ·
                      refine ⟨1984168324993779713404085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5291115533316745902410893 1984168324993779713404085)
                      ·
                        rfl

theorem cell23_3864154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_3864154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864154 prefixEnd_3864154 := by exact prefixLift 3864154
  have htrace : WordTrace (prefixWord ++ tailWord_3864154) baseStart_3864154 baseEnd_3864154 := by
    simpa [prefixWord, tailWord_3864154, baseEnd_3864154] using wordTrace_append hprefix tailTrace_3864154
  have hstable : (prefixWord ++ tailWord_3864154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864154).length < 2 ^ (prefixWord ++ tailWord_3864154).sum := by decide
  have hdescent : baseEnd_3864154 < baseStart_3864154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864181 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_3864181 : Nat := 118140960795 + 3864181 * 2 ^ 59
def prefixEnd_3864181 : Nat := 4983230072969 + 3 ^ 40 * 3864181 * 2
def baseEnd_3864181 : Nat := 1984182188971451107766461

theorem tailTrace_3864181 : CollatzResearch.WordTrace tailWord_3864181 prefixEnd_3864181 1984182188971451107766461 := by
  unfold tailWord_3864181
  simp only [CollatzResearch.WordTrace]
  refine ⟨140938259613739661418640397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93958839742493107612426931 140938259613739661418640397)
  ·
    refine ⟨52851847355152373031990149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140938259613739661418640397 52851847355152373031990149)
    ·
      refine ⟨9909721379091069943498153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52851847355152373031990149 9909721379091069943498153)
      ·
        refine ⟨7432291034318302457623615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9909721379091069943498153 7432291034318302457623615)
        ·
          refine ⟨11148436551477453686435423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7432291034318302457623615 11148436551477453686435423)
          ·
            refine ⟨16722654827216180529653135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11148436551477453686435423 16722654827216180529653135)
            ·
              refine ⟨25083982240824270794479703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16722654827216180529653135 25083982240824270794479703)
              ·
                refine ⟨37625973361236406191719555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25083982240824270794479703 37625973361236406191719555)
                ·
                  refine ⟨56438960041854609287579333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37625973361236406191719555 56438960041854609287579333)
                  ·
                    refine ⟨10582305007847739241421125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56438960041854609287579333 10582305007847739241421125)
                    ·
                      refine ⟨1984182188971451107766461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10582305007847739241421125 1984182188971451107766461)
                      ·
                        rfl

theorem cell23_3864181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_3864181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864181 prefixEnd_3864181 := by exact prefixLift 3864181
  have htrace : WordTrace (prefixWord ++ tailWord_3864181) baseStart_3864181 baseEnd_3864181 := by
    simpa [prefixWord, tailWord_3864181, baseEnd_3864181] using wordTrace_append hprefix tailTrace_3864181
  have hstable : (prefixWord ++ tailWord_3864181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864181).length < 2 ^ (prefixWord ++ tailWord_3864181).sum := by decide
  have hdescent : baseEnd_3864181 < baseStart_3864181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864204 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 1, 7]
def baseStart_3864204 : Nat := 118140960795 + 3864204 * 2 ^ 59
def prefixEnd_3864204 : Nat := 4983230072969 + 3 ^ 40 * 3864204 * 2
def baseEnd_3864204 : Nat := 661397999675501505926285

theorem tailTrace_3864204 : CollatzResearch.WordTrace tailWord_3864204 prefixEnd_3864204 661397999675501505926285 := by
  unfold tailWord_3864204
  simp only [CollatzResearch.WordTrace]
  refine ⟨70469549246328168173363833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93959398995104224231151777 70469549246328168173363833)
  ·
    refine ⟨52852161934746126130022875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70469549246328168173363833 52852161934746126130022875)
    ·
      refine ⟨79278242902119189195034313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52852161934746126130022875 79278242902119189195034313)
      ·
        refine ⟨59458682176589391896275735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79278242902119189195034313 59458682176589391896275735)
        ·
          refine ⟨89188023264884087844413603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59458682176589391896275735 89188023264884087844413603)
          ·
            refine ⟨133782034897326131766620405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89188023264884087844413603 133782034897326131766620405)
            ·
              refine ⟨12542065771624324853120663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133782034897326131766620405 12542065771624324853120663)
              ·
                refine ⟨18813098657436487279680995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12542065771624324853120663 18813098657436487279680995)
                ·
                  refine ⟨28219647986154730919521493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18813098657436487279680995 28219647986154730919521493)
                  ·
                    refine ⟨661397999675501505926285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28219647986154730919521493 661397999675501505926285)
                    ·
                      rfl

theorem cell23_3864204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_3864204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864204 prefixEnd_3864204 := by exact prefixLift 3864204
  have htrace : WordTrace (prefixWord ++ tailWord_3864204) baseStart_3864204 baseEnd_3864204 := by
    simpa [prefixWord, tailWord_3864204, baseEnd_3864204] using wordTrace_append hprefix tailTrace_3864204
  have hstable : (prefixWord ++ tailWord_3864204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864204).length < 2 ^ (prefixWord ++ tailWord_3864204).sum := by decide
  have hdescent : baseEnd_3864204 < baseStart_3864204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864264 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 10]
def baseStart_3864264 : Nat := 118140960795 + 3864264 * 2 ^ 59
def prefixEnd_3864264 : Nat := 4983230072969 + 3 ^ 40 * 3864264 * 2
def baseEnd_3864264 : Nat := 220469423096197142558731

theorem tailTrace_3864264 : CollatzResearch.WordTrace tailWord_3864264 prefixEnd_3864264 220469423096197142558731 := by
  unfold tailWord_3864264
  simp only [CollatzResearch.WordTrace]
  refine ⟨70470643436219483296955923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93960857914959311062607897 70470643436219483296955923)
  ·
    refine ⟨105705965154329224945433885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70470643436219483296955923 105705965154329224945433885)
    ·
      refine ⟨39639736932873459354537707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105705965154329224945433885 39639736932873459354537707)
      ·
        refine ⟨59459605399310189031806561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39639736932873459354537707 59459605399310189031806561)
        ·
          refine ⟨44594704049482641773854921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59459605399310189031806561 44594704049482641773854921)
          ·
            refine ⟨33446028037111981330391191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44594704049482641773854921 33446028037111981330391191)
            ·
              refine ⟨50169042055667971995586787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33446028037111981330391191 50169042055667971995586787)
              ·
                refine ⟨75253563083501957993380181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50169042055667971995586787 75253563083501957993380181)
                ·
                  refine ⟨220469423096197142558731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 75253563083501957993380181 220469423096197142558731)
                  ·
                    rfl

theorem cell23_3864264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 10].length) (baseStart_3864264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864264 prefixEnd_3864264 := by exact prefixLift 3864264
  have htrace : WordTrace (prefixWord ++ tailWord_3864264) baseStart_3864264 baseEnd_3864264 := by
    simpa [prefixWord, tailWord_3864264, baseEnd_3864264] using wordTrace_append hprefix tailTrace_3864264
  have hstable : (prefixWord ++ tailWord_3864264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864264).length < 2 ^ (prefixWord ++ tailWord_3864264).sum := by decide
  have hdescent : baseEnd_3864264 < baseStart_3864264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864298 : List Nat := [3, 1, 3, 1, 1, 1, 6, 1, 6]
def baseStart_3864298 : Nat := 118140960795 + 3864298 * 2 ^ 59
def prefixEnd_3864298 : Nat := 4983230072969 + 3 ^ 40 * 3864298 * 2
def baseEnd_3864298 : Nat := 220471362912003016667047

theorem tailTrace_3864298 : CollatzResearch.WordTrace tailWord_3864298 prefixEnd_3864298 220471362912003016667047 := by
  unfold tailWord_3864298
  simp only [CollatzResearch.WordTrace]
  refine ⟨35235631738578947600162387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93961684636210526933766365 35235631738578947600162387)
  ·
    refine ⟨52853447607868421400243581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35235631738578947600162387 52853447607868421400243581)
    ·
      refine ⟨19820042852950658025091343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52853447607868421400243581 19820042852950658025091343)
      ·
        refine ⟨29730064279425987037637015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19820042852950658025091343 29730064279425987037637015)
        ·
          refine ⟨44595096419138980556455523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29730064279425987037637015 44595096419138980556455523)
          ·
            refine ⟨66892644628708470834683285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44595096419138980556455523 66892644628708470834683285)
            ·
              refine ⟨3135592716970709570375779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66892644628708470834683285 3135592716970709570375779)
              ·
                refine ⟨4703389075456064355563669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135592716970709570375779 4703389075456064355563669)
                ·
                  refine ⟨220471362912003016667047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4703389075456064355563669 220471362912003016667047)
                  ·
                    rfl

theorem cell23_3864298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 6].length) (baseStart_3864298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864298 prefixEnd_3864298 := by exact prefixLift 3864298
  have htrace : WordTrace (prefixWord ++ tailWord_3864298) baseStart_3864298 baseEnd_3864298 := by
    simpa [prefixWord, tailWord_3864298, baseEnd_3864298] using wordTrace_append hprefix tailTrace_3864298
  have hstable : (prefixWord ++ tailWord_3864298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864298).length < 2 ^ (prefixWord ++ tailWord_3864298).sum := by decide
  have hdescent : baseEnd_3864298 < baseStart_3864298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864304 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 7]
def baseStart_3864304 : Nat := 118140960795 + 3864304 * 2 ^ 59
def prefixEnd_3864304 : Nat := 4983230072969 + 3 ^ 40 * 3864304 * 2
def baseEnd_3864304 : Nat := 1984245347091954126528395

theorem tailTrace_3864304 : CollatzResearch.WordTrace tailWord_3864304 prefixEnd_3864304 1984245347091954126528395 := by
  unfold tailWord_3864304
  simp only [CollatzResearch.WordTrace]
  refine ⟨70471372896147026712683983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93961830528196035616911977 70471372896147026712683983)
  ·
    refine ⟨105707059344220540069025975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70471372896147026712683983 105707059344220540069025975)
    ·
      refine ⟨158560589016330810103538963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105707059344220540069025975 158560589016330810103538963)
      ·
        refine ⟨237840883524496215155308445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158560589016330810103538963 237840883524496215155308445)
        ·
          refine ⟨89190331321686080683240667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237840883524496215155308445 89190331321686080683240667)
          ·
            refine ⟨133785496982529121024861001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89190331321686080683240667 133785496982529121024861001)
            ·
              refine ⟨100339122736896840768645751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133785496982529121024861001 100339122736896840768645751)
              ·
                refine ⟨150508684105345261152968627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100339122736896840768645751 150508684105345261152968627)
                ·
                  refine ⟨225763026158017891729452941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150508684105345261152968627 225763026158017891729452941)
                  ·
                    refine ⟨84661134809256709398544853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 225763026158017891729452941 84661134809256709398544853)
                    ·
                      refine ⟨1984245347091954126528395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84661134809256709398544853 1984245347091954126528395)
                      ·
                        rfl

theorem cell23_3864304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_3864304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864304 prefixEnd_3864304 := by exact prefixLift 3864304
  have htrace : WordTrace (prefixWord ++ tailWord_3864304) baseStart_3864304 baseEnd_3864304 := by
    simpa [prefixWord, tailWord_3864304, baseEnd_3864304] using wordTrace_append hprefix tailTrace_3864304
  have hstable : (prefixWord ++ tailWord_3864304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864304).length < 2 ^ (prefixWord ++ tailWord_3864304).sum := by decide
  have hdescent : baseEnd_3864304 < baseStart_3864304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864351 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 5]
def baseStart_3864351 : Nat := 118140960795 + 3864351 * 2 ^ 59
def prefixEnd_3864351 : Nat := 4983230072969 + 3 ^ 40 * 3864351 * 2
def baseEnd_3864351 : Nat := 1984269480682715442640679

theorem tailTrace_3864351 : CollatzResearch.WordTrace tailWord_3864351 prefixEnd_3864351 1984269480682715442640679 := by
  unfold tailWord_3864351
  simp only [CollatzResearch.WordTrace]
  refine ⟨140944460023123780452328907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93962973348749186968219271 140944460023123780452328907)
  ·
    refine ⟨211416690034685670678493361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140944460023123780452328907 211416690034685670678493361)
    ·
      refine ⟨158562517526014253008870021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211416690034685670678493361 158562517526014253008870021)
      ·
        refine ⟨29730472036127672439163129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158562517526014253008870021 29730472036127672439163129)
        ·
          refine ⟨22297854027095754329372347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29730472036127672439163129 22297854027095754329372347)
          ·
            refine ⟨33446781040643631494058521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22297854027095754329372347 33446781040643631494058521)
            ·
              refine ⟨25085085780482723620543891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33446781040643631494058521 25085085780482723620543891)
              ·
                refine ⟨37627628670724085430815837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25085085780482723620543891 37627628670724085430815837)
                ·
                  refine ⟨14110360751521532036555939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37627628670724085430815837 14110360751521532036555939)
                  ·
                    refine ⟨21165541127282298054833909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14110360751521532036555939 21165541127282298054833909)
                    ·
                      refine ⟨1984269480682715442640679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21165541127282298054833909 1984269480682715442640679)
                      ·
                        rfl

theorem cell23_3864351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_3864351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864351 prefixEnd_3864351 := by exact prefixLift 3864351
  have htrace : WordTrace (prefixWord ++ tailWord_3864351) baseStart_3864351 baseEnd_3864351 := by
    simpa [prefixWord, tailWord_3864351, baseEnd_3864351] using wordTrace_append hprefix tailTrace_3864351
  have hstable : (prefixWord ++ tailWord_3864351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864351).length < 2 ^ (prefixWord ++ tailWord_3864351).sum := by decide
  have hdescent : baseEnd_3864351 < baseStart_3864351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864378 : List Nat := [3, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4]
def baseStart_3864378 : Nat := 118140960795 + 3864378 * 2 ^ 59
def prefixEnd_3864378 : Nat := 4983230072969 + 3 ^ 40 * 3864378 * 2
def baseEnd_3864378 : Nat := 1984283344660386837003055

theorem tailTrace_3864378 : CollatzResearch.WordTrace tailWord_3864378 prefixEnd_3864378 1984283344660386837003055 := by
  unfold tailWord_3864378
  simp only [CollatzResearch.WordTrace]
  refine ⟨35236361198506491015890447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93963629862683976042374525 35236361198506491015890447)
  ·
    refine ⟨52854541797759736523835671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35236361198506491015890447 52854541797759736523835671)
    ·
      refine ⟨79281812696639604785753507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52854541797759736523835671 79281812696639604785753507)
      ·
        refine ⟨118922719044959407178630261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79281812696639604785753507 118922719044959407178630261)
        ·
          refine ⟨11149004910464944422996587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118922719044959407178630261 11149004910464944422996587)
          ·
            refine ⟨16723507365697416634494881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11149004910464944422996587 16723507365697416634494881)
            ·
              refine ⟨12542630524273062475871161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16723507365697416634494881 12542630524273062475871161)
              ·
                refine ⟨9406972893204796856903371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12542630524273062475871161 9406972893204796856903371)
                ·
                  refine ⟨14110459339807195285355057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9406972893204796856903371 14110459339807195285355057)
                  ·
                    refine ⟨10582844504855396464016293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14110459339807195285355057 10582844504855396464016293)
                    ·
                      refine ⟨1984283344660386837003055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10582844504855396464016293 1984283344660386837003055)
                      ·
                        rfl

theorem cell23_3864378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_3864378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864378 prefixEnd_3864378 := by exact prefixLift 3864378
  have htrace : WordTrace (prefixWord ++ tailWord_3864378) baseStart_3864378 baseEnd_3864378 := by
    simpa [prefixWord, tailWord_3864378, baseEnd_3864378] using wordTrace_append hprefix tailTrace_3864378
  have hstable : (prefixWord ++ tailWord_3864378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864378).length < 2 ^ (prefixWord ++ tailWord_3864378).sum := by decide
  have hdescent : baseEnd_3864378 < baseStart_3864378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864382 : List Nat := [4, 2, 1, 2, 2, 1, 4, 1, 1, 1, 4]
def baseStart_3864382 : Nat := 118140960795 + 3864382 * 2 ^ 59
def prefixEnd_3864382 : Nat := 4983230072969 + 3 ^ 40 * 3864382 * 2
def baseEnd_3864382 : Nat := 1984285398583004821353037

theorem tailTrace_3864382 : CollatzResearch.WordTrace tailWord_3864382 prefixEnd_3864382 1984285398583004821353037 := by
  unfold tailWord_3864382
  simp only [CollatzResearch.WordTrace]
  refine ⟨17618198835751434093338425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93963727124007648497804933 17618198835751434093338425)
  ·
    refine ⟨13213649126813575570003819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17618198835751434093338425 13213649126813575570003819)
    ·
      refine ⟨19820473690220363355005729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13213649126813575570003819 19820473690220363355005729)
      ·
        refine ⟨14865355267665272516254297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19820473690220363355005729 14865355267665272516254297)
        ·
          refine ⟨11149016450748954387190723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14865355267665272516254297 11149016450748954387190723)
          ·
            refine ⟨16723524676123431580786085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11149016450748954387190723 16723524676123431580786085)
            ·
              refine ⟨3135660876773143421397391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16723524676123431580786085 3135660876773143421397391)
              ·
                refine ⟨4703491315159715132096087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135660876773143421397391 4703491315159715132096087)
                ·
                  refine ⟨7055236972739572698144131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4703491315159715132096087 7055236972739572698144131)
                  ·
                    refine ⟨10582855459109359047216197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7055236972739572698144131 10582855459109359047216197)
                    ·
                      refine ⟨1984285398583004821353037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10582855459109359047216197 1984285398583004821353037)
                      ·
                        rfl

theorem cell23_3864382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_3864382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864382 prefixEnd_3864382 := by exact prefixLift 3864382
  have htrace : WordTrace (prefixWord ++ tailWord_3864382) baseStart_3864382 baseEnd_3864382 := by
    simpa [prefixWord, tailWord_3864382, baseEnd_3864382] using wordTrace_append hprefix tailTrace_3864382
  have hstable : (prefixWord ++ tailWord_3864382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864382).length < 2 ^ (prefixWord ++ tailWord_3864382).sum := by decide
  have hdescent : baseEnd_3864382 < baseStart_3864382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864412 : List Nat := [2, 2, 4, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_3864412 : Nat := 118140960795 + 3864412 * 2 ^ 59
def prefixEnd_3864412 : Nat := 4983230072969 + 3 ^ 40 * 3864412 * 2
def baseEnd_3864412 : Nat := 1984300803002639703977899

theorem tailTrace_3864412 : CollatzResearch.WordTrace tailWord_3864412 prefixEnd_3864412 1984300803002639703977899 := by
  unfold tailWord_3864412
  simp only [CollatzResearch.WordTrace]
  refine ⟨70473342437951393935149745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93964456583935191913532993 70473342437951393935149745)
  ·
    refine ⟨52855006828463545451362309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70473342437951393935149745 52855006828463545451362309)
    ·
      refine ⟨9910313780336914772130433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52855006828463545451362309 9910313780336914772130433)
      ·
        refine ⟨7432735335252686079097825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9910313780336914772130433 7432735335252686079097825)
        ·
          refine ⟨5574551501439514559323369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7432735335252686079097825 5574551501439514559323369)
          ·
            refine ⟨4180913626079635919492527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5574551501439514559323369 4180913626079635919492527)
            ·
              refine ⟨6271370439119453879238791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4180913626079635919492527 6271370439119453879238791)
              ·
                refine ⟨9407055658679180818858187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6271370439119453879238791 9407055658679180818858187)
                ·
                  refine ⟨14110583488018771228287281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9407055658679180818858187 14110583488018771228287281)
                  ·
                    refine ⟨10582937616014078421215461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14110583488018771228287281 10582937616014078421215461)
                    ·
                      refine ⟨1984300803002639703977899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10582937616014078421215461 1984300803002639703977899)
                      ·
                        rfl

theorem cell23_3864412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_3864412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864412 prefixEnd_3864412 := by exact prefixLift 3864412
  have htrace : WordTrace (prefixWord ++ tailWord_3864412) baseStart_3864412 baseEnd_3864412 := by
    simpa [prefixWord, tailWord_3864412, baseEnd_3864412] using wordTrace_append hprefix tailTrace_3864412
  have hstable : (prefixWord ++ tailWord_3864412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864412).length < 2 ^ (prefixWord ++ tailWord_3864412).sum := by decide
  have hdescent : baseEnd_3864412 < baseStart_3864412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864415 : List Nat := [1, 1, 2, 3, 1, 6, 1, 1, 1, 3, 3]
def baseStart_3864415 : Nat := 118140960795 + 3864415 * 2 ^ 59
def prefixEnd_3864415 : Nat := 4983230072969 + 3 ^ 40 * 3864415 * 2
def baseEnd_3864415 : Nat := 1984302343444603192240385

theorem tailTrace_3864415 : CollatzResearch.WordTrace tailWord_3864415 prefixEnd_3864415 1984302343444603192240385 := by
  unfold tailWord_3864415
  simp only [CollatzResearch.WordTrace]
  refine ⟨140946794294891919382658699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93964529529927946255105799 140946794294891919382658699)
  ·
    refine ⟨211420191442337879073988049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140946794294891919382658699 211420191442337879073988049)
    ·
      refine ⟨158565143581753409305491037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211420191442337879073988049 158565143581753409305491037)
      ·
        refine ⟨59461928843157528489559139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158565143581753409305491037 59461928843157528489559139)
        ·
          refine ⟨89192893264736292734338709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59461928843157528489559139 89192893264736292734338709)
          ·
            refine ⟨4180916871784513721922127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89192893264736292734338709 4180916871784513721922127)
            ·
              refine ⟨6271375307676770582883191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4180916871784513721922127 6271375307676770582883191)
              ·
                refine ⟨9407062961515155874324787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6271375307676770582883191 9407062961515155874324787)
                ·
                  refine ⟨14110594442272733811487181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9407062961515155874324787 14110594442272733811487181)
                  ·
                    refine ⟨5291472915852275179307693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14110594442272733811487181 5291472915852275179307693)
                    ·
                      refine ⟨1984302343444603192240385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5291472915852275179307693 1984302343444603192240385)
                      ·
                        rfl

theorem cell23_3864415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_3864415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864415 prefixEnd_3864415 := by exact prefixLift 3864415
  have htrace : WordTrace (prefixWord ++ tailWord_3864415) baseStart_3864415 baseEnd_3864415 := by
    simpa [prefixWord, tailWord_3864415, baseEnd_3864415] using wordTrace_append hprefix tailTrace_3864415
  have hstable : (prefixWord ++ tailWord_3864415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864415).length < 2 ^ (prefixWord ++ tailWord_3864415).sum := by decide
  have hdescent : baseEnd_3864415 < baseStart_3864415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864466 : List Nat := [3, 2, 3, 2, 1, 3, 2, 1, 2, 1, 3]
def baseStart_3864466 : Nat := 118140960795 + 3864466 * 2 ^ 59
def prefixEnd_3864466 : Nat := 4983230072969 + 3 ^ 40 * 3864466 * 2
def baseEnd_3864466 : Nat := 1984328530957982492702651

theorem tailTrace_3864466 : CollatzResearch.WordTrace tailWord_3864466 prefixEnd_3864466 1984328530957982492702651 := by
  unfold tailWord_3864466
  simp only [CollatzResearch.WordTrace]
  refine ⟨35237163604426788773191313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93965769611804770061843501 35237163604426788773191313)
  ·
    refine ⟨26427872703320091579893485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35237163604426788773191313 26427872703320091579893485)
    ·
      refine ⟨9910452263745034342460057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26427872703320091579893485 9910452263745034342460057)
      ·
        refine ⟨7432839197808775756845043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9910452263745034342460057 7432839197808775756845043)
        ·
          refine ⟨11149258796713163635267565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7432839197808775756845043 11149258796713163635267565)
          ·
            refine ⟨4180972048767436363225337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11149258796713163635267565 4180972048767436363225337)
            ·
              refine ⟨3135729036575577272419003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4180972048767436363225337 3135729036575577272419003)
              ·
                refine ⟨4703593554863365908628505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135729036575577272419003 4703593554863365908628505)
                ·
                  refine ⟨3527695166147524431471379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4703593554863365908628505 3527695166147524431471379)
                  ·
                    refine ⟨5291542749221286647207069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3527695166147524431471379 5291542749221286647207069)
                    ·
                      refine ⟨1984328530957982492702651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5291542749221286647207069 1984328530957982492702651)
                      ·
                        rfl

theorem cell23_3864466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_3864466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864466 prefixEnd_3864466 := by exact prefixLift 3864466
  have htrace : WordTrace (prefixWord ++ tailWord_3864466) baseStart_3864466 baseEnd_3864466 := by
    simpa [prefixWord, tailWord_3864466, baseEnd_3864466] using wordTrace_append hprefix tailTrace_3864466
  have hstable : (prefixWord ++ tailWord_3864466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864466).length < 2 ^ (prefixWord ++ tailWord_3864466).sum := by decide
  have hdescent : baseEnd_3864466 < baseStart_3864466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864528 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 4]
def baseStart_3864528 : Nat := 118140960795 + 3864528 * 2 ^ 59
def prefixEnd_3864528 : Nat := 4983230072969 + 3 ^ 40 * 3864528 * 2
def baseEnd_3864528 : Nat := 1984360366758561250127365

theorem tailTrace_3864528 : CollatzResearch.WordTrace tailWord_3864528 prefixEnd_3864528 1984360366758561250127365 := by
  unfold tailWord_3864528
  simp only [CollatzResearch.WordTrace]
  refine ⟨70475457871741269840761119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93967277162321693121014825 70475457871741269840761119)
  ·
    refine ⟨105713186807611904761141679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70475457871741269840761119 105713186807611904761141679)
    ·
      refine ⟨158569780211417857141712519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105713186807611904761141679 158569780211417857141712519)
      ·
        refine ⟨237854670317126785712568779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158569780211417857141712519 237854670317126785712568779)
        ·
          refine ⟨356782005475690178568853169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237854670317126785712568779 356782005475690178568853169)
          ·
            refine ⟨267586504106767633926639877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356782005475690178568853169 267586504106767633926639877)
            ·
              refine ⟨50172469520018931361244977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 267586504106767633926639877 50172469520018931361244977)
              ·
                refine ⟨37629352140014198520933733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50172469520018931361244977 37629352140014198520933733)
                ·
                  refine ⟨7055503526252662222675075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37629352140014198520933733 7055503526252662222675075)
                  ·
                    refine ⟨10583255289378993334012613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7055503526252662222675075 10583255289378993334012613)
                    ·
                      refine ⟨1984360366758561250127365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10583255289378993334012613 1984360366758561250127365)
                      ·
                        rfl

theorem cell23_3864528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 4].length) (baseStart_3864528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864528 prefixEnd_3864528 := by exact prefixLift 3864528
  have htrace : WordTrace (prefixWord ++ tailWord_3864528) baseStart_3864528 baseEnd_3864528 := by
    simpa [prefixWord, tailWord_3864528, baseEnd_3864528] using wordTrace_append hprefix tailTrace_3864528
  have hstable : (prefixWord ++ tailWord_3864528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864528).length < 2 ^ (prefixWord ++ tailWord_3864528).sum := by decide
  have hdescent : baseEnd_3864528 < baseStart_3864528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864545 : List Nat := [1, 2, 3, 1, 2, 1, 5, 1, 2, 1, 4]
def baseStart_3864545 : Nat := 118140960795 + 3864545 * 2 ^ 59
def prefixEnd_3864545 : Nat := 4983230072969 + 3 ^ 40 * 3864545 * 2
def baseEnd_3864545 : Nat := 1984369095929687683614787

theorem tailTrace_3864545 : CollatzResearch.WordTrace tailWord_3864545 prefixEnd_3864545 1984369095929687683614787 := by
  unfold tailWord_3864545
  simp only [CollatzResearch.WordTrace]
  refine ⟨140951535784420951584891089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93967690522947301056594059 140951535784420951584891089)
  ·
    refine ⟨105713651838315713688668317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140951535784420951584891089 105713651838315713688668317)
    ·
      refine ⟨39642619439368392633250619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105713651838315713688668317 39642619439368392633250619)
      ·
        refine ⟨59463929159052588949875929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39642619439368392633250619 59463929159052588949875929)
        ·
          refine ⟨44597946869289441712406947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59463929159052588949875929 44597946869289441712406947)
          ·
            refine ⟨66896920303934162568610421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44597946869289441712406947 66896920303934162568610421)
            ·
              refine ⟨6271586278493827740807227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66896920303934162568610421 6271586278493827740807227)
              ·
                refine ⟨9407379417740741611210841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6271586278493827740807227 9407379417740741611210841)
                ·
                  refine ⟨7055534563305556208408131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9407379417740741611210841 7055534563305556208408131)
                  ·
                    refine ⟨10583301844958334312612197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7055534563305556208408131 10583301844958334312612197)
                    ·
                      refine ⟨1984369095929687683614787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10583301844958334312612197 1984369095929687683614787)
                      ·
                        rfl

theorem cell23_3864545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_3864545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864545 prefixEnd_3864545 := by exact prefixLift 3864545
  have htrace : WordTrace (prefixWord ++ tailWord_3864545) baseStart_3864545 baseEnd_3864545 := by
    simpa [prefixWord, tailWord_3864545, baseEnd_3864545] using wordTrace_append hprefix tailTrace_3864545
  have hstable : (prefixWord ++ tailWord_3864545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864545).length < 2 ^ (prefixWord ++ tailWord_3864545).sum := by decide
  have hdescent : baseEnd_3864545 < baseStart_3864545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864572 : List Nat := [2, 2, 2, 1, 2, 2, 1, 6, 1, 4]
def baseStart_3864572 : Nat := 118140960795 + 3864572 * 2 ^ 59
def prefixEnd_3864572 : Nat := 4983230072969 + 3 ^ 40 * 3864572 * 2
def baseEnd_3864572 : Nat := 661460986635786359325721

theorem tailTrace_3864572 : CollatzResearch.WordTrace tailWord_3864572 prefixEnd_3864572 661460986635786359325721 := by
  unfold tailWord_3864572
  simp only [CollatzResearch.WordTrace]
  refine ⟨70476260277661567598061985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93968347036882090130749313 70476260277661567598061985)
  ·
    refine ⟨52857195208246175698546489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70476260277661567598061985 52857195208246175698546489)
    ·
      refine ⟨39642896406184631773909867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52857195208246175698546489 39642896406184631773909867)
      ·
        refine ⟨59464344609276947660864801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39642896406184631773909867 59464344609276947660864801)
        ·
          refine ⟨44598258456957710745648601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59464344609276947660864801 44598258456957710745648601)
          ·
            refine ⟨33448693842718283059236451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44598258456957710745648601 33448693842718283059236451)
            ·
              refine ⟨50173040764077424588854677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33448693842718283059236451 50173040764077424588854677)
              ·
                refine ⟨2351861285816129277602563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50173040764077424588854677 2351861285816129277602563)
                ·
                  refine ⟨3527791928724193916403845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2351861285816129277602563 3527791928724193916403845)
                  ·
                    refine ⟨661460986635786359325721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3527791928724193916403845 661460986635786359325721)
                    ·
                      rfl

theorem cell23_3864572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_3864572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864572 prefixEnd_3864572 := by exact prefixLift 3864572
  have htrace : WordTrace (prefixWord ++ tailWord_3864572) baseStart_3864572 baseEnd_3864572 := by
    simpa [prefixWord, tailWord_3864572, baseEnd_3864572] using wordTrace_append hprefix tailTrace_3864572
  have hstable : (prefixWord ++ tailWord_3864572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864572).length < 2 ^ (prefixWord ++ tailWord_3864572).sum := by decide
  have hdescent : baseEnd_3864572 < baseStart_3864572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864588 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 1, 2, 6]
def baseStart_3864588 : Nat := 118140960795 + 3864588 * 2 ^ 59
def prefixEnd_3864588 : Nat := 4983230072969 + 3 ^ 40 * 3864588 * 2
def baseEnd_3864588 : Nat := 1984391175597831015377089

theorem tailTrace_3864588 : CollatzResearch.WordTrace tailWord_3864588 prefixEnd_3864588 1984391175597831015377089 := by
  unfold tailWord_3864588
  simp only [CollatzResearch.WordTrace]
  refine ⟨70476552061632584964353209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93968736082176779952470945 70476552061632584964353209)
  ·
    refine ⟨52857414046224438723264907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70476552061632584964353209 52857414046224438723264907)
    ·
      refine ⟨79286121069336658084897361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52857414046224438723264907 79286121069336658084897361)
      ·
        refine ⟨59464590802002493563673021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79286121069336658084897361 59464590802002493563673021)
        ·
          refine ⟨22299221550750935086377383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59464590802002493563673021 22299221550750935086377383)
          ·
            refine ⟨33448832326126402629566075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22299221550750935086377383 33448832326126402629566075)
            ·
              refine ⟨50173248489189603944349113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33448832326126402629566075 50173248489189603944349113)
              ·
                refine ⟨37629936366892202958261835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50173248489189603944349113 37629936366892202958261835)
                ·
                  refine ⟨56444904550338304437392753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37629936366892202958261835 56444904550338304437392753)
                  ·
                    refine ⟨42333678412753728328044565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56444904550338304437392753 42333678412753728328044565)
                    ·
                      refine ⟨1984391175597831015377089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42333678412753728328044565 1984391175597831015377089)
                      ·
                        rfl

theorem cell23_3864588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_3864588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864588 prefixEnd_3864588 := by exact prefixLift 3864588
  have htrace : WordTrace (prefixWord ++ tailWord_3864588) baseStart_3864588 baseEnd_3864588 := by
    simpa [prefixWord, tailWord_3864588, baseEnd_3864588] using wordTrace_append hprefix tailTrace_3864588
  have hstable : (prefixWord ++ tailWord_3864588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864588).length < 2 ^ (prefixWord ++ tailWord_3864588).sum := by decide
  have hdescent : baseEnd_3864588 < baseStart_3864588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864629 : List Nat := [1, 3, 3, 1, 1, 1, 2, 6, 1, 1, 3]
def baseStart_3864629 : Nat := 118140960795 + 3864629 * 2 ^ 59
def prefixEnd_3864629 : Nat := 4983230072969 + 3 ^ 40 * 3864629 * 2
def baseEnd_3864629 : Nat := 1984412228304665354964401

theorem tailTrace_3864629 : CollatzResearch.WordTrace tailWord_3864629 prefixEnd_3864629 1984412228304665354964401 := by
  unfold tailWord_3864629
  simp only [CollatzResearch.WordTrace]
  refine ⟨140954599516116633930948941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93969733010744422620632627 140954599516116633930948941)
  ·
    refine ⟨52857974818543737724105853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140954599516116633930948941 52857974818543737724105853)
    ·
      refine ⟨19821740556953901646539695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52857974818543737724105853 19821740556953901646539695)
      ·
        refine ⟨29732610835430852469809543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19821740556953901646539695 29732610835430852469809543)
        ·
          refine ⟨44598916253146278704714315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29732610835430852469809543 44598916253146278704714315)
          ·
            refine ⟨66898374379719418057071473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44598916253146278704714315 66898374379719418057071473)
            ·
              refine ⟨50173780784789563542803605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66898374379719418057071473 50173780784789563542803605)
              ·
                refine ⟨2351895974287010791068919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50173780784789563542803605 2351895974287010791068919)
                ·
                  refine ⟨3527843961430516186603379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2351895974287010791068919 3527843961430516186603379)
                  ·
                    refine ⟨5291765942145774279905069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3527843961430516186603379 5291765942145774279905069)
                    ·
                      refine ⟨1984412228304665354964401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5291765942145774279905069 1984412228304665354964401)
                      ·
                        rfl

theorem cell23_3864629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_3864629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864629 prefixEnd_3864629 := by exact prefixLift 3864629
  have htrace : WordTrace (prefixWord ++ tailWord_3864629) baseStart_3864629 baseEnd_3864629 := by
    simpa [prefixWord, tailWord_3864629, baseEnd_3864629] using wordTrace_append hprefix tailTrace_3864629
  have hstable : (prefixWord ++ tailWord_3864629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864629).length < 2 ^ (prefixWord ++ tailWord_3864629).sum := by decide
  have hdescent : baseEnd_3864629 < baseStart_3864629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864652 : List Nat := [2, 2, 1, 3, 1, 1, 5, 2, 1, 1, 4]
def baseStart_3864652 : Nat := 118140960795 + 3864652 * 2 ^ 59
def prefixEnd_3864652 : Nat := 4983230072969 + 3 ^ 40 * 3864652 * 2
def baseEnd_3864652 : Nat := 1984424038359718764976795

theorem tailTrace_3864652 : CollatzResearch.WordTrace tailWord_3864652 prefixEnd_3864652 1984424038359718764976795 := by
  unfold tailWord_3864652
  simp only [CollatzResearch.WordTrace]
  refine ⟨70477719197516654429518105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93970292263355539239357473 70477719197516654429518105)
  ·
    refine ⟨52858289398137490822138579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70477719197516654429518105 52858289398137490822138579)
    ·
      refine ⟨79287434097206236233207869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52858289398137490822138579 79287434097206236233207869)
      ·
        refine ⟨29732787786452338587452951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79287434097206236233207869 29732787786452338587452951)
        ·
          refine ⟨44599181679678507881179427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29732787786452338587452951 44599181679678507881179427)
          ·
            refine ⟨66898772519517761821769141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44599181679678507881179427 66898772519517761821769141)
            ·
              refine ⟨6271759923704790170790857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66898772519517761821769141 6271759923704790170790857)
              ·
                refine ⟨4703819942778592628093143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6271759923704790170790857 4703819942778592628093143)
                ·
                  refine ⟨7055729914167888942139715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4703819942778592628093143 7055729914167888942139715)
                  ·
                    refine ⟨10583594871251833413209573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7055729914167888942139715 10583594871251833413209573)
                    ·
                      refine ⟨1984424038359718764976795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10583594871251833413209573 1984424038359718764976795)
                      ·
                        rfl

theorem cell23_3864652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_3864652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864652 prefixEnd_3864652 := by exact prefixLift 3864652
  have htrace : WordTrace (prefixWord ++ tailWord_3864652) baseStart_3864652 baseEnd_3864652 := by
    simpa [prefixWord, tailWord_3864652, baseEnd_3864652] using wordTrace_append hprefix tailTrace_3864652
  have hstable : (prefixWord ++ tailWord_3864652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864652).length < 2 ^ (prefixWord ++ tailWord_3864652).sum := by decide
  have hdescent : baseEnd_3864652 < baseStart_3864652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864655 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 3]
def baseStart_3864655 : Nat := 118140960795 + 3864655 * 2 ^ 59
def prefixEnd_3864655 : Nat := 4983230072969 + 3 ^ 40 * 3864655 * 2
def baseEnd_3864655 : Nat := 1984425578801682253239281

theorem tailTrace_3864655 : CollatzResearch.WordTrace tailWord_3864655 prefixEnd_3864655 1984425578801682253239281 := by
  unfold tailWord_3864655
  simp only [CollatzResearch.WordTrace]
  refine ⟨140955547814022440371395419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93970365209348293580930279 140955547814022440371395419)
  ·
    refine ⟨211433321721033660557093129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140955547814022440371395419 211433321721033660557093129)
    ·
      refine ⟨158574991290775245417819847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211433321721033660557093129 158574991290775245417819847)
      ·
        refine ⟨237862486936162868126729771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158574991290775245417819847 237862486936162868126729771)
        ·
          refine ⟨356793730404244302190094657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237862486936162868126729771 356793730404244302190094657)
          ·
            refine ⟨267595297803183226642570993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356793730404244302190094657 267595297803183226642570993)
            ·
              refine ⟨200696473352387419981928245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267595297803183226642570993 200696473352387419981928245)
              ·
                refine ⟨18815294376786320623305773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 200696473352387419981928245 18815294376786320623305773)
                ·
                  refine ⟨7055735391294870233739665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18815294376786320623305773 7055735391294870233739665)
                  ·
                    refine ⟨5291801543471152675304749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7055735391294870233739665 5291801543471152675304749)
                    ·
                      refine ⟨1984425578801682253239281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5291801543471152675304749 1984425578801682253239281)
                      ·
                        rfl

theorem cell23_3864655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 3].length) (baseStart_3864655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864655 prefixEnd_3864655 := by exact prefixLift 3864655
  have htrace : WordTrace (prefixWord ++ tailWord_3864655) baseStart_3864655 baseEnd_3864655 := by
    simpa [prefixWord, tailWord_3864655, baseEnd_3864655] using wordTrace_append hprefix tailTrace_3864655
  have hstable : (prefixWord ++ tailWord_3864655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864655).length < 2 ^ (prefixWord ++ tailWord_3864655).sum := by decide
  have hdescent : baseEnd_3864655 < baseStart_3864655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864665 : List Nat := [1, 2, 1, 2, 2, 1, 5, 2, 1, 2, 4]
def baseStart_3864665 : Nat := 118140960795 + 3864665 * 2 ^ 59
def prefixEnd_3864665 : Nat := 4983230072969 + 3 ^ 40 * 3864665 * 2
def baseEnd_3864665 : Nat := 1984430713608227214114235

theorem tailTrace_3864665 : CollatzResearch.WordTrace tailWord_3864665 prefixEnd_3864665 1984430713608227214114235 := by
  unfold tailWord_3864665
  simp only [CollatzResearch.WordTrace]
  refine ⟨140955912543986212079259449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93970608362657474719506299 140955912543986212079259449)
  ·
    refine ⟨105716934407989659059444587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140955912543986212079259449 105716934407989659059444587)
    ·
      refine ⟨158575401611984488589166881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105716934407989659059444587 158575401611984488589166881)
      ·
        refine ⟨118931551208988366441875161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158575401611984488589166881 118931551208988366441875161)
        ·
          refine ⟨89198663406741274831406371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118931551208988366441875161 89198663406741274831406371)
          ·
            refine ⟨133797995110111912247109557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89198663406741274831406371 133797995110111912247109557)
            ·
              refine ⟨12543562041572991773166521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133797995110111912247109557 12543562041572991773166521)
              ·
                refine ⟨9407671531179743829874891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12543562041572991773166521 9407671531179743829874891)
                ·
                  refine ⟨14111507296769615744812337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9407671531179743829874891 14111507296769615744812337)
                  ·
                    refine ⟨10583630472577211808609253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14111507296769615744812337 10583630472577211808609253)
                    ·
                      refine ⟨1984430713608227214114235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10583630472577211808609253 1984430713608227214114235)
                      ·
                        rfl

theorem cell23_3864665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_3864665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864665 prefixEnd_3864665 := by exact prefixLift 3864665
  have htrace : WordTrace (prefixWord ++ tailWord_3864665) baseStart_3864665 baseEnd_3864665 := by
    simpa [prefixWord, tailWord_3864665, baseEnd_3864665] using wordTrace_append hprefix tailTrace_3864665
  have hstable : (prefixWord ++ tailWord_3864665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864665).length < 2 ^ (prefixWord ++ tailWord_3864665).sum := by decide
  have hdescent : baseEnd_3864665 < baseStart_3864665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864672 : List Nat := [2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 5]
def baseStart_3864672 : Nat := 118140960795 + 3864672 * 2 ^ 59
def prefixEnd_3864672 : Nat := 4983230072969 + 3 ^ 40 * 3864672 * 2
def baseEnd_3864672 : Nat := 1984434307972808686726703

theorem tailTrace_3864672 : CollatzResearch.WordTrace tailWord_3864672 prefixEnd_3864672 1984434307972808686726703 := by
  unfold tailWord_3864672
  simp only [CollatzResearch.WordTrace]
  refine ⟨70478083927480426137382135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93970778569973901516509513 70478083927480426137382135)
  ·
    refine ⟨105717125891220639206073203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70478083927480426137382135 105717125891220639206073203)
    ·
      refine ⟨158575688836830958809109805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105717125891220639206073203 158575688836830958809109805)
      ·
        refine ⟨59465883313811609553416177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158575688836830958809109805 59465883313811609553416177)
        ·
          refine ⟨44599412485358707165062133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59465883313811609553416177 44599412485358707165062133)
          ·
            refine ⟨4181194920502378796724575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44599412485358707165062133 4181194920502378796724575)
            ·
              refine ⟨6271792380753568195086863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4181194920502378796724575 6271792380753568195086863)
              ·
                refine ⟨9407688571130352292630295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6271792380753568195086863 9407688571130352292630295)
                ·
                  refine ⟨14111532856695528438945443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9407688571130352292630295 14111532856695528438945443)
                  ·
                    refine ⟨21167299285043292658418165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14111532856695528438945443 21167299285043292658418165)
                    ·
                      refine ⟨1984434307972808686726703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21167299285043292658418165 1984434307972808686726703)
                      ·
                        rfl

theorem cell23_3864672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_3864672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864672 prefixEnd_3864672 := by exact prefixLift 3864672
  have htrace : WordTrace (prefixWord ++ tailWord_3864672) baseStart_3864672 baseEnd_3864672 := by
    simpa [prefixWord, tailWord_3864672, baseEnd_3864672] using wordTrace_append hprefix tailTrace_3864672
  have hstable : (prefixWord ++ tailWord_3864672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864672).length < 2 ^ (prefixWord ++ tailWord_3864672).sum := by decide
  have hdescent : baseEnd_3864672 < baseStart_3864672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864736 : List Nat := [2, 1, 1, 4, 2, 4, 1, 2, 2, 1, 3]
def baseStart_3864736 : Nat := 118140960795 + 3864736 * 2 ^ 59
def prefixEnd_3864736 : Nat := 4983230072969 + 3 ^ 40 * 3864736 * 2
def baseEnd_3864736 : Nat := 1984467170734696436326409

theorem tailTrace_3864736 : CollatzResearch.WordTrace tailWord_3864736 prefixEnd_3864736 1984467170734696436326409 := by
  unfold tailWord_3864736
  simp only [CollatzResearch.WordTrace]
  refine ⟨70479251063364495602547031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93972334751152660803396041 70479251063364495602547031)
  ·
    refine ⟨105718876595046743403820547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70479251063364495602547031 105718876595046743403820547)
    ·
      refine ⟨158578314892570115105730821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105718876595046743403820547 158578314892570115105730821)
      ·
        refine ⟨29733434042356896582324529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158578314892570115105730821 29733434042356896582324529)
        ·
          refine ⟨22300075531767672436743397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29733434042356896582324529 22300075531767672436743397)
          ·
            refine ⟨4181264162206438581889387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22300075531767672436743397 4181264162206438581889387)
            ·
              refine ⟨6271896243309657872834081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4181264162206438581889387 6271896243309657872834081)
              ·
                refine ⟨4703922182482243404625561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6271896243309657872834081 4703922182482243404625561)
                ·
                  refine ⟨3527941636861682553469171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4703922182482243404625561 3527941636861682553469171)
                  ·
                    refine ⟨5291912455292523830203757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3527941636861682553469171 5291912455292523830203757)
                    ·
                      refine ⟨1984467170734696436326409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5291912455292523830203757 1984467170734696436326409)
                      ·
                        rfl

theorem cell23_3864736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_3864736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864736 prefixEnd_3864736 := by exact prefixLift 3864736
  have htrace : WordTrace (prefixWord ++ tailWord_3864736) baseStart_3864736 baseEnd_3864736 := by
    simpa [prefixWord, tailWord_3864736, baseEnd_3864736] using wordTrace_append hprefix tailTrace_3864736
  have hstable : (prefixWord ++ tailWord_3864736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864736).length < 2 ^ (prefixWord ++ tailWord_3864736).sum := by decide
  have hdescent : baseEnd_3864736 < baseStart_3864736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864753 : List Nat := [1, 2, 2, 5, 2, 1, 3, 1, 2, 1, 3]
def baseStart_3864753 : Nat := 118140960795 + 3864753 * 2 ^ 59
def prefixEnd_3864753 : Nat := 4983230072969 + 3 ^ 40 * 3864753 * 2
def baseEnd_3864753 : Nat := 1984475899905822869813831

theorem tailTrace_3864753 : CollatzResearch.WordTrace tailWord_3864753 prefixEnd_3864753 1984475899905822869813831 := by
  unfold tailWord_3864753
  simp only [CollatzResearch.WordTrace]
  refine ⟨140959122167667403108462913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93972748111778268738975275 140959122167667403108462913)
  ·
    refine ⟨105719341625750552331347185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140959122167667403108462913 105719341625750552331347185)
    ·
      refine ⟨79289506219312914248510389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105719341625750552331347185 79289506219312914248510389)
      ·
        refine ⟨7433391208060585710797849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79289506219312914248510389 7433391208060585710797849)
        ·
          refine ⟨5575043406045439283098387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7433391208060585710797849 5575043406045439283098387)
          ·
            refine ⟨8362565109068158924647581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5575043406045439283098387 8362565109068158924647581)
            ·
              refine ⟨3135961915900559596742843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8362565109068158924647581 3135961915900559596742843)
              ·
                refine ⟨4703942873850839395114265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135961915900559596742843 4703942873850839395114265)
                ·
                  refine ⟨3527957155388129546335699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4703942873850839395114265 3527957155388129546335699)
                  ·
                    refine ⟨5291935733082194319503549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3527957155388129546335699 5291935733082194319503549)
                    ·
                      refine ⟨1984475899905822869813831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5291935733082194319503549 1984475899905822869813831)
                      ·
                        rfl

theorem cell23_3864753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_3864753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864753 prefixEnd_3864753 := by exact prefixLift 3864753
  have htrace : WordTrace (prefixWord ++ tailWord_3864753) baseStart_3864753 baseEnd_3864753 := by
    simpa [prefixWord, tailWord_3864753, baseEnd_3864753] using wordTrace_append hprefix tailTrace_3864753
  have hstable : (prefixWord ++ tailWord_3864753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864753).length < 2 ^ (prefixWord ++ tailWord_3864753).sum := by decide
  have hdescent : baseEnd_3864753 < baseStart_3864753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864759 : List Nat := [1, 1, 3, 1, 4, 2, 3, 1, 1, 4, 2]
def baseStart_3864759 : Nat := 118140960795 + 3864759 * 2 ^ 59
def prefixEnd_3864759 : Nat := 4983230072969 + 3 ^ 40 * 3864759 * 2
def baseEnd_3864759 : Nat := 1984478980789749846338803

theorem tailTrace_3864759 : CollatzResearch.WordTrace tailWord_3864759 prefixEnd_3864759 1984478980789749846338803 := by
  unfold tailWord_3864759
  simp only [CollatzResearch.WordTrace]
  refine ⟨140959341005645666133181331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93972894003763777422120887 140959341005645666133181331)
  ·
    refine ⟨211439011508468499199771997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140959341005645666133181331 211439011508468499199771997)
    ·
      refine ⟨79289629315675687199914499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211439011508468499199771997 79289629315675687199914499)
      ·
        refine ⟨118934443973513530799871749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79289629315675687199914499 118934443973513530799871749)
        ·
          refine ⟨22300208245033787024975953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118934443973513530799871749 22300208245033787024975953)
          ·
            refine ⟨16725156183775340268731965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22300208245033787024975953 16725156183775340268731965)
            ·
              refine ⟨6271933568915752600774487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16725156183775340268731965 6271933568915752600774487)
              ·
                refine ⟨9407900353373628901161731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6271933568915752600774487 9407900353373628901161731)
                ·
                  refine ⟨14111850530060443351742597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9407900353373628901161731 14111850530060443351742597)
                  ·
                    refine ⟨2645971974386333128451737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14111850530060443351742597 2645971974386333128451737)
                    ·
                      refine ⟨1984478980789749846338803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2645971974386333128451737 1984478980789749846338803)
                      ·
                        rfl

theorem cell23_3864759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 4, 2].length) (baseStart_3864759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864759 prefixEnd_3864759 := by exact prefixLift 3864759
  have htrace : WordTrace (prefixWord ++ tailWord_3864759) baseStart_3864759 baseEnd_3864759 := by
    simpa [prefixWord, tailWord_3864759, baseEnd_3864759] using wordTrace_append hprefix tailTrace_3864759
  have hstable : (prefixWord ++ tailWord_3864759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864759).length < 2 ^ (prefixWord ++ tailWord_3864759).sum := by decide
  have hdescent : baseEnd_3864759 < baseStart_3864759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864795 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 4, 5]
def baseStart_3864795 : Nat := 118140960795 + 3864795 * 2 ^ 59
def prefixEnd_3864795 : Nat := 4983230072969 + 3 ^ 40 * 3864795 * 2
def baseEnd_3864795 : Nat := 661499155364437235162879

theorem tailTrace_3864795 : CollatzResearch.WordTrace tailWord_3864795 prefixEnd_3864795 661499155364437235162879 := by
  unfold tailWord_3864795
  simp only [CollatzResearch.WordTrace]
  refine ⟨140960654033515244281491839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93973769355676829520994559 140960654033515244281491839)
  ·
    refine ⟨211440981050272866422237759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140960654033515244281491839 211440981050272866422237759)
    ·
      refine ⟨317161471575409299633356639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211440981050272866422237759 317161471575409299633356639)
      ·
        refine ⟨475742207363113949450034959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317161471575409299633356639 475742207363113949450034959)
        ·
          refine ⟨713613311044670924175052439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475742207363113949450034959 713613311044670924175052439)
          ·
            refine ⟨1070419966567006386262578659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713613311044670924175052439 1070419966567006386262578659)
            ·
              refine ⟨1605629949850509579393867989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070419966567006386262578659 1605629949850509579393867989)
              ·
                refine ⟨37631951949621318267043781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1605629949850509579393867989 37631951949621318267043781)
                ·
                  refine ⟨7055990990553997175070709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37631951949621318267043781 7055990990553997175070709)
                  ·
                    refine ⟨661499155364437235162879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7055990990553997175070709 661499155364437235162879)
                    ·
                      rfl

theorem cell23_3864795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 5].length) (baseStart_3864795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864795 prefixEnd_3864795 := by exact prefixLift 3864795
  have htrace : WordTrace (prefixWord ++ tailWord_3864795) baseStart_3864795 baseEnd_3864795 := by
    simpa [prefixWord, tailWord_3864795, baseEnd_3864795] using wordTrace_append hprefix tailTrace_3864795
  have hstable : (prefixWord ++ tailWord_3864795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864795).length < 2 ^ (prefixWord ++ tailWord_3864795).sum := by decide
  have hdescent : baseEnd_3864795 < baseStart_3864795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864832 : List Nat := [2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 4]
def baseStart_3864832 : Nat := 118140960795 + 3864832 * 2 ^ 59
def prefixEnd_3864832 : Nat := 4983230072969 + 3 ^ 40 * 3864832 * 2
def baseEnd_3864832 : Nat := 1984516464877528060725967

theorem tailTrace_3864832 : CollatzResearch.WordTrace tailWord_3864832 prefixEnd_3864832 1984516464877528060725967 := by
  unfold tailWord_3864832
  simp only [CollatzResearch.WordTrace]
  refine ⟨70481001767190599800294375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93974669022920799733725833 70481001767190599800294375)
  ·
    refine ⟨105721502650785899700441563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70481001767190599800294375 105721502650785899700441563)
    ·
      refine ⟨158582253976178849550662345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105721502650785899700441563 158582253976178849550662345)
      ·
        refine ⟨118936690482134137162996759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158582253976178849550662345 118936690482134137162996759)
        ·
          refine ⟨178405035723201205744495139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118936690482134137162996759 178405035723201205744495139)
          ·
            refine ⟨267607553584801808616742709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178405035723201205744495139 267607553584801808616742709)
            ·
              refine ⟨25088208148575169557819629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 267607553584801808616742709 25088208148575169557819629)
              ·
                refine ⟨9408078055715688584182361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25088208148575169557819629 9408078055715688584182361)
                ·
                  refine ⟨7056058541786766438136771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9408078055715688584182361 7056058541786766438136771)
                  ·
                    refine ⟨10584087812680149657205157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7056058541786766438136771 10584087812680149657205157)
                    ·
                      refine ⟨1984516464877528060725967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10584087812680149657205157 1984516464877528060725967)
                      ·
                        rfl

theorem cell23_3864832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_3864832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864832 prefixEnd_3864832 := by exact prefixLift 3864832
  have htrace : WordTrace (prefixWord ++ tailWord_3864832) baseStart_3864832 baseEnd_3864832 := by
    simpa [prefixWord, tailWord_3864832, baseEnd_3864832] using wordTrace_append hprefix tailTrace_3864832
  have hstable : (prefixWord ++ tailWord_3864832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864832).length < 2 ^ (prefixWord ++ tailWord_3864832).sum := by decide
  have hdescent : baseEnd_3864832 < baseStart_3864832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864866 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 2, 4, 2]
def baseStart_3864866 : Nat := 118140960795 + 3864866 * 2 ^ 59
def prefixEnd_3864866 : Nat := 4983230072969 + 3 ^ 40 * 3864866 * 2
def baseEnd_3864866 : Nat := 1984533923219780927700811

theorem tailTrace_3864866 : CollatzResearch.WordTrace tailWord_3864866 prefixEnd_3864866 1984533923219780927700811 := by
  unfold tailWord_3864866
  simp only [CollatzResearch.WordTrace]
  refine ⟨35240810904064505851831613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93975495744172015604884301 35240810904064505851831613)
  ·
    refine ⟨13215304089024189694436855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35240810904064505851831613 13215304089024189694436855)
    ·
      refine ⟨19822956133536284541655283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13215304089024189694436855 19822956133536284541655283)
      ·
        refine ⟨29734434200304426812482925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19822956133536284541655283 29734434200304426812482925)
        ·
          refine ⟨11150412825114160054681097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29734434200304426812482925 11150412825114160054681097)
          ·
            refine ⟨8362809618835620041010823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11150412825114160054681097 8362809618835620041010823)
            ·
              refine ⟨12544214428253430061516235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8362809618835620041010823 12544214428253430061516235)
              ·
                refine ⟨18816321642380145092274353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12544214428253430061516235 18816321642380145092274353)
                ·
                  refine ⟨14112241231785108819205765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18816321642380145092274353 14112241231785108819205765)
                  ·
                    refine ⟨2646045230959707903601081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14112241231785108819205765 2646045230959707903601081)
                    ·
                      refine ⟨1984533923219780927700811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2646045230959707903601081 1984533923219780927700811)
                      ·
                        rfl

theorem cell23_3864866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_3864866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864866 prefixEnd_3864866 := by exact prefixLift 3864866
  have htrace : WordTrace (prefixWord ++ tailWord_3864866) baseStart_3864866 baseEnd_3864866 := by
    simpa [prefixWord, tailWord_3864866, baseEnd_3864866] using wordTrace_append hprefix tailTrace_3864866
  have hstable : (prefixWord ++ tailWord_3864866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864866).length < 2 ^ (prefixWord ++ tailWord_3864866).sum := by decide
  have hdescent : baseEnd_3864866 < baseStart_3864866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864916 : List Nat := [2, 4, 1, 1, 2, 2, 1, 3, 3, 1, 3]
def baseStart_3864916 : Nat := 118140960795 + 3864916 * 2 ^ 59
def prefixEnd_3864916 : Nat := 4983230072969 + 3 ^ 40 * 3864916 * 2
def baseEnd_3864916 : Nat := 1984559597252505732075581

theorem tailTrace_3864916 : CollatzResearch.WordTrace tailWord_3864916 prefixEnd_3864916 1984559597252505732075581 := by
  unfold tailWord_3864916
  simp only [CollatzResearch.WordTrace]
  refine ⟨70482533633038440973323301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93976711510717921297764401 70482533633038440973323301)
  ·
    refine ⟨13215475056194707682498119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70482533633038440973323301 13215475056194707682498119)
    ·
      refine ⟨19823212584292061523747179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13215475056194707682498119 19823212584292061523747179)
      ·
        refine ⟨29734818876438092285620769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19823212584292061523747179 29734818876438092285620769)
        ·
          refine ⟨22301114157328569214215577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29734818876438092285620769 22301114157328569214215577)
          ·
            refine ⟨16725835617996426910661683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22301114157328569214215577 16725835617996426910661683)
            ·
              refine ⟨25088753426994640365992525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16725835617996426910661683 25088753426994640365992525)
              ·
                refine ⟨9408282535122990137247197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25088753426994640365992525 9408282535122990137247197)
                ·
                  refine ⟨3528105950671121301467699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9408282535122990137247197 3528105950671121301467699)
                  ·
                    refine ⟨5292158926006681952201549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3528105950671121301467699 5292158926006681952201549)
                    ·
                      refine ⟨1984559597252505732075581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5292158926006681952201549 1984559597252505732075581)
                      ·
                        rfl

theorem cell23_3864916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_3864916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864916 prefixEnd_3864916 := by exact prefixLift 3864916
  have htrace : WordTrace (prefixWord ++ tailWord_3864916) baseStart_3864916 baseEnd_3864916 := by
    simpa [prefixWord, tailWord_3864916, baseEnd_3864916] using wordTrace_append hprefix tailTrace_3864916
  have hstable : (prefixWord ++ tailWord_3864916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864916).length < 2 ^ (prefixWord ++ tailWord_3864916).sum := by decide
  have hdescent : baseEnd_3864916 < baseStart_3864916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864936 : List Nat := [2, 1, 4, 2, 2, 2, 2, 2, 1, 5]
def baseStart_3864936 : Nat := 118140960795 + 3864936 * 2 ^ 59
def prefixEnd_3864936 : Nat := 4983230072969 + 3 ^ 40 * 3864936 * 2
def baseEnd_3864936 : Nat := 661523288955198551275163

theorem tailTrace_3864936 : CollatzResearch.WordTrace tailWord_3864936 prefixEnd_3864936 661523288955198551275163 := by
  unfold tailWord_3864936
  simp only [CollatzResearch.WordTrace]
  refine ⟨70482898363002212681187331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93977197817336283574916441 70482898363002212681187331)
  ·
    refine ⟨105724347544503319021780997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70482898363002212681187331 105724347544503319021780997)
    ·
      refine ⟨19823315164594372316583937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105724347544503319021780997 19823315164594372316583937)
      ·
        refine ⟨14867486373445779237437953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19823315164594372316583937 14867486373445779237437953)
        ·
          refine ⟨11150614780084334428078465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14867486373445779237437953 11150614780084334428078465)
          ·
            refine ⟨8362961085063250821058849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11150614780084334428078465 8362961085063250821058849)
            ·
              refine ⟨6272220813797438115794137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8362961085063250821058849 6272220813797438115794137)
              ·
                refine ⟨4704165610348078586845603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6272220813797438115794137 4704165610348078586845603)
                ·
                  refine ⟨7056248415522117880268405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4704165610348078586845603 7056248415522117880268405)
                  ·
                    refine ⟨661523288955198551275163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7056248415522117880268405 661523288955198551275163)
                    ·
                      rfl

theorem cell23_3864936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_3864936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864936 prefixEnd_3864936 := by exact prefixLift 3864936
  have htrace : WordTrace (prefixWord ++ tailWord_3864936) baseStart_3864936 baseEnd_3864936 := by
    simpa [prefixWord, tailWord_3864936, baseEnd_3864936] using wordTrace_append hprefix tailTrace_3864936
  have hstable : (prefixWord ++ tailWord_3864936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864936).length < 2 ^ (prefixWord ++ tailWord_3864936).sum := by decide
  have hdescent : baseEnd_3864936 < baseStart_3864936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864990 : List Nat := [4, 3, 1, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_3864990 : Nat := 118140960795 + 3864990 * 2 ^ 59
def prefixEnd_3864990 : Nat := 4983230072969 + 3 ^ 40 * 3864990 * 2
def baseEnd_3864990 : Nat := 1984597594820938442550241

theorem tailTrace_3864990 : CollatzResearch.WordTrace tailWord_3864990 prefixEnd_3864990 1984597594820938442550241 := by
  unfold tailWord_3864990
  simp only [CollatzResearch.WordTrace]
  refine ⟨17620970783476099073105053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93978510845205861723226949 17620970783476099073105053)
  ·
    refine ⟨6607864043803537152414395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17620970783476099073105053 6607864043803537152414395)
    ·
      refine ⟨9911796065705305728621593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6607864043803537152414395 9911796065705305728621593)
      ·
        refine ⟨7433847049278979296466195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9911796065705305728621593 7433847049278979296466195)
        ·
          refine ⟨11150770573918468944699293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7433847049278979296466195 11150770573918468944699293)
          ·
            refine ⟨4181538965219425854262235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11150770573918468944699293 4181538965219425854262235)
            ·
              refine ⟨6272308447829138781393353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4181538965219425854262235 6272308447829138781393353)
              ·
                refine ⟨4704231335871854086045015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6272308447829138781393353 4704231335871854086045015)
                ·
                  refine ⟨7056347003807781129067523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4704231335871854086045015 7056347003807781129067523)
                  ·
                    refine ⟨10584520505711671693601285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7056347003807781129067523 10584520505711671693601285)
                    ·
                      refine ⟨1984597594820938442550241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10584520505711671693601285 1984597594820938442550241)
                      ·
                        rfl

theorem cell23_3864990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_3864990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864990 prefixEnd_3864990 := by exact prefixLift 3864990
  have htrace : WordTrace (prefixWord ++ tailWord_3864990) baseStart_3864990 baseEnd_3864990 := by
    simpa [prefixWord, tailWord_3864990, baseEnd_3864990] using wordTrace_append hprefix tailTrace_3864990
  have hstable : (prefixWord ++ tailWord_3864990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864990).length < 2 ^ (prefixWord ++ tailWord_3864990).sum := by decide
  have hdescent : baseEnd_3864990 < baseStart_3864990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3864993 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 3, 2, 3]
def baseStart_3864993 : Nat := 118140960795 + 3864993 * 2 ^ 59
def prefixEnd_3864993 : Nat := 4983230072969 + 3 ^ 40 * 3864993 * 2
def baseEnd_3864993 : Nat := 1984599135262901930812727

theorem tailTrace_3864993 : CollatzResearch.WordTrace tailWord_3864993 prefixEnd_3864993 1984599135262901930812727 := by
  unfold tailWord_3864993
  simp only [CollatzResearch.WordTrace]
  refine ⟨140967875686797924097199633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93978583791198616064799755 140967875686797924097199633)
  ·
    refine ⟨105725906765098443072899725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140967875686797924097199633 105725906765098443072899725)
    ·
      refine ⟨39647215036911916152337397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105725906765098443072899725 39647215036911916152337397)
      ·
        refine ⟨3716926409710492139281631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39647215036911916152337397 3716926409710492139281631)
        ·
          refine ⟨5575389614565738208922447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3716926409710492139281631 5575389614565738208922447)
          ·
            refine ⟨8363084421848607313383671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5575389614565738208922447 8363084421848607313383671)
            ·
              refine ⟨12544626632772910970075507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8363084421848607313383671 12544626632772910970075507)
              ·
                refine ⟨18816939949159366455113261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12544626632772910970075507 18816939949159366455113261)
                ·
                  refine ⟨7056352480934762420667473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18816939949159366455113261 7056352480934762420667473)
                  ·
                    refine ⟨5292264360701071815500605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7056352480934762420667473 5292264360701071815500605)
                    ·
                      refine ⟨1984599135262901930812727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5292264360701071815500605 1984599135262901930812727)
                      ·
                        rfl

theorem cell23_3864993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_3864993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3864993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3864993 prefixEnd_3864993 := by exact prefixLift 3864993
  have htrace : WordTrace (prefixWord ++ tailWord_3864993) baseStart_3864993 baseEnd_3864993 := by
    simpa [prefixWord, tailWord_3864993, baseEnd_3864993] using wordTrace_append hprefix tailTrace_3864993
  have hstable : (prefixWord ++ tailWord_3864993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3864993).length < 2 ^ (prefixWord ++ tailWord_3864993).sum := by decide
  have hdescent : baseEnd_3864993 < baseStart_3864993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3864993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865046 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_3865046 : Nat := 118140960795 + 3865046 * 2 ^ 59
def prefixEnd_3865046 : Nat := 4983230072969 + 3 ^ 40 * 3865046 * 2
def baseEnd_3865046 : Nat := 1984626349737590223449983

theorem tailTrace_3865046 : CollatzResearch.WordTrace tailWord_3865046 prefixEnd_3865046 1984626349737590223449983 := by
  unfold tailWord_3865046
  simp only [CollatzResearch.WordTrace]
  refine ⟨8810613047225369634304937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93979872503737276099252661 8810613047225369634304937)
  ·
    refine ⟨6607959785419027225728703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8810613047225369634304937 6607959785419027225728703)
    ·
      refine ⟨9911939678128540838593055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6607959785419027225728703 9911939678128540838593055)
      ·
        refine ⟨14867909517192811257889583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9911939678128540838593055 14867909517192811257889583)
        ·
          refine ⟨22301864275789216886834375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14867909517192811257889583 22301864275789216886834375)
          ·
            refine ⟨33452796413683825330251563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22301864275789216886834375 33452796413683825330251563)
            ·
              refine ⟨50179194620525737995377345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33452796413683825330251563 50179194620525737995377345)
              ·
                refine ⟨37634395965394303496533009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50179194620525737995377345 37634395965394303496533009)
                ·
                  refine ⟨28225796974045727622399757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37634395965394303496533009 28225796974045727622399757)
                  ·
                    refine ⟨10584673865267147858399909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28225796974045727622399757 10584673865267147858399909)
                    ·
                      refine ⟨1984626349737590223449983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10584673865267147858399909 1984626349737590223449983)
                      ·
                        rfl

theorem cell23_3865046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_3865046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865046 prefixEnd_3865046 := by exact prefixLift 3865046
  have htrace : WordTrace (prefixWord ++ tailWord_3865046) baseStart_3865046 baseEnd_3865046 := by
    simpa [prefixWord, tailWord_3865046, baseEnd_3865046] using wordTrace_append hprefix tailTrace_3865046
  have hstable : (prefixWord ++ tailWord_3865046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865046).length < 2 ^ (prefixWord ++ tailWord_3865046).sum := by decide
  have hdescent : baseEnd_3865046 < baseStart_3865046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865049 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 2, 4, 3]
def baseStart_3865049 : Nat := 118140960795 + 3865049 * 2 ^ 59
def prefixEnd_3865049 : Nat := 4983230072969 + 3 ^ 40 * 3865049 * 2
def baseEnd_3865049 : Nat := 1984627890179553711712469

theorem tailTrace_3865049 : CollatzResearch.WordTrace tailWord_3865049 prefixEnd_3865049 1984627890179553711712469 := by
  unfold tailWord_3865049
  simp only [CollatzResearch.WordTrace]
  refine ⟨140969918174595045661238201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93979945449730030440825467 140969918174595045661238201)
  ·
    refine ⟨105727438630946284245928651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140969918174595045661238201 105727438630946284245928651)
    ·
      refine ⟨158591157946419426368892977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105727438630946284245928651 158591157946419426368892977)
      ·
        refine ⟨118943368459814569776669733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158591157946419426368892977 118943368459814569776669733)
        ·
          refine ⟨22301881586215231833125575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118943368459814569776669733 22301881586215231833125575)
          ·
            refine ⟨33452822379322847749688363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22301881586215231833125575 33452822379322847749688363)
            ·
              refine ⟨50179233568984271624532545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33452822379322847749688363 50179233568984271624532545)
              ·
                refine ⟨37634425176738203718399409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50179233568984271624532545 37634425176738203718399409)
                ·
                  refine ⟨28225818882553652788799557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37634425176738203718399409 28225818882553652788799557)
                  ·
                    refine ⟨5292341040478809897899917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28225818882553652788799557 5292341040478809897899917)
                    ·
                      refine ⟨1984627890179553711712469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5292341040478809897899917 1984627890179553711712469)
                      ·
                        rfl

theorem cell23_3865049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 4, 3].length) (baseStart_3865049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865049 prefixEnd_3865049 := by exact prefixLift 3865049
  have htrace : WordTrace (prefixWord ++ tailWord_3865049) baseStart_3865049 baseEnd_3865049 := by
    simpa [prefixWord, tailWord_3865049, baseEnd_3865049] using wordTrace_append hprefix tailTrace_3865049
  have hstable : (prefixWord ++ tailWord_3865049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865049).length < 2 ^ (prefixWord ++ tailWord_3865049).sum := by decide
  have hdescent : baseEnd_3865049 < baseStart_3865049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865063 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 4, 2, 2]
def baseStart_3865063 : Nat := 118140960795 + 3865063 * 2 ^ 59
def prefixEnd_3865063 : Nat := 4983230072969 + 3 ^ 40 * 3865063 * 2
def baseEnd_3865063 : Nat := 1984635078908716656937405

theorem tailTrace_3865063 : CollatzResearch.WordTrace tailWord_3865063 prefixEnd_3865063 1984635078908716656937405 := by
  unfold tailWord_3865063
  simp only [CollatzResearch.WordTrace]
  refine ⟨140970428796544326052247843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93980285864362884034831895 140970428796544326052247843)
  ·
    refine ⟨211455643194816489078371765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140970428796544326052247843 211455643194816489078371765)
    ·
      refine ⟨19823966549514045851097353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211455643194816489078371765 19823966549514045851097353)
      ·
        refine ⟨14867974912135534388323015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19823966549514045851097353 14867974912135534388323015)
        ·
          refine ⟨22301962368203301582484523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14867974912135534388323015 22301962368203301582484523)
          ·
            refine ⟨33452943552304952373726785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22301962368203301582484523 33452943552304952373726785)
            ·
              refine ⟨25089707664228714280295089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33452943552304952373726785 25089707664228714280295089)
              ·
                refine ⟨18817280748171535710221317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25089707664228714280295089 18817280748171535710221317)
                ·
                  refine ⟨3528240140282162945666497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18817280748171535710221317 3528240140282162945666497)
                  ·
                    refine ⟨2646180105211622209249873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3528240140282162945666497 2646180105211622209249873)
                    ·
                      refine ⟨1984635078908716656937405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2646180105211622209249873 1984635078908716656937405)
                      ·
                        rfl

theorem cell23_3865063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_3865063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865063 prefixEnd_3865063 := by exact prefixLift 3865063
  have htrace : WordTrace (prefixWord ++ tailWord_3865063) baseStart_3865063 baseEnd_3865063 := by
    simpa [prefixWord, tailWord_3865063, baseEnd_3865063] using wordTrace_append hprefix tailTrace_3865063
  have hstable : (prefixWord ++ tailWord_3865063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865063).length < 2 ^ (prefixWord ++ tailWord_3865063).sum := by decide
  have hdescent : baseEnd_3865063 < baseStart_3865063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865099 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 1, 7]
def baseStart_3865099 : Nat := 118140960795 + 3865099 * 2 ^ 59
def prefixEnd_3865099 : Nat := 4983230072969 + 3 ^ 40 * 3865099 * 2
def baseEnd_3865099 : Nat := 661551188070759505362413

theorem tailTrace_3865099 : CollatzResearch.WordTrace tailWord_3865099 prefixEnd_3865099 661551188070759505362413 := by
  unfold tailWord_3865099
  simp only [CollatzResearch.WordTrace]
  refine ⟨140971741824413904200558351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93981161216275936133705567 140971741824413904200558351)
  ·
    refine ⟨211457612736620856300837527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140971741824413904200558351 211457612736620856300837527)
    ·
      refine ⟨317186419104931284451256291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211457612736620856300837527 317186419104931284451256291)
      ·
        refine ⟨475779628657396926676884437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317186419104931284451256291 475779628657396926676884437)
        ·
          refine ⟨11151085046657740468989479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 475779628657396926676884437 11151085046657740468989479)
          ·
            refine ⟨16726627569986610703484219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11151085046657740468989479 16726627569986610703484219)
            ·
              refine ⟨25089941354979916055226329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16726627569986610703484219 25089941354979916055226329)
              ·
                refine ⟨18817456016234937041419747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25089941354979916055226329 18817456016234937041419747)
                ·
                  refine ⟨28226184024352405562129621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18817456016234937041419747 28226184024352405562129621)
                  ·
                    refine ⟨661551188070759505362413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28226184024352405562129621 661551188070759505362413)
                    ·
                      rfl

theorem cell23_3865099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 7].length) (baseStart_3865099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865099 prefixEnd_3865099 := by exact prefixLift 3865099
  have htrace : WordTrace (prefixWord ++ tailWord_3865099) baseStart_3865099 baseEnd_3865099 := by
    simpa [prefixWord, tailWord_3865099, baseEnd_3865099] using wordTrace_append hprefix tailTrace_3865099
  have hstable : (prefixWord ++ tailWord_3865099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865099).length < 2 ^ (prefixWord ++ tailWord_3865099).sum := by decide
  have hdescent : baseEnd_3865099 < baseStart_3865099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865120 : List Nat := [2, 1, 1, 6, 2, 2, 1, 3, 5]
def baseStart_3865120 : Nat := 118140960795 + 3865120 * 2 ^ 59
def prefixEnd_3865120 : Nat := 4983230072969 + 3 ^ 40 * 3865120 * 2
def baseEnd_3865120 : Nat := 220518260811780325991627

theorem tailTrace_3865120 : CollatzResearch.WordTrace tailWord_3865120 prefixEnd_3865120 220518260811780325991627 := by
  unfold tailWord_3865120
  simp only [CollatzResearch.WordTrace]
  refine ⟨70486253878668912393536407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93981671838225216524715209 70486253878668912393536407)
  ·
    refine ⟨105729380818003368590304611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70486253878668912393536407 105729380818003368590304611)
    ·
      refine ⟨158594071227005052885456917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105729380818003368590304611 158594071227005052885456917)
      ·
        refine ⟨7434097088765861854005793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 158594071227005052885456917 7434097088765861854005793)
        ·
          refine ⟨5575572816574396390504345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7434097088765861854005793 5575572816574396390504345)
          ·
            refine ⟨4181679612430797292878259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5575572816574396390504345 4181679612430797292878259)
            ·
              refine ⟨6272519418646195939317389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4181679612430797292878259 6272519418646195939317389)
              ·
                refine ⟨2352194781992323477244021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6272519418646195939317389 2352194781992323477244021)
                ·
                  refine ⟨220518260811780325991627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2352194781992323477244021 220518260811780325991627)
                  ·
                    rfl

theorem cell23_3865120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 5].length) (baseStart_3865120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865120 prefixEnd_3865120 := by exact prefixLift 3865120
  have htrace : WordTrace (prefixWord ++ tailWord_3865120) baseStart_3865120 baseEnd_3865120 := by
    simpa [prefixWord, tailWord_3865120, baseEnd_3865120] using wordTrace_append hprefix tailTrace_3865120
  have hstable : (prefixWord ++ tailWord_3865120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865120).length < 2 ^ (prefixWord ++ tailWord_3865120).sum := by decide
  have hdescent : baseEnd_3865120 < baseStart_3865120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865136 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 4, 4, 2]
def baseStart_3865136 : Nat := 118140960795 + 3865136 * 2 ^ 59
def prefixEnd_3865136 : Nat := 4983230072969 + 3 ^ 40 * 3865136 * 2
def baseEnd_3865136 : Nat := 1984672562996494871324569

theorem tailTrace_3865136 : CollatzResearch.WordTrace tailWord_3865136 prefixEnd_3865136 1984672562996494871324569 := by
  unfold tailWord_3865136
  simp only [CollatzResearch.WordTrace]
  refine ⟨70486545662639929759827631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93982060883519906346436841 70486545662639929759827631)
  ·
    refine ⟨105729818493959894639741447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70486545662639929759827631 105729818493959894639741447)
    ·
      refine ⟨158594727740939841959612171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105729818493959894639741447 158594727740939841959612171)
      ·
        refine ⟨237892091611409762939418257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158594727740939841959612171 237892091611409762939418257)
        ·
          refine ⟨178419068708557322204563693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237892091611409762939418257 178419068708557322204563693)
          ·
            refine ⟨66907150765708995826711385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178419068708557322204563693 66907150765708995826711385)
            ·
              refine ⟨50180363074281746870033539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66907150765708995826711385 50180363074281746870033539)
              ·
                refine ⟨75270544611422620305050309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50180363074281746870033539 75270544611422620305050309)
                ·
                  refine ⟨14113227114641741307196933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75270544611422620305050309 14113227114641741307196933)
                  ·
                    refine ⟨2646230083995326495099425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14113227114641741307196933 2646230083995326495099425)
                    ·
                      refine ⟨1984672562996494871324569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2646230083995326495099425 1984672562996494871324569)
                      ·
                        rfl

theorem cell23_3865136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 4, 4, 2].length) (baseStart_3865136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865136 prefixEnd_3865136 := by exact prefixLift 3865136
  have htrace : WordTrace (prefixWord ++ tailWord_3865136) baseStart_3865136 baseEnd_3865136 := by
    simpa [prefixWord, tailWord_3865136, baseEnd_3865136] using wordTrace_append hprefix tailTrace_3865136
  have hstable : (prefixWord ++ tailWord_3865136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865136).length < 2 ^ (prefixWord ++ tailWord_3865136).sum := by decide
  have hdescent : baseEnd_3865136 < baseStart_3865136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865197 : List Nat := [1, 5, 1, 1, 3, 1, 4, 2, 1, 4]
def baseStart_3865197 : Nat := 118140960795 + 3865197 * 2 ^ 59
def prefixEnd_3865197 : Nat := 4983230072969 + 3 ^ 40 * 3865197 * 2
def baseEnd_3865197 : Nat := 661567961772139710887263

theorem tailTrace_3865197 : CollatzResearch.WordTrace tailWord_3865197 prefixEnd_3865197 661567961772139710887263 := by
  unfold tailWord_3865197
  simp only [CollatzResearch.WordTrace]
  refine ⟨140975316178058866937625845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93983544118705911291750563 140975316178058866937625845)
  ·
    refine ⟨13216435891693018775402423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140975316178058866937625845 13216435891693018775402423)
    ·
      refine ⟨19824653837539528163103635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13216435891693018775402423 19824653837539528163103635)
      ·
        refine ⟨29736980756309292244655453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19824653837539528163103635 29736980756309292244655453)
        ·
          refine ⟨11151367783615984591745795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29736980756309292244655453 11151367783615984591745795)
          ·
            refine ⟨16727051675423976887618693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11151367783615984591745795 16727051675423976887618693)
            ·
              refine ⟨3136322189141995666428505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16727051675423976887618693 3136322189141995666428505)
              ·
                refine ⟨2352241641856496749821379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3136322189141995666428505 2352241641856496749821379)
                ·
                  refine ⟨3528362462784745124732069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2352241641856496749821379 3528362462784745124732069)
                  ·
                    refine ⟨661567961772139710887263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3528362462784745124732069 661567961772139710887263)
                    ·
                      rfl

theorem cell23_3865197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_3865197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865197 prefixEnd_3865197 := by exact prefixLift 3865197
  have htrace : WordTrace (prefixWord ++ tailWord_3865197) baseStart_3865197 baseEnd_3865197 := by
    simpa [prefixWord, tailWord_3865197, baseEnd_3865197] using wordTrace_append hprefix tailTrace_3865197
  have hstable : (prefixWord ++ tailWord_3865197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865197).length < 2 ^ (prefixWord ++ tailWord_3865197).sum := by decide
  have hdescent : baseEnd_3865197 < baseStart_3865197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865220 : List Nat := [2, 3, 2, 1, 3, 2, 1, 2, 3, 1, 3]
def baseStart_3865220 : Nat := 118140960795 + 3865220 * 2 ^ 59
def prefixEnd_3865220 : Nat := 4983230072969 + 3 ^ 40 * 3865220 * 2
def baseEnd_3865220 : Nat := 1984715695371472542674183

theorem tailTrace_3865220 : CollatzResearch.WordTrace tailWord_3865220 prefixEnd_3865220 1984715695371472542674183 := by
  unfold tailWord_3865220
  simp only [CollatzResearch.WordTrace]
  refine ⟨70488077528487770932856557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93984103371317027910475409 70488077528487770932856557)
  ·
    refine ⟨26433029073182914099821209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70488077528487770932856557 26433029073182914099821209)
    ·
      refine ⟨19824771804887185574865907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26433029073182914099821209 19824771804887185574865907)
      ·
        refine ⟨29737157707330778362298861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19824771804887185574865907 29737157707330778362298861)
        ·
          refine ⟨11151434140249041885862073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29737157707330778362298861 11151434140249041885862073)
          ·
            refine ⟨8363575605186781414396555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11151434140249041885862073 8363575605186781414396555)
            ·
              refine ⟨12545363407780172121594833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8363575605186781414396555 12545363407780172121594833)
              ·
                refine ⟨9409022555835129091196125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12545363407780172121594833 9409022555835129091196125)
                ·
                  refine ⟨3528383458438173409198547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9409022555835129091196125 3528383458438173409198547)
                  ·
                    refine ⟨5292575187657260113797821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3528383458438173409198547 5292575187657260113797821)
                    ·
                      refine ⟨1984715695371472542674183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5292575187657260113797821 1984715695371472542674183)
                      ·
                        rfl

theorem cell23_3865220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_3865220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865220 prefixEnd_3865220 := by exact prefixLift 3865220
  have htrace : WordTrace (prefixWord ++ tailWord_3865220) baseStart_3865220 baseEnd_3865220 := by
    simpa [prefixWord, tailWord_3865220, baseEnd_3865220] using wordTrace_append hprefix tailTrace_3865220
  have hstable : (prefixWord ++ tailWord_3865220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865220).length < 2 ^ (prefixWord ++ tailWord_3865220).sum := by decide
  have hdescent : baseEnd_3865220 < baseStart_3865220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865280 : List Nat := [2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 3]
def baseStart_3865280 : Nat := 118140960795 + 3865280 * 2 ^ 59
def prefixEnd_3865280 : Nat := 4983230072969 + 3 ^ 40 * 3865280 * 2
def baseEnd_3865280 : Nat := 1984746504210742307923907

theorem tailTrace_3865280 : CollatzResearch.WordTrace tailWord_3865280 prefixEnd_3865280 1984746504210742307923907 := by
  unfold tailWord_3865280
  simp only [CollatzResearch.WordTrace]
  refine ⟨70489171718379086056448647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93985562291172114741931529 70489171718379086056448647)
  ·
    refine ⟨105733757577568629084672971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70489171718379086056448647 105733757577568629084672971)
    ·
      refine ⟨158600636366352943627009457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105733757577568629084672971 158600636366352943627009457)
      ·
        refine ⟨118950477274764707720257093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158600636366352943627009457 118950477274764707720257093)
        ·
          refine ⟨22303214489018382697548205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118950477274764707720257093 22303214489018382697548205)
          ·
            refine ⟨8363705433381893511580577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22303214489018382697548205 8363705433381893511580577)
            ·
              refine ⟨6272779075036420133685433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8363705433381893511580577 6272779075036420133685433)
              ·
                refine ⟨4704584306277315100264075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6272779075036420133685433 4704584306277315100264075)
                ·
                  refine ⟨7056876459415972650396113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4704584306277315100264075 7056876459415972650396113)
                  ·
                    refine ⟨5292657344561979487797085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7056876459415972650396113 5292657344561979487797085)
                    ·
                      refine ⟨1984746504210742307923907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5292657344561979487797085 1984746504210742307923907)
                      ·
                        rfl

theorem cell23_3865280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 3].length) (baseStart_3865280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865280 prefixEnd_3865280 := by exact prefixLift 3865280
  have htrace : WordTrace (prefixWord ++ tailWord_3865280) baseStart_3865280 baseEnd_3865280 := by
    simpa [prefixWord, tailWord_3865280, baseEnd_3865280] using wordTrace_append hprefix tailTrace_3865280
  have hstable : (prefixWord ++ tailWord_3865280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865280).length < 2 ^ (prefixWord ++ tailWord_3865280).sum := by decide
  have hdescent : baseEnd_3865280 < baseStart_3865280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865294 : List Nat := [4, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2]
def baseStart_3865294 : Nat := 118140960795 + 3865294 * 2 ^ 59
def prefixEnd_3865294 : Nat := 4983230072969 + 3 ^ 40 * 3865294 * 2
def baseEnd_3865294 : Nat := 1984753692939905253148843

theorem tailTrace_3865294 : CollatzResearch.WordTrace tailWord_3865294 prefixEnd_3865294 1984753692939905253148843 := by
  unfold tailWord_3865294
  simp only [CollatzResearch.WordTrace]
  refine ⟨17622356757338431562988367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93985902705804968335937957 17622356757338431562988367)
  ·
    refine ⟨26433535136007647344482551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17622356757338431562988367 26433535136007647344482551)
    ·
      refine ⟨39650302704011471016723827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26433535136007647344482551 39650302704011471016723827)
      ·
        refine ⟨59475454056017206525085741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39650302704011471016723827 59475454056017206525085741)
        ·
          refine ⟨22303295271006452446907153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59475454056017206525085741 22303295271006452446907153)
          ·
            refine ⟨16727471453254839335180365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22303295271006452446907153 16727471453254839335180365)
            ·
              refine ⟨6272801794970564750692637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16727471453254839335180365 6272801794970564750692637)
              ·
                refine ⟨2352300673113961781509739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6272801794970564750692637 2352300673113961781509739)
                ·
                  refine ⟨3528451009670942672264609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2352300673113961781509739 3528451009670942672264609)
                  ·
                    refine ⟨2646338257253207004198457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3528451009670942672264609 2646338257253207004198457)
                    ·
                      refine ⟨1984753692939905253148843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2646338257253207004198457 1984753692939905253148843)
                      ·
                        rfl

theorem cell23_3865294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2].length) (baseStart_3865294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865294 prefixEnd_3865294 := by exact prefixLift 3865294
  have htrace : WordTrace (prefixWord ++ tailWord_3865294) baseStart_3865294 baseEnd_3865294 := by
    simpa [prefixWord, tailWord_3865294, baseEnd_3865294] using wordTrace_append hprefix tailTrace_3865294
  have hstable : (prefixWord ++ tailWord_3865294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865294).length < 2 ^ (prefixWord ++ tailWord_3865294).sum := by decide
  have hdescent : baseEnd_3865294 < baseStart_3865294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865300 : List Nat := [2, 4, 1, 3, 3, 1, 9]
def baseStart_3865300 : Nat := 118140960795 + 3865300 * 2 ^ 59
def prefixEnd_3865300 : Nat := 4983230072969 + 3 ^ 40 * 3865300 * 2
def baseEnd_3865300 : Nat := 24503170047207805304615

theorem tailTrace_3865300 : CollatzResearch.WordTrace tailWord_3865300 prefixEnd_3865300 24503170047207805304615 := by
  unfold tailWord_3865300
  simp only [CollatzResearch.WordTrace]
  refine ⟨70489536448342857764312677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93986048597790477019083569 70489536448342857764312677)
  ·
    refine ⟨13216788084064285830808627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70489536448342857764312677 13216788084064285830808627)
    ·
      refine ⟨19825182126096428746212941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13216788084064285830808627 19825182126096428746212941)
      ·
        refine ⟨7434443297286160779829853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19825182126096428746212941 7434443297286160779829853)
        ·
          refine ⟨2787916236482310292436195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7434443297286160779829853 2787916236482310292436195)
          ·
            refine ⟨4181874354723465438654293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2787916236482310292436195 4181874354723465438654293)
            ·
              refine ⟨24503170047207805304615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4181874354723465438654293 24503170047207805304615)
              ·
                rfl

theorem cell23_3865300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 9].length) (baseStart_3865300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865300 prefixEnd_3865300 := by exact prefixLift 3865300
  have htrace : WordTrace (prefixWord ++ tailWord_3865300) baseStart_3865300 baseEnd_3865300 := by
    simpa [prefixWord, tailWord_3865300, baseEnd_3865300] using wordTrace_append hprefix tailTrace_3865300
  have hstable : (prefixWord ++ tailWord_3865300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865300).length < 2 ^ (prefixWord ++ tailWord_3865300).sum := by decide
  have hdescent : baseEnd_3865300 < baseStart_3865300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865306 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5]
def baseStart_3865306 : Nat := 118140960795 + 3865306 * 2 ^ 59
def prefixEnd_3865306 : Nat := 4983230072969 + 3 ^ 40 * 3865306 * 2
def baseEnd_3865306 : Nat := 1984759854707759206198787

theorem tailTrace_3865306 : CollatzResearch.WordTrace tailWord_3865306 prefixEnd_3865306 1984759854707759206198787 := by
  unfold tailWord_3865306
  simp only [CollatzResearch.WordTrace]
  refine ⟨35244822933665994638335943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93986194489775985702229181 35244822933665994638335943)
  ·
    refine ⟨52867234400498991957503915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35244822933665994638335943 52867234400498991957503915)
    ·
      refine ⟨79300851600748487936255873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52867234400498991957503915 79300851600748487936255873)
      ·
        refine ⟨59475638700561365952191905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79300851600748487936255873 59475638700561365952191905)
        ·
          refine ⟨44606729025421024464143929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59475638700561365952191905 44606729025421024464143929)
          ·
            refine ⟨33455046769065768348107947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44606729025421024464143929 33455046769065768348107947)
            ·
              refine ⟨50182570153598652522161921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33455046769065768348107947 50182570153598652522161921)
              ·
                refine ⟨37636927615198989391621441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50182570153598652522161921 37636927615198989391621441)
                ·
                  refine ⟨28227695711399242043716081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37636927615198989391621441 28227695711399242043716081)
                  ·
                    refine ⟨21170771783549431532787061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28227695711399242043716081 21170771783549431532787061)
                    ·
                      refine ⟨1984759854707759206198787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21170771783549431532787061 1984759854707759206198787)
                      ·
                        rfl

theorem cell23_3865306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_3865306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865306 prefixEnd_3865306 := by exact prefixLift 3865306
  have htrace : WordTrace (prefixWord ++ tailWord_3865306) baseStart_3865306 baseEnd_3865306 := by
    simpa [prefixWord, tailWord_3865306, baseEnd_3865306] using wordTrace_append hprefix tailTrace_3865306
  have hstable : (prefixWord ++ tailWord_3865306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865306).length < 2 ^ (prefixWord ++ tailWord_3865306).sum := by decide
  have hdescent : baseEnd_3865306 < baseStart_3865306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865327 : List Nat := [1, 1, 2, 1, 5, 2, 4, 1, 2, 1, 3]
def baseStart_3865327 : Nat := 118140960795 + 3865327 * 2 ^ 59
def prefixEnd_3865327 : Nat := 4983230072969 + 3 ^ 40 * 3865327 * 2
def baseEnd_3865327 : Nat := 1984770637801503624036191

theorem tailTrace_3865327 : CollatzResearch.WordTrace tailWord_3865327 prefixEnd_3865327 1984770637801503624036191 := by
  unfold tailWord_3865327
  simp only [CollatzResearch.WordTrace]
  refine ⟨140980057667587899139858235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93986705111725266093238823 140980057667587899139858235)
  ·
    refine ⟨211470086501381848709787353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140980057667587899139858235 211470086501381848709787353)
    ·
      refine ⟨158602564876036386532340515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211470086501381848709787353 158602564876036386532340515)
      ·
        refine ⟨237903847314054579798510773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158602564876036386532340515 237903847314054579798510773)
        ·
          refine ⟨22303485685692616856110385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 237903847314054579798510773 22303485685692616856110385)
          ·
            refine ⟨16727614264269462642082789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22303485685692616856110385 16727614264269462642082789)
            ·
              refine ⟨3136427674550524245390523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16727614264269462642082789 3136427674550524245390523)
              ·
                refine ⟨4704641511825786368085785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3136427674550524245390523 4704641511825786368085785)
                ·
                  refine ⟨3528481133869339776064339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4704641511825786368085785 3528481133869339776064339)
                  ·
                    refine ⟨5292721700804009664096509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3528481133869339776064339 5292721700804009664096509)
                    ·
                      refine ⟨1984770637801503624036191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5292721700804009664096509 1984770637801503624036191)
                      ·
                        rfl

theorem cell23_3865327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 2, 1, 3].length) (baseStart_3865327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865327 prefixEnd_3865327 := by exact prefixLift 3865327
  have htrace : WordTrace (prefixWord ++ tailWord_3865327) baseStart_3865327 baseEnd_3865327 := by
    simpa [prefixWord, tailWord_3865327, baseEnd_3865327] using wordTrace_append hprefix tailTrace_3865327
  have hstable : (prefixWord ++ tailWord_3865327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865327).length < 2 ^ (prefixWord ++ tailWord_3865327).sum := by decide
  have hdescent : baseEnd_3865327 < baseStart_3865327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865336 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 4, 1, 5]
def baseStart_3865336 : Nat := 118140960795 + 3865336 * 2 ^ 59
def prefixEnd_3865336 : Nat := 4983230072969 + 3 ^ 40 * 3865336 * 2
def baseEnd_3865336 : Nat := 1984775259127394088823649

theorem tailTrace_3865336 : CollatzResearch.WordTrace tailWord_3865336 prefixEnd_3865336 1984775259127394088823649 := by
  unfold tailWord_3865336
  simp only [CollatzResearch.WordTrace]
  refine ⟨70490192962277646838467931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93986923949703529117957241 70490192962277646838467931)
  ·
    refine ⟨105735289443416470257701897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70490192962277646838467931 105735289443416470257701897)
    ·
      refine ⟨79301467082562352693276423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105735289443416470257701897 79301467082562352693276423)
      ·
        refine ⟨118952200623843529039914635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79301467082562352693276423 118952200623843529039914635)
        ·
          refine ⟨178428300935765293559871953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118952200623843529039914635 178428300935765293559871953)
          ·
            refine ⟨133821225701823970169903965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178428300935765293559871953 133821225701823970169903965)
            ·
              refine ⟨50182959638183988813713987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133821225701823970169903965 50182959638183988813713987)
              ·
                refine ⟨75274439457275983220570981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50182959638183988813713987 75274439457275983220570981)
                ·
                  refine ⟨14113957398239246853857059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75274439457275983220570981 14113957398239246853857059)
                  ·
                    refine ⟨21170936097358870280785589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14113957398239246853857059 21170936097358870280785589)
                    ·
                      refine ⟨1984775259127394088823649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21170936097358870280785589 1984775259127394088823649)
                      ·
                        rfl

theorem cell23_3865336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_3865336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865336 prefixEnd_3865336 := by exact prefixLift 3865336
  have htrace : WordTrace (prefixWord ++ tailWord_3865336) baseStart_3865336 baseEnd_3865336 := by
    simpa [prefixWord, tailWord_3865336, baseEnd_3865336] using wordTrace_append hprefix tailTrace_3865336
  have hstable : (prefixWord ++ tailWord_3865336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865336).length < 2 ^ (prefixWord ++ tailWord_3865336).sum := by decide
  have hdescent : baseEnd_3865336 < baseStart_3865336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865380 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 2, 2, 4]
def baseStart_3865380 : Nat := 118140960795 + 3865380 * 2 ^ 59
def prefixEnd_3865380 : Nat := 4983230072969 + 3 ^ 40 * 3865380 * 2
def baseEnd_3865380 : Nat := 1984797852276191916673447

theorem tailTrace_3865380 : CollatzResearch.WordTrace tailWord_3865380 prefixEnd_3865380 1984797852276191916673447 := by
  unfold tailWord_3865380
  simp only [CollatzResearch.WordTrace]
  refine ⟨70490995368197944595768797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93987993824263926127691729 70490995368197944595768797)
  ·
    refine ⟨26434123263074229223413299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70490995368197944595768797 26434123263074229223413299)
    ·
      refine ⟨39651184894611343835119949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26434123263074229223413299 39651184894611343835119949)
      ·
        refine ⟨14869194335479253938169981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39651184894611343835119949 14869194335479253938169981)
        ·
          refine ⟨5575947875804720226813743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14869194335479253938169981 5575947875804720226813743)
          ·
            refine ⟨8363921813707080340220615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5575947875804720226813743 8363921813707080340220615)
            ·
              refine ⟨12545882720560620510330923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8363921813707080340220615 12545882720560620510330923)
              ·
                refine ⟨18818824080840930765496385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12545882720560620510330923 18818824080840930765496385)
                ·
                  refine ⟨14114118060630698074122289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18818824080840930765496385 14114118060630698074122289)
                  ·
                    refine ⟨10585588545473023555591717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14114118060630698074122289 10585588545473023555591717)
                    ·
                      refine ⟨1984797852276191916673447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10585588545473023555591717 1984797852276191916673447)
                      ·
                        rfl

theorem cell23_3865380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_3865380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865380 prefixEnd_3865380 := by exact prefixLift 3865380
  have htrace : WordTrace (prefixWord ++ tailWord_3865380) baseStart_3865380 baseEnd_3865380 := by
    simpa [prefixWord, tailWord_3865380, baseEnd_3865380] using wordTrace_append hprefix tailTrace_3865380
  have hstable : (prefixWord ++ tailWord_3865380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865380).length < 2 ^ (prefixWord ++ tailWord_3865380).sum := by decide
  have hdescent : baseEnd_3865380 < baseStart_3865380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865390 : List Nat := [4, 1, 3, 2, 1, 2, 1, 2, 7]
def baseStart_3865390 : Nat := 118140960795 + 3865390 * 2 ^ 59
def prefixEnd_3865390 : Nat := 4983230072969 + 3 ^ 40 * 3865390 * 2
def baseEnd_3865390 : Nat := 220533665231415208616489

theorem tailTrace_3865390 : CollatzResearch.WordTrace tailWord_3865390 prefixEnd_3865390 220533665231415208616489 := by
  unfold tailWord_3865390
  simp only [CollatzResearch.WordTrace]
  refine ⟨17622794433294957612425203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93988236977573107266267749 17622794433294957612425203)
  ·
    refine ⟨26434191649942436418637805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17622794433294957612425203 26434191649942436418637805)
    ·
      refine ⟨9912821868728413656989177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26434191649942436418637805 9912821868728413656989177)
      ·
        refine ⟨7434616401546310242741883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9912821868728413656989177 7434616401546310242741883)
        ·
          refine ⟨11151924602319465364112825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7434616401546310242741883 11151924602319465364112825)
          ·
            refine ⟨8363943451739599023084619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11151924602319465364112825 8363943451739599023084619)
            ·
              refine ⟨12545915177609398534626929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8363943451739599023084619 12545915177609398534626929)
              ·
                refine ⟨9409436383207048900970197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12545915177609398534626929 9409436383207048900970197)
                ·
                  refine ⟨220533665231415208616489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9409436383207048900970197 220533665231415208616489)
                  ·
                    rfl

theorem cell23_3865390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_3865390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865390 prefixEnd_3865390 := by exact prefixLift 3865390
  have htrace : WordTrace (prefixWord ++ tailWord_3865390) baseStart_3865390 baseEnd_3865390 := by
    simpa [prefixWord, tailWord_3865390, baseEnd_3865390] using wordTrace_append hprefix tailTrace_3865390
  have hstable : (prefixWord ++ tailWord_3865390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865390).length < 2 ^ (prefixWord ++ tailWord_3865390).sum := by decide
  have hdescent : baseEnd_3865390 < baseStart_3865390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865440 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 2, 4, 2]
def baseStart_3865440 : Nat := 118140960795 + 3865440 * 2 ^ 59
def prefixEnd_3865440 : Nat := 4983230072969 + 3 ^ 40 * 3865440 * 2
def baseEnd_3865440 : Nat := 1984828661115461681923171

theorem tailTrace_3865440 : CollatzResearch.WordTrace tailWord_3865440 prefixEnd_3865440 1984828661115461681923171 := by
  unfold tailWord_3865440
  simp only [CollatzResearch.WordTrace]
  refine ⟨70492089558089259719360887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93989452744119012959147849 70492089558089259719360887)
  ·
    refine ⟨105738134337133889579041331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70492089558089259719360887 105738134337133889579041331)
    ·
      refine ⟨158607201505700834368561997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105738134337133889579041331 158607201505700834368561997)
      ·
        refine ⟨59477700564637812888210749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158607201505700834368561997 59477700564637812888210749)
        ·
          refine ⟨22304137711739179833079031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59477700564637812888210749 22304137711739179833079031)
          ·
            refine ⟨33456206567608769749618547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22304137711739179833079031 33456206567608769749618547)
            ·
              refine ⟨50184309851413154624427821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33456206567608769749618547 50184309851413154624427821)
              ·
                refine ⟨18819116194279932984160433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50184309851413154624427821 18819116194279932984160433)
                ·
                  refine ⟨14114337145709949738120325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18819116194279932984160433 14114337145709949738120325)
                  ·
                    refine ⟨2646438214820615575897561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14114337145709949738120325 2646438214820615575897561)
                    ·
                      refine ⟨1984828661115461681923171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2646438214820615575897561 1984828661115461681923171)
                      ·
                        rfl

theorem cell23_3865440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 2, 4, 2].length) (baseStart_3865440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865440 prefixEnd_3865440 := by exact prefixLift 3865440
  have htrace : WordTrace (prefixWord ++ tailWord_3865440) baseStart_3865440 baseEnd_3865440 := by
    simpa [prefixWord, tailWord_3865440, baseEnd_3865440] using wordTrace_append hprefix tailTrace_3865440
  have hstable : (prefixWord ++ tailWord_3865440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865440).length < 2 ^ (prefixWord ++ tailWord_3865440).sum := by decide
  have hdescent : baseEnd_3865440 < baseStart_3865440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865453 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_3865453 : Nat := 118140960795 + 3865453 * 2 ^ 59
def prefixEnd_3865453 : Nat := 4983230072969 + 3 ^ 40 * 3865453 * 2
def baseEnd_3865453 : Nat := 1984835336363970131060611

theorem tailTrace_3865453 : CollatzResearch.WordTrace tailWord_3865453 prefixEnd_3865453 1984835336363970131060611 := by
  unfold tailWord_3865453
  simp only [CollatzResearch.WordTrace]
  refine ⟨140984653265131422658945013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93989768843420948439296675 140984653265131422658945013)
  ·
    refine ⟨13217311243606070874276095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140984653265131422658945013 13217311243606070874276095)
    ·
      refine ⟨19825966865409106311414143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13217311243606070874276095 19825966865409106311414143)
      ·
        refine ⟨29738950298113659467121215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19825966865409106311414143 29738950298113659467121215)
        ·
          refine ⟨44608425447170489200681823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29738950298113659467121215 44608425447170489200681823)
          ·
            refine ⟨66912638170755733801022735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44608425447170489200681823 66912638170755733801022735)
            ·
              refine ⟨100368957256133600701534103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66912638170755733801022735 100368957256133600701534103)
              ·
                refine ⟨150553435884200401052301155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100368957256133600701534103 150553435884200401052301155)
                ·
                  refine ⟨225830153826300601578451733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150553435884200401052301155 225830153826300601578451733)
                  ·
                    refine ⟨10585788460607840698989925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 225830153826300601578451733 10585788460607840698989925)
                    ·
                      refine ⟨1984835336363970131060611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10585788460607840698989925 1984835336363970131060611)
                      ·
                        rfl

theorem cell23_3865453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_3865453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865453 prefixEnd_3865453 := by exact prefixLift 3865453
  have htrace : WordTrace (prefixWord ++ tailWord_3865453) baseStart_3865453 baseEnd_3865453 := by
    simpa [prefixWord, tailWord_3865453, baseEnd_3865453] using wordTrace_append hprefix tailTrace_3865453
  have hstable : (prefixWord ++ tailWord_3865453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865453).length < 2 ^ (prefixWord ++ tailWord_3865453).sum := by decide
  have hdescent : baseEnd_3865453 < baseStart_3865453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865467 : List Nat := [1, 1, 1, 1, 1, 5, 5, 3, 1, 4]
def baseStart_3865467 : Nat := 118140960795 + 3865467 * 2 ^ 59
def prefixEnd_3865467 : Nat := 4983230072969 + 3 ^ 40 * 3865467 * 2
def baseEnd_3865467 : Nat := 661614175031044358761849

theorem tailTrace_3865467 : CollatzResearch.WordTrace tailWord_3865467 prefixEnd_3865467 661614175031044358761849 := by
  unfold tailWord_3865467
  simp only [CollatzResearch.WordTrace]
  refine ⟨140985163887080703049954655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93990109258053802033303103 140985163887080703049954655)
  ·
    refine ⟨211477745830621054574931983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140985163887080703049954655 211477745830621054574931983)
    ·
      refine ⟨317216618745931581862397975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211477745830621054574931983 317216618745931581862397975)
      ·
        refine ⟨475824928118897372793596963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317216618745931581862397975 475824928118897372793596963)
        ·
          refine ⟨713737392178346059190395445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475824928118897372793596963 713737392178346059190395445)
          ·
            refine ⟨66912880516719943049099573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 713737392178346059190395445 66912880516719943049099573)
            ·
              refine ⟨6273082548442494660853085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66912880516719943049099573 6273082548442494660853085)
              ·
                refine ⟨2352405955665935497819907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6273082548442494660853085 2352405955665935497819907)
                ·
                  refine ⟨3528608933498903246729861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2352405955665935497819907 3528608933498903246729861)
                  ·
                    refine ⟨661614175031044358761849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3528608933498903246729861 661614175031044358761849)
                    ·
                      rfl

theorem cell23_3865467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 1, 4].length) (baseStart_3865467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865467 prefixEnd_3865467 := by exact prefixLift 3865467
  have htrace : WordTrace (prefixWord ++ tailWord_3865467) baseStart_3865467 baseEnd_3865467 := by
    simpa [prefixWord, tailWord_3865467, baseEnd_3865467] using wordTrace_append hprefix tailTrace_3865467
  have hstable : (prefixWord ++ tailWord_3865467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865467).length < 2 ^ (prefixWord ++ tailWord_3865467).sum := by decide
  have hdescent : baseEnd_3865467 < baseStart_3865467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865543 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 6]
def baseStart_3865543 : Nat := 118140960795 + 3865543 * 2 ^ 59
def prefixEnd_3865543 : Nat := 4983230072969 + 3 ^ 40 * 3865543 * 2
def baseEnd_3865543 : Nat := 1984881549622874778935197

theorem tailTrace_3865543 : CollatzResearch.WordTrace tailWord_3865543 prefixEnd_3865543 1984881549622874778935197 := by
  unfold tailWord_3865543
  simp only [CollatzResearch.WordTrace]
  refine ⟨140987935834805368029721283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93991957223203578686480855 140987935834805368029721283)
  ·
    refine ⟨211481903752208052044581925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140987935834805368029721283 211481903752208052044581925)
    ·
      refine ⟨39652856953539009758359111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211481903752208052044581925 39652856953539009758359111)
      ·
        refine ⟨59479285430308514637538667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39652856953539009758359111 59479285430308514637538667)
        ·
          refine ⟨89218928145462771956308001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59479285430308514637538667 89218928145462771956308001)
          ·
            refine ⟨66914196109097078967231001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89218928145462771956308001 66914196109097078967231001)
            ·
              refine ⟨50185647081822809225423251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66914196109097078967231001 50185647081822809225423251)
              ·
                refine ⟨75278470622734213838134877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50185647081822809225423251 75278470622734213838134877)
                ·
                  refine ⟨28229426483525330189300579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75278470622734213838134877 28229426483525330189300579)
                  ·
                    refine ⟨42344139725287995283950869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28229426483525330189300579 42344139725287995283950869)
                    ·
                      refine ⟨1984881549622874778935197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42344139725287995283950869 1984881549622874778935197)
                      ·
                        rfl

theorem cell23_3865543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_3865543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865543 prefixEnd_3865543 := by exact prefixLift 3865543
  have htrace : WordTrace (prefixWord ++ tailWord_3865543) baseStart_3865543 baseEnd_3865543 := by
    simpa [prefixWord, tailWord_3865543, baseEnd_3865543] using wordTrace_append hprefix tailTrace_3865543
  have hstable : (prefixWord ++ tailWord_3865543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865543).length < 2 ^ (prefixWord ++ tailWord_3865543).sum := by decide
  have hdescent : baseEnd_3865543 < baseStart_3865543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865557 : List Nat := [1, 3, 2, 3, 3, 1, 2, 1, 1, 6]
def baseStart_3865557 : Nat := 118140960795 + 3865557 * 2 ^ 59
def prefixEnd_3865557 : Nat := 4983230072969 + 3 ^ 40 * 3865557 * 2
def baseEnd_3865557 : Nat := 661629579450679241386711

theorem tailTrace_3865557 : CollatzResearch.WordTrace tailWord_3865557 prefixEnd_3865557 661629579450679241386711 := by
  unfold tailWord_3865557
  simp only [CollatzResearch.WordTrace]
  refine ⟨140988446456754648420730925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93992297637836432280487283 140988446456754648420730925)
  ·
    refine ⟨52870667421282993157774097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140988446456754648420730925 52870667421282993157774097)
    ·
      refine ⟨39653000565962244868330573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52870667421282993157774097 39653000565962244868330573)
      ·
        refine ⟨14869875212235841825623965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39653000565962244868330573 14869875212235841825623965)
        ·
          refine ⟨5576203204588440684608987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14869875212235841825623965 5576203204588440684608987)
          ·
            refine ⟨8364304806882661026913481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5576203204588440684608987 8364304806882661026913481)
            ·
              refine ⟨6273228605161995770185111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8364304806882661026913481 6273228605161995770185111)
              ·
                refine ⟨9409842907742993655277667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6273228605161995770185111 9409842907742993655277667)
                ·
                  refine ⟨14114764361614490482916501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9409842907742993655277667 14114764361614490482916501)
                  ·
                    refine ⟨661629579450679241386711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14114764361614490482916501 661629579450679241386711)
                    ·
                      rfl

theorem cell23_3865557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_3865557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865557 prefixEnd_3865557 := by exact prefixLift 3865557
  have htrace : WordTrace (prefixWord ++ tailWord_3865557) baseStart_3865557 baseEnd_3865557 := by
    simpa [prefixWord, tailWord_3865557, baseEnd_3865557] using wordTrace_append hprefix tailTrace_3865557
  have hstable : (prefixWord ++ tailWord_3865557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865557).length < 2 ^ (prefixWord ++ tailWord_3865557).sum := by decide
  have hdescent : baseEnd_3865557 < baseStart_3865557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865560 : List Nat := [2, 1, 2, 2, 2, 3, 1, 3, 1, 2, 4]
def baseStart_3865560 : Nat := 118140960795 + 3865560 * 2 ^ 59
def prefixEnd_3865560 : Nat := 4983230072969 + 3 ^ 40 * 3865560 * 2
def baseEnd_3865560 : Nat := 1984890278794001212422619

theorem tailTrace_3865560 : CollatzResearch.WordTrace tailWord_3865560 prefixEnd_3865560 1984890278794001212422619 := by
  unfold tailWord_3865560
  simp only [CollatzResearch.WordTrace]
  refine ⟨70494277937871889966545067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93992370583829186622060089 70494277937871889966545067)
  ·
    refine ⟨105741416906807834949817601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70494277937871889966545067 105741416906807834949817601)
    ·
      refine ⟨79306062680105876212363201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105741416906807834949817601 79306062680105876212363201)
      ·
        refine ⟨59479547010079407159272401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79306062680105876212363201 59479547010079407159272401)
        ·
          refine ⟨44609660257559555369454301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59479547010079407159272401 44609660257559555369454301)
          ·
            refine ⟨16728622596584833263545363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44609660257559555369454301 16728622596584833263545363)
            ·
              refine ⟨25092933894877249895318045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16728622596584833263545363 25092933894877249895318045)
              ·
                refine ⟨9409850210578968710744267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25092933894877249895318045 9409850210578968710744267)
                ·
                  refine ⟨14114775315868453066116401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9409850210578968710744267 14114775315868453066116401)
                  ·
                    refine ⟨10586081486901339799587301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14114775315868453066116401 10586081486901339799587301)
                    ·
                      refine ⟨1984890278794001212422619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10586081486901339799587301 1984890278794001212422619)
                      ·
                        rfl

theorem cell23_3865560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_3865560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865560 prefixEnd_3865560 := by exact prefixLift 3865560
  have htrace : WordTrace (prefixWord ++ tailWord_3865560) baseStart_3865560 baseEnd_3865560 := by
    simpa [prefixWord, tailWord_3865560, baseEnd_3865560] using wordTrace_append hprefix tailTrace_3865560
  have hstable : (prefixWord ++ tailWord_3865560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865560).length < 2 ^ (prefixWord ++ tailWord_3865560).sum := by decide
  have hdescent : baseEnd_3865560 < baseStart_3865560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865598 : List Nat := [4, 2, 2, 2, 2, 1, 2, 1, 3, 2, 2]
def baseStart_3865598 : Nat := 118140960795 + 3865598 * 2 ^ 59
def prefixEnd_3865598 : Nat := 4983230072969 + 3 ^ 40 * 3865598 * 2
def baseEnd_3865598 : Nat := 1984909791058872063747445

theorem tailTrace_3865598 : CollatzResearch.WordTrace tailWord_3865598 prefixEnd_3865598 1984909791058872063747445 := by
  unfold tailWord_3865598
  simp only [CollatzResearch.WordTrace]
  refine ⟨17623742731200764052871681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93993294566404074948648965 17623742731200764052871681)
  ·
    refine ⟨13217807048400573039653761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17623742731200764052871681 13217807048400573039653761)
    ·
      refine ⟨9913355286300429779740321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13217807048400573039653761 9913355286300429779740321)
      ·
        refine ⟨7435016464725322334805241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9913355286300429779740321 7435016464725322334805241)
        ·
          refine ⟨5576262348543991751103931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7435016464725322334805241 5576262348543991751103931)
          ·
            refine ⟨8364393522815987626655897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5576262348543991751103931 8364393522815987626655897)
            ·
              refine ⟨6273295142111990719991923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8364393522815987626655897 6273295142111990719991923)
              ·
                refine ⟨9409942713167986079987885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6273295142111990719991923 9409942713167986079987885)
                ·
                  refine ⟨3528728517437994779995457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9409942713167986079987885 3528728517437994779995457)
                  ·
                    refine ⟨2646546388078496084996593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3528728517437994779995457 2646546388078496084996593)
                    ·
                      refine ⟨1984909791058872063747445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2646546388078496084996593 1984909791058872063747445)
                      ·
                        rfl

theorem cell23_3865598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_3865598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865598 prefixEnd_3865598 := by exact prefixLift 3865598
  have htrace : WordTrace (prefixWord ++ tailWord_3865598) baseStart_3865598 baseEnd_3865598 := by
    simpa [prefixWord, tailWord_3865598, baseEnd_3865598] using wordTrace_append hprefix tailTrace_3865598
  have hstable : (prefixWord ++ tailWord_3865598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865598).length < 2 ^ (prefixWord ++ tailWord_3865598).sum := by decide
  have hdescent : baseEnd_3865598 < baseStart_3865598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865614 : List Nat := [4, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3]
def baseStart_3865614 : Nat := 118140960795 + 3865614 * 2 ^ 59
def prefixEnd_3865614 : Nat := 4983230072969 + 3 ^ 40 * 3865614 * 2
def baseEnd_3865614 : Nat := 1984918006749344001147371

theorem tailTrace_3865614 : CollatzResearch.WordTrace tailWord_3865614 prefixEnd_3865614 1984918006749344001147371 := by
  unfold tailWord_3865614
  simp only [CollatzResearch.WordTrace]
  refine ⟨17623815677193518394444487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93993683611698764770370597 17623815677193518394444487)
  ·
    refine ⟨26435723515790277591666731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17623815677193518394444487 26435723515790277591666731)
    ·
      refine ⟨39653585273685416387500097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26435723515790277591666731 39653585273685416387500097)
      ·
        refine ⟨29740188955264062290625073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39653585273685416387500097 29740188955264062290625073)
        ·
          refine ⟨22305141716448046717968805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29740188955264062290625073 22305141716448046717968805)
          ·
            refine ⟨4182214071834008759619151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22305141716448046717968805 4182214071834008759619151)
            ·
              refine ⟨6273321107751013139428727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4182214071834008759619151 6273321107751013139428727)
              ·
                refine ⟨9409981661626519709143091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6273321107751013139428727 9409981661626519709143091)
                ·
                  refine ⟨14114972492439779563714637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9409981661626519709143091 14114972492439779563714637)
                  ·
                    refine ⟨5293114684664917336392989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14114972492439779563714637 5293114684664917336392989)
                    ·
                      refine ⟨1984918006749344001147371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5293114684664917336392989 1984918006749344001147371)
                      ·
                        rfl

theorem cell23_3865614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_3865614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865614 prefixEnd_3865614 := by exact prefixLift 3865614
  have htrace : WordTrace (prefixWord ++ tailWord_3865614) baseStart_3865614 baseEnd_3865614 := by
    simpa [prefixWord, tailWord_3865614, baseEnd_3865614] using wordTrace_append hprefix tailTrace_3865614
  have hstable : (prefixWord ++ tailWord_3865614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865614).length < 2 ^ (prefixWord ++ tailWord_3865614).sum := by decide
  have hdescent : baseEnd_3865614 < baseStart_3865614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865624 : List Nat := [2, 1, 2, 3, 2, 2, 1, 4, 1, 3, 2]
def baseStart_3865624 : Nat := 118140960795 + 3865624 * 2 ^ 59
def prefixEnd_3865624 : Nat := 4983230072969 + 3 ^ 40 * 3865624 * 2
def baseEnd_3865624 : Nat := 1984923141555888962022325

theorem tailTrace_3865624 : CollatzResearch.WordTrace tailWord_3865624 prefixEnd_3865624 1984923141555888962022325 := by
  unfold tailWord_3865624
  simp only [CollatzResearch.WordTrace]
  refine ⟨70495445073755959431709963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93993926765007945908946617 70495445073755959431709963)
  ·
    refine ⟨105743167610633939147564945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70495445073755959431709963 105743167610633939147564945)
    ·
      refine ⟨79307375707975454360673709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105743167610633939147564945 79307375707975454360673709)
      ·
        refine ⟨29740265890490795385252641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79307375707975454360673709 29740265890490795385252641)
        ·
          refine ⟨22305199417868096538939481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29740265890490795385252641 22305199417868096538939481)
          ·
            refine ⟨16728899563401072404204611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22305199417868096538939481 16728899563401072404204611)
            ·
              refine ⟨25093349345101608606306917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16728899563401072404204611 25093349345101608606306917)
              ·
                refine ⟨4705003002206551613682547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25093349345101608606306917 4705003002206551613682547)
                ·
                  refine ⟨7057504503309827420523821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4705003002206551613682547 7057504503309827420523821)
                  ·
                    refine ⟨2646564188741185282696433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7057504503309827420523821 2646564188741185282696433)
                    ·
                      refine ⟨1984923141555888962022325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2646564188741185282696433 1984923141555888962022325)
                      ·
                        rfl

theorem cell23_3865624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_3865624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865624 prefixEnd_3865624 := by exact prefixLift 3865624
  have htrace : WordTrace (prefixWord ++ tailWord_3865624) baseStart_3865624 baseEnd_3865624 := by
    simpa [prefixWord, tailWord_3865624, baseEnd_3865624] using wordTrace_append hprefix tailTrace_3865624
  have hstable : (prefixWord ++ tailWord_3865624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865624).length < 2 ^ (prefixWord ++ tailWord_3865624).sum := by decide
  have hdescent : baseEnd_3865624 < baseStart_3865624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865632 : List Nat := [2, 1, 1, 7, 2, 1, 1, 3, 1, 2, 2]
def baseStart_3865632 : Nat := 118140960795 + 3865632 * 2 ^ 59
def prefixEnd_3865632 : Nat := 4983230072969 + 3 ^ 40 * 3865632 * 2
def baseEnd_3865632 : Nat := 1984927249401124930722289

theorem tailTrace_3865632 : CollatzResearch.WordTrace tailWord_3865632 prefixEnd_3865632 1984927249401124930722289 := by
  unfold tailWord_3865632
  simp only [CollatzResearch.WordTrace]
  refine ⟨70495590965741468114855575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93994121287655290819807433 70495590965741468114855575)
  ·
    refine ⟨105743386448612202172283363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70495590965741468114855575 105743386448612202172283363)
    ·
      refine ⟨158615079672918303258425045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105743386448612202172283363 158615079672918303258425045)
      ·
        refine ⟨3717540929834022732619337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 158615079672918303258425045 3717540929834022732619337)
        ·
          refine ⟨2788155697375517049464503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3717540929834022732619337 2788155697375517049464503)
          ·
            refine ⟨4182233546063275574196755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2788155697375517049464503 4182233546063275574196755)
            ·
              refine ⟨6273350319094913361295133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4182233546063275574196755 6273350319094913361295133)
              ·
                refine ⟨2352506369660592510485675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6273350319094913361295133 2352506369660592510485675)
                ·
                  refine ⟨3528759554490888765728513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2352506369660592510485675 3528759554490888765728513)
                  ·
                    refine ⟨2646569665868166574296385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3528759554490888765728513 2646569665868166574296385)
                    ·
                      refine ⟨1984927249401124930722289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2646569665868166574296385 1984927249401124930722289)
                      ·
                        rfl

theorem cell23_3865632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_3865632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865632 prefixEnd_3865632 := by exact prefixLift 3865632
  have htrace : WordTrace (prefixWord ++ tailWord_3865632) baseStart_3865632 baseEnd_3865632 := by
    simpa [prefixWord, tailWord_3865632, baseEnd_3865632] using wordTrace_append hprefix tailTrace_3865632
  have hstable : (prefixWord ++ tailWord_3865632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865632).length < 2 ^ (prefixWord ++ tailWord_3865632).sum := by decide
  have hdescent : baseEnd_3865632 < baseStart_3865632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865637 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 3, 4, 2]
def baseStart_3865637 : Nat := 118140960795 + 3865637 * 2 ^ 59
def prefixEnd_3865637 : Nat := 4983230072969 + 3 ^ 40 * 3865637 * 2
def baseEnd_3865637 : Nat := 1984929816804397411159765

theorem tailTrace_3865637 : CollatzResearch.WordTrace tailWord_3865637 prefixEnd_3865637 1984929816804397411159765 := by
  unfold tailWord_3865637
  simp only [CollatzResearch.WordTrace]
  refine ⟨140991364296464822083643165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93994242864309881389095443 140991364296464822083643165)
  ·
    refine ⟨52871761611174308281366187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140991364296464822083643165 52871761611174308281366187)
    ·
      refine ⟨79307642416761462422049281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52871761611174308281366187 79307642416761462422049281)
      ·
        refine ⟨59480731812571096816536961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79307642416761462422049281 59480731812571096816536961)
        ·
          refine ⟨44610548859428322612402721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59480731812571096816536961 44610548859428322612402721)
          ·
            refine ⟨33457911644571241959302041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44610548859428322612402721 33457911644571241959302041)
            ·
              refine ⟨25093433733428431469476531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33457911644571241959302041 25093433733428431469476531)
              ·
                refine ⟨37640150600142647204214797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25093433733428431469476531 37640150600142647204214797)
                ·
                  refine ⟨14115056475053492701580549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37640150600142647204214797 14115056475053492701580549)
                  ·
                    refine ⟨2646573089072529881546353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14115056475053492701580549 2646573089072529881546353)
                    ·
                      refine ⟨1984929816804397411159765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2646573089072529881546353 1984929816804397411159765)
                      ·
                        rfl

theorem cell23_3865637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 4, 2].length) (baseStart_3865637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865637 prefixEnd_3865637 := by exact prefixLift 3865637
  have htrace : WordTrace (prefixWord ++ tailWord_3865637) baseStart_3865637 baseEnd_3865637 := by
    simpa [prefixWord, tailWord_3865637, baseEnd_3865637] using wordTrace_append hprefix tailTrace_3865637
  have hstable : (prefixWord ++ tailWord_3865637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865637).length < 2 ^ (prefixWord ++ tailWord_3865637).sum := by decide
  have hdescent : baseEnd_3865637 < baseStart_3865637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865665 : List Nat := [1, 2, 5, 1, 4, 1, 2, 1, 2, 1, 3]
def baseStart_3865665 : Nat := 118140960795 + 3865665 * 2 ^ 59
def prefixEnd_3865665 : Nat := 4983230072969 + 3 ^ 40 * 3865665 * 2
def baseEnd_3865665 : Nat := 1984944194262723301609637

theorem tailTrace_3865665 : CollatzResearch.WordTrace tailWord_3865665 prefixEnd_3865665 1984944194262723301609637 := by
  unfold tailWord_3865665
  simp only [CollatzResearch.WordTrace]
  refine ⟨140992385540363382865662449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93994923693575588577108299 140992385540363382865662449)
  ·
    refine ⟨105744289155272537149246837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140992385540363382865662449 105744289155272537149246837)
    ·
      refine ⟨9913527108306800357741891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105744289155272537149246837 9913527108306800357741891)
      ·
        refine ⟨14870290662460200536612837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9913527108306800357741891 14870290662460200536612837)
        ·
          refine ⟨2788179499211287600614907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14870290662460200536612837 2788179499211287600614907)
          ·
            refine ⟨4182269248816931400922361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2788179499211287600614907 4182269248816931400922361)
            ·
              refine ⟨3136701936612698550691771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4182269248816931400922361 3136701936612698550691771)
              ·
                refine ⟨4705052904919047826037657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3136701936612698550691771 4705052904919047826037657)
                ·
                  refine ⟨3528789678689285869528243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4705052904919047826037657 3528789678689285869528243)
                  ·
                    refine ⟨5293184518033928804292365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3528789678689285869528243 5293184518033928804292365)
                    ·
                      refine ⟨1984944194262723301609637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5293184518033928804292365 1984944194262723301609637)
                      ·
                        rfl

theorem cell23_3865665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_3865665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865665 prefixEnd_3865665 := by exact prefixLift 3865665
  have htrace : WordTrace (prefixWord ++ tailWord_3865665) baseStart_3865665 baseEnd_3865665 := by
    simpa [prefixWord, tailWord_3865665, baseEnd_3865665] using wordTrace_append hprefix tailTrace_3865665
  have hstable : (prefixWord ++ tailWord_3865665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865665).length < 2 ^ (prefixWord ++ tailWord_3865665).sum := by decide
  have hdescent : baseEnd_3865665 < baseStart_3865665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865671 : List Nat := [1, 1, 4, 1, 3, 3, 1, 3, 2, 2, 2]
def baseStart_3865671 : Nat := 118140960795 + 3865671 * 2 ^ 59
def prefixEnd_3865671 : Nat := 4983230072969 + 3 ^ 40 * 3865671 * 2
def baseEnd_3865671 : Nat := 1984947275146650278134609

theorem tailTrace_3865671 : CollatzResearch.WordTrace tailWord_3865671 prefixEnd_3865671 1984947275146650278134609 := by
  unfold tailWord_3865671
  simp only [CollatzResearch.WordTrace]
  refine ⟨140992604378341645890380867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93995069585561097260253911 140992604378341645890380867)
  ·
    refine ⟨211488906567512468835571301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140992604378341645890380867 211488906567512468835571301)
    ·
      refine ⟨39654169981408587906669619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211488906567512468835571301 39654169981408587906669619)
      ·
        refine ⟨59481254972112881860004429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39654169981408587906669619 59481254972112881860004429)
        ·
          refine ⟨22305470614542330697501661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59481254972112881860004429 22305470614542330697501661)
          ·
            refine ⟨8364551480453374011563123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22305470614542330697501661 8364551480453374011563123)
            ·
              refine ⟨12546827220680061017344685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8364551480453374011563123 12546827220680061017344685)
              ·
                refine ⟨4705060207755022881504257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12546827220680061017344685 4705060207755022881504257)
                ·
                  refine ⟨3528795155816267161128193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4705060207755022881504257 3528795155816267161128193)
                  ·
                    refine ⟨2646596366862200370846145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3528795155816267161128193 2646596366862200370846145)
                    ·
                      refine ⟨1984947275146650278134609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2646596366862200370846145 1984947275146650278134609)
                      ·
                        rfl

theorem cell23_3865671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 2, 2].length) (baseStart_3865671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865671 prefixEnd_3865671 := by exact prefixLift 3865671
  have htrace : WordTrace (prefixWord ++ tailWord_3865671) baseStart_3865671 baseEnd_3865671 := by
    simpa [prefixWord, tailWord_3865671, baseEnd_3865671] using wordTrace_append hprefix tailTrace_3865671
  have hstable : (prefixWord ++ tailWord_3865671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865671).length < 2 ^ (prefixWord ++ tailWord_3865671).sum := by decide
  have hdescent : baseEnd_3865671 < baseStart_3865671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865737 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 5, 4]
def baseStart_3865737 : Nat := 118140960795 + 3865737 * 2 ^ 59
def prefixEnd_3865737 : Nat := 4983230072969 + 3 ^ 40 * 3865737 * 2
def baseEnd_3865737 : Nat := 661660388289949006636435

theorem tailTrace_3865737 : CollatzResearch.WordTrace tailWord_3865737 prefixEnd_3865737 661660388289949006636435 := by
  unfold tailWord_3865737
  simp only [CollatzResearch.WordTrace]
  refine ⟨140995011596102539162283465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93996674397401692774855643 140995011596102539162283465)
  ·
    refine ⟨105746258697076904371712599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140995011596102539162283465 105746258697076904371712599)
    ·
      refine ⟨158619388045615356557568899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105746258697076904371712599 158619388045615356557568899)
      ·
        refine ⟨237929082068423034836353349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158619388045615356557568899 237929082068423034836353349)
        ·
          refine ⟨44611702887829319031816253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237929082068423034836353349 44611702887829319031816253)
          ·
            refine ⟨16729388582935994636931095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44611702887829319031816253 16729388582935994636931095)
            ·
              refine ⟨25094082874403991955396643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16729388582935994636931095 25094082874403991955396643)
              ·
                refine ⟨37641124311605987933094965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25094082874403991955396643 37641124311605987933094965)
                ·
                  refine ⟨3528855404213061368727653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37641124311605987933094965 3528855404213061368727653)
                  ·
                    refine ⟨661660388289949006636435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3528855404213061368727653 661660388289949006636435)
                    ·
                      rfl

theorem cell23_3865737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 4].length) (baseStart_3865737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865737 prefixEnd_3865737 := by exact prefixLift 3865737
  have htrace : WordTrace (prefixWord ++ tailWord_3865737) baseStart_3865737 baseEnd_3865737 := by
    simpa [prefixWord, tailWord_3865737, baseEnd_3865737] using wordTrace_append hprefix tailTrace_3865737
  have hstable : (prefixWord ++ tailWord_3865737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865737).length < 2 ^ (prefixWord ++ tailWord_3865737).sum := by decide
  have hdescent : baseEnd_3865737 < baseStart_3865737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865740 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 6]
def baseStart_3865740 : Nat := 118140960795 + 3865740 * 2 ^ 59
def prefixEnd_3865740 : Nat := 4983230072969 + 3 ^ 40 * 3865740 * 2
def baseEnd_3865740 : Nat := 1984982705311810508171791

theorem tailTrace_3865740 : CollatzResearch.WordTrace tailWord_3865740 prefixEnd_3865740 1984982705311810508171791 := by
  unfold tailWord_3865740
  simp only [CollatzResearch.WordTrace]
  refine ⟨70497560507545835337321337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93996747343394447116428449 70497560507545835337321337)
  ·
    refine ⟨52873170380659376502991003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70497560507545835337321337 52873170380659376502991003)
    ·
      refine ⟨79309755570989064754486505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52873170380659376502991003 79309755570989064754486505)
      ·
        refine ⟨59482316678241798565864879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79309755570989064754486505 59482316678241798565864879)
        ·
          refine ⟨89223475017362697848797319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59482316678241798565864879 89223475017362697848797319)
          ·
            refine ⟨133835212526044046773195979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89223475017362697848797319 133835212526044046773195979)
            ·
              refine ⟨200752818789066070159793969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133835212526044046773195979 200752818789066070159793969)
              ·
                refine ⟨150564614091799552619845477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200752818789066070159793969 150564614091799552619845477)
                ·
                  refine ⟨28230865142212416116221027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150564614091799552619845477 28230865142212416116221027)
                  ·
                    refine ⟨42346297713318624174331541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28230865142212416116221027 42346297713318624174331541)
                    ·
                      refine ⟨1984982705311810508171791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42346297713318624174331541 1984982705311810508171791)
                      ·
                        rfl

theorem cell23_3865740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_3865740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865740 prefixEnd_3865740 := by exact prefixLift 3865740
  have htrace : WordTrace (prefixWord ++ tailWord_3865740) baseStart_3865740 baseEnd_3865740 := by
    simpa [prefixWord, tailWord_3865740, baseEnd_3865740] using wordTrace_append hprefix tailTrace_3865740
  have hstable : (prefixWord ++ tailWord_3865740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865740).length < 2 ^ (prefixWord ++ tailWord_3865740).sum := by decide
  have hdescent : baseEnd_3865740 < baseStart_3865740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865817 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 5, 1, 4]
def baseStart_3865817 : Nat := 118140960795 + 3865817 * 2 ^ 59
def prefixEnd_3865817 : Nat := 4983230072969 + 3 ^ 40 * 3865817 * 2
def baseEnd_3865817 : Nat := 1985022243322206706908937

theorem tailTrace_3865817 : CollatzResearch.WordTrace tailWord_3865817 prefixEnd_3865817 1985022243322206706908937 := by
  unfold tailWord_3865817
  simp only [CollatzResearch.WordTrace]
  refine ⟨140997929435812712825195705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93998619623875141883463803 140997929435812712825195705)
  ·
    refine ⟨105748447076859534618896779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140997929435812712825195705 105748447076859534618896779)
    ·
      refine ⟨158622670615289301928345169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105748447076859534618896779 158622670615289301928345169)
      ·
        refine ⟨118967002961466976446258877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158622670615289301928345169 118967002961466976446258877)
        ·
          refine ⟨44612626110550116167347079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118967002961466976446258877 44612626110550116167347079)
          ·
            refine ⟨66918939165825174251020619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44612626110550116167347079 66918939165825174251020619)
            ·
              refine ⟨100378408748737761376530929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66918939165825174251020619 100378408748737761376530929)
              ·
                refine ⟨75283806561553321032398197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100378408748737761376530929 75283806561553321032398197)
                ·
                  refine ⟨7057856865145623846787331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75283806561553321032398197 7057856865145623846787331)
                  ·
                    refine ⟨10586785297718435770180997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7057856865145623846787331 10586785297718435770180997)
                    ·
                      refine ⟨1985022243322206706908937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10586785297718435770180997 1985022243322206706908937)
                      ·
                        rfl

theorem cell23_3865817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_3865817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865817 prefixEnd_3865817 := by exact prefixLift 3865817
  have htrace : WordTrace (prefixWord ++ tailWord_3865817) baseStart_3865817 baseEnd_3865817 := by
    simpa [prefixWord, tailWord_3865817, baseEnd_3865817] using wordTrace_append hprefix tailTrace_3865817
  have hstable : (prefixWord ++ tailWord_3865817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865817).length < 2 ^ (prefixWord ++ tailWord_3865817).sum := by decide
  have hdescent : baseEnd_3865817 < baseStart_3865817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865857 : List Nat := [1, 2, 4, 1, 1, 3, 2, 9]
def baseStart_3865857 : Nat := 118140960795 + 3865857 * 2 ^ 59
def prefixEnd_3865857 : Nat := 4983230072969 + 3 ^ 40 * 3865857 * 2
def baseEnd_3865857 : Nat := 73520103057347650015139

theorem tailTrace_3865857 : CollatzResearch.WordTrace tailWord_3865857 prefixEnd_3865857 73520103057347650015139 := by
  unfold tailWord_3865857
  simp only [CollatzResearch.WordTrace]
  refine ⟨140999388355667799656651825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93999592237111866437767883 140999388355667799656651825)
  ·
    refine ⟨105749541266750849742488869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140999388355667799656651825 105749541266750849742488869)
    ·
      refine ⟨19828038987515784326716663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105749541266750849742488869 19828038987515784326716663)
      ·
        refine ⟨29742058481273676490074995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19828038987515784326716663 29742058481273676490074995)
        ·
          refine ⟨44613087721910514735112493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29742058481273676490074995 44613087721910514735112493)
          ·
            refine ⟨16729907895716443025667185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44613087721910514735112493 16729907895716443025667185)
            ·
              refine ⟨12547430921787332269250389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16729907895716443025667185 12547430921787332269250389)
              ·
                refine ⟨73520103057347650015139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12547430921787332269250389 73520103057347650015139)
                ·
                  rfl

theorem cell23_3865857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 9].length) (baseStart_3865857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865857 prefixEnd_3865857 := by exact prefixLift 3865857
  have htrace : WordTrace (prefixWord ++ tailWord_3865857) baseStart_3865857 baseEnd_3865857 := by
    simpa [prefixWord, tailWord_3865857, baseEnd_3865857] using wordTrace_append hprefix tailTrace_3865857
  have hstable : (prefixWord ++ tailWord_3865857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865857).length < 2 ^ (prefixWord ++ tailWord_3865857).sum := by decide
  have hdescent : baseEnd_3865857 < baseStart_3865857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865874 : List Nat := [3, 2, 4, 2, 12]
def baseStart_3865874 : Nat := 118140960795 + 3865874 * 2 ^ 59
def prefixEnd_3865874 : Nat := 4983230072969 + 3 ^ 40 * 3865874 * 2
def baseEnd_3865874 : Nat := 2722978754073406013575

theorem tailTrace_3865874 : CollatzResearch.WordTrace tailWord_3865874 prefixEnd_3865874 2722978754073406013575 := by
  unfold tailWord_3865874
  simp only [CollatzResearch.WordTrace]
  refine ⟨35250002099151552890005169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94000005597737474373347117 35250002099151552890005169)
  ·
    refine ⟨26437501574363664667503877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35250002099151552890005169 26437501574363664667503877)
    ·
      refine ⟨4957031545193187125156977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26437501574363664667503877 4957031545193187125156977)
      ·
        refine ⟨3717773658894890343867733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4957031545193187125156977 3717773658894890343867733)
        ·
          refine ⟨2722978754073406013575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3717773658894890343867733 2722978754073406013575)
          ·
            rfl

theorem cell23_3865874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 12].length) (baseStart_3865874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865874 prefixEnd_3865874 := by exact prefixLift 3865874
  have htrace : WordTrace (prefixWord ++ tailWord_3865874) baseStart_3865874 baseEnd_3865874 := by
    simpa [prefixWord, tailWord_3865874, baseEnd_3865874] using wordTrace_append hprefix tailTrace_3865874
  have hstable : (prefixWord ++ tailWord_3865874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865874).length < 2 ^ (prefixWord ++ tailWord_3865874).sum := by decide
  have hdescent : baseEnd_3865874 < baseStart_3865874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865964 : List Nat := [2, 2, 1, 1, 5, 1, 2, 2, 7]
def baseStart_3865964 : Nat := 118140960795 + 3865964 * 2 ^ 59
def prefixEnd_3865964 : Nat := 4983230072969 + 3 ^ 40 * 3865964 * 2
def baseEnd_3865964 : Nat := 220566413886490847974529

theorem tailTrace_3865964 : CollatzResearch.WordTrace tailWord_3865964 prefixEnd_3865964 220566413886490847974529 := by
  unfold tailWord_3865964
  simp only [CollatzResearch.WordTrace]
  refine ⟨70501645483140078465398473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94002193977520104620531297 70501645483140078465398473)
  ·
    refine ⟨52876234112355058849048855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70501645483140078465398473 52876234112355058849048855)
    ·
      refine ⟨79314351168532588273573283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52876234112355058849048855 79314351168532588273573283)
      ·
        refine ⟨118971526752798882410359925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79314351168532588273573283 118971526752798882410359925)
        ·
          refine ⟨11153580633074895225971243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118971526752798882410359925 11153580633074895225971243)
          ·
            refine ⟨16730370949612342838956865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11153580633074895225971243 16730370949612342838956865)
            ·
              refine ⟨12547778212209257129217649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16730370949612342838956865 12547778212209257129217649)
              ·
                refine ⟨9410833659156942846913237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12547778212209257129217649 9410833659156942846913237)
                ·
                  refine ⟨220566413886490847974529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9410833659156942846913237 220566413886490847974529)
                  ·
                    rfl

theorem cell23_3865964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 7].length) (baseStart_3865964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865964 prefixEnd_3865964 := by exact prefixLift 3865964
  have htrace : WordTrace (prefixWord ++ tailWord_3865964) baseStart_3865964 baseEnd_3865964 := by
    simpa [prefixWord, tailWord_3865964, baseEnd_3865964] using wordTrace_append hprefix tailTrace_3865964
  have hstable : (prefixWord ++ tailWord_3865964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865964).length < 2 ^ (prefixWord ++ tailWord_3865964).sum := by decide
  have hdescent : baseEnd_3865964 < baseStart_3865964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3865998 : List Nat := [4, 1, 1, 4, 2, 2, 1, 1, 7]
def baseStart_3865998 : Nat := 118140960795 + 3865998 * 2 ^ 59
def prefixEnd_3865998 : Nat := 4983230072969 + 3 ^ 40 * 3865998 * 2
def baseEnd_3865998 : Nat := 220568353702296722082845

theorem tailTrace_3865998 : CollatzResearch.WordTrace tailWord_3865998 prefixEnd_3865998 220568353702296722082845 := by
  unfold tailWord_3865998
  simp only [CollatzResearch.WordTrace]
  refine ⟨17625566381019622592191831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94003020698771320491689765 17625566381019622592191831)
  ·
    refine ⟨26438349571529433888287747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17625566381019622592191831 26438349571529433888287747)
    ·
      refine ⟨39657524357294150832431621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26438349571529433888287747 39657524357294150832431621)
      ·
        refine ⟨7435785816992653281080929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39657524357294150832431621 7435785816992653281080929)
        ·
          refine ⟨5576839362744489960810697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7435785816992653281080929 5576839362744489960810697)
          ·
            refine ⟨4182629522058367470608023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5576839362744489960810697 4182629522058367470608023)
            ·
              refine ⟨6273944283087551205912035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4182629522058367470608023 6273944283087551205912035)
              ·
                refine ⟨9410916424631326808868053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6273944283087551205912035 9410916424631326808868053)
                ·
                  refine ⟨220568353702296722082845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9410916424631326808868053 220568353702296722082845)
                  ·
                    rfl

theorem cell23_3865998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_3865998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3865998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3865998 prefixEnd_3865998 := by exact prefixLift 3865998
  have htrace : WordTrace (prefixWord ++ tailWord_3865998) baseStart_3865998 baseEnd_3865998 := by
    simpa [prefixWord, tailWord_3865998, baseEnd_3865998] using wordTrace_append hprefix tailTrace_3865998
  have hstable : (prefixWord ++ tailWord_3865998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3865998).length < 2 ^ (prefixWord ++ tailWord_3865998).sum := by decide
  have hdescent : baseEnd_3865998 < baseStart_3865998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3865998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866051 : List Nat := [1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 3]
def baseStart_3866051 : Nat := 118140960795 + 3866051 * 2 ^ 59
def prefixEnd_3866051 : Nat := 4983230072969 + 3 ^ 40 * 3866051 * 2
def baseEnd_3866051 : Nat := 1985142397795358791382861

theorem tailTrace_3866051 : CollatzResearch.WordTrace tailWord_3866051 prefixEnd_3866051 1985142397795358791382861 := by
  unfold tailWord_3866051
  simp only [CollatzResearch.WordTrace]
  refine ⟨141006464116964970789214007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94004309411309980526142671 141006464116964970789214007)
  ·
    refine ⟨211509696175447456183821011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141006464116964970789214007 211509696175447456183821011)
    ·
      refine ⟨317264544263171184275731517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211509696175447456183821011 317264544263171184275731517)
      ·
        refine ⟨118974204098689194103399319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317264544263171184275731517 118974204098689194103399319)
        ·
          refine ⟨178461306148033791155098979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118974204098689194103399319 178461306148033791155098979)
          ·
            refine ⟨267691959222050686732648469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178461306148033791155098979 267691959222050686732648469)
            ·
              refine ⟨12548060588533625940592897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 267691959222050686732648469 12548060588533625940592897)
              ·
                refine ⟨9411045441400219455444673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12548060588533625940592897 9411045441400219455444673)
                ·
                  refine ⟨7058284081050164591583505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9411045441400219455444673 7058284081050164591583505)
                  ·
                    refine ⟨5293713060787623443687629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7058284081050164591583505 5293713060787623443687629)
                    ·
                      refine ⟨1985142397795358791382861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5293713060787623443687629 1985142397795358791382861)
                      ·
                        rfl

theorem cell23_3866051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 3].length) (baseStart_3866051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866051 prefixEnd_3866051 := by exact prefixLift 3866051
  have htrace : WordTrace (prefixWord ++ tailWord_3866051) baseStart_3866051 baseEnd_3866051 := by
    simpa [prefixWord, tailWord_3866051, baseEnd_3866051] using wordTrace_append hprefix tailTrace_3866051
  have hstable : (prefixWord ++ tailWord_3866051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866051).length < 2 ^ (prefixWord ++ tailWord_3866051).sum := by decide
  have hdescent : baseEnd_3866051 < baseStart_3866051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866085 : List Nat := [1, 3, 1, 5, 1, 3, 1, 1, 2, 2, 3]
def baseStart_3866085 : Nat := 118140960795 + 3866085 * 2 ^ 59
def prefixEnd_3866085 : Nat := 4983230072969 + 3 ^ 40 * 3866085 * 2
def baseEnd_3866085 : Nat := 1985159856137611658357705

theorem tailTrace_3866085 : CollatzResearch.WordTrace tailWord_3866085 prefixEnd_3866085 1985159856137611658357705 := by
  unfold tailWord_3866085
  simp only [CollatzResearch.WordTrace]
  refine ⟨141007704198841794595951709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94005136132561196397301139 141007704198841794595951709)
  ·
    refine ⟨52877889074565672973481891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141007704198841794595951709 52877889074565672973481891)
    ·
      refine ⟨79316833611848509460222837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52877889074565672973481891 79316833611848509460222837)
      ·
        refine ⟨7435953151110797761895891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79316833611848509460222837 7435953151110797761895891)
        ·
          refine ⟨11153929726666196642843837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7435953151110797761895891 11153929726666196642843837)
          ·
            refine ⟨4182723647499823741066439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11153929726666196642843837 4182723647499823741066439)
            ·
              refine ⟨6274085471249735611599659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4182723647499823741066439 6274085471249735611599659)
              ·
                refine ⟨9411128206874603417399489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6274085471249735611599659 9411128206874603417399489)
                ·
                  refine ⟨7058346155155952563049617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9411128206874603417399489 7058346155155952563049617)
                  ·
                    refine ⟨5293759616366964422287213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7058346155155952563049617 5293759616366964422287213)
                    ·
                      refine ⟨1985159856137611658357705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5293759616366964422287213 1985159856137611658357705)
                      ·
                        rfl

theorem cell23_3866085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_3866085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866085 prefixEnd_3866085 := by exact prefixLift 3866085
  have htrace : WordTrace (prefixWord ++ tailWord_3866085) baseStart_3866085 baseEnd_3866085 := by
    simpa [prefixWord, tailWord_3866085, baseEnd_3866085] using wordTrace_append hprefix tailTrace_3866085
  have hstable : (prefixWord ++ tailWord_3866085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866085).length < 2 ^ (prefixWord ++ tailWord_3866085).sum := by decide
  have hdescent : baseEnd_3866085 < baseStart_3866085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866108 : List Nat := [2, 2, 2, 1, 2, 1, 2, 4, 2, 3, 2]
def baseStart_3866108 : Nat := 118140960795 + 3866108 * 2 ^ 59
def prefixEnd_3866108 : Nat := 4983230072969 + 3 ^ 40 * 3866108 * 2
def baseEnd_3866108 : Nat := 1985171666192665068370099

theorem tailTrace_3866108 : CollatzResearch.WordTrace tailWord_3866108 prefixEnd_3866108 1985171666192665068370099 := by
  unfold tailWord_3866108
  simp only [CollatzResearch.WordTrace]
  refine ⟨70504271538879234762019489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94005695385172313016025985 70504271538879234762019489)
  ·
    refine ⟨52878203654159426071514617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70504271538879234762019489 52878203654159426071514617)
    ·
      refine ⟨39658652740619569553635963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52878203654159426071514617 39658652740619569553635963)
      ·
        refine ⟨59487979110929354330453945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39658652740619569553635963 59487979110929354330453945)
        ·
          refine ⟨44615984333197015747840459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59487979110929354330453945 44615984333197015747840459)
          ·
            refine ⟨66923976499795523621760689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44615984333197015747840459 66923976499795523621760689)
            ·
              refine ⟨50192982374846642716320517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66923976499795523621760689 50192982374846642716320517)
              ·
                refine ⟨9411184195283745509310097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50192982374846642716320517 9411184195283745509310097)
                ·
                  refine ⟨7058388146462809131982573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9411184195283745509310097 7058388146462809131982573)
                  ·
                    refine ⟨2646895554923553424493465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7058388146462809131982573 2646895554923553424493465)
                    ·
                      refine ⟨1985171666192665068370099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2646895554923553424493465 1985171666192665068370099)
                      ·
                        rfl

theorem cell23_3866108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 2, 3, 2].length) (baseStart_3866108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866108 prefixEnd_3866108 := by exact prefixLift 3866108
  have htrace : WordTrace (prefixWord ++ tailWord_3866108) baseStart_3866108 baseEnd_3866108 := by
    simpa [prefixWord, tailWord_3866108, baseEnd_3866108] using wordTrace_append hprefix tailTrace_3866108
  have hstable : (prefixWord ++ tailWord_3866108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866108).length < 2 ^ (prefixWord ++ tailWord_3866108).sum := by decide
  have hdescent : baseEnd_3866108 < baseStart_3866108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866131 : List Nat := [1, 1, 1, 2, 1, 6, 3, 1, 1, 6]
def baseStart_3866131 : Nat := 118140960795 + 3866131 * 2 ^ 59
def prefixEnd_3866131 : Nat := 4983230072969 + 3 ^ 40 * 3866131 * 2
def baseEnd_3866131 : Nat := 661727825415906159460831

theorem tailTrace_3866131 : CollatzResearch.WordTrace tailWord_3866131 prefixEnd_3866131 661727825415906159460831 := by
  unfold tailWord_3866131
  simp only [CollatzResearch.WordTrace]
  refine ⟨141009381956675144452126247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94006254637783429634750831 141009381956675144452126247)
  ·
    refine ⟨211514072935012716678189371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141009381956675144452126247 211514072935012716678189371)
    ·
      refine ⟨317271109402519075017284057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211514072935012716678189371 317271109402519075017284057)
      ·
        refine ⟨237953332051889306262963043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317271109402519075017284057 237953332051889306262963043)
        ·
          refine ⟨356929998077833959394444565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237953332051889306262963043 356929998077833959394444565)
          ·
            refine ⟨16731093659898466846614589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 356929998077833959394444565 16731093659898466846614589)
            ·
              refine ⟨6274160122461925067480471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16731093659898466846614589 6274160122461925067480471)
              ·
                refine ⟨9411240183692887601220707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6274160122461925067480471 9411240183692887601220707)
                ·
                  refine ⟨14116860275539331401831061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9411240183692887601220707 14116860275539331401831061)
                  ·
                    refine ⟨661727825415906159460831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14116860275539331401831061 661727825415906159460831)
                    ·
                      rfl

theorem cell23_3866131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 6].length) (baseStart_3866131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866131 prefixEnd_3866131 := by exact prefixLift 3866131
  have htrace : WordTrace (prefixWord ++ tailWord_3866131) baseStart_3866131 baseEnd_3866131 := by
    simpa [prefixWord, tailWord_3866131, baseEnd_3866131] using wordTrace_append hprefix tailTrace_3866131
  have hstable : (prefixWord ++ tailWord_3866131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866131).length < 2 ^ (prefixWord ++ tailWord_3866131).sum := by decide
  have hdescent : baseEnd_3866131 < baseStart_3866131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866141 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_3866141 : Nat := 118140960795 + 3866141 * 2 ^ 59
def prefixEnd_3866141 : Nat := 4983230072969 + 3 ^ 40 * 3866141 * 2
def baseEnd_3866141 : Nat := 1985188611054263439257447

theorem tailTrace_3866141 : CollatzResearch.WordTrace tailWord_3866141 prefixEnd_3866141 1985188611054263439257447 := by
  unfold tailWord_3866141
  simp only [CollatzResearch.WordTrace]
  refine ⟨141009746686638916159990277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94006497791092610773326851 141009746686638916159990277)
  ·
    refine ⟨26439327503744796779998177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141009746686638916159990277 26439327503744796779998177)
    ·
      refine ⟨19829495627808597584998633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26439327503744796779998177 19829495627808597584998633)
      ·
        refine ⟨14872121720856448188748975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19829495627808597584998633 14872121720856448188748975)
        ·
          refine ⟨22308182581284672283123463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14872121720856448188748975 22308182581284672283123463)
          ·
            refine ⟨33462273871927008424685195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22308182581284672283123463 33462273871927008424685195)
            ·
              refine ⟨50193410807890512637027793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33462273871927008424685195 50193410807890512637027793)
              ·
                refine ⟨37645058105917884477770845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50193410807890512637027793 37645058105917884477770845)
                ·
                  refine ⟨14116896789719206679164067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37645058105917884477770845 14116896789719206679164067)
                  ·
                    refine ⟨21175345184578810018746101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14116896789719206679164067 21175345184578810018746101)
                    ·
                      refine ⟨1985188611054263439257447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21175345184578810018746101 1985188611054263439257447)
                      ·
                        rfl

theorem cell23_3866141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_3866141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866141 prefixEnd_3866141 := by exact prefixLift 3866141
  have htrace : WordTrace (prefixWord ++ tailWord_3866141) baseStart_3866141 baseEnd_3866141 := by
    simpa [prefixWord, tailWord_3866141, baseEnd_3866141] using wordTrace_append hprefix tailTrace_3866141
  have hstable : (prefixWord ++ tailWord_3866141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866141).length < 2 ^ (prefixWord ++ tailWord_3866141).sum := by decide
  have hdescent : baseEnd_3866141 < baseStart_3866141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866158 : List Nat := [4, 1, 3, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_3866158 : Nat := 118140960795 + 3866158 * 2 ^ 59
def prefixEnd_3866158 : Nat := 4983230072969 + 3 ^ 40 * 3866158 * 2
def baseEnd_3866158 : Nat := 1985197340225389872744869

theorem tailTrace_3866158 : CollatzResearch.WordTrace tailWord_3866158 prefixEnd_3866158 1985197340225389872744869 := by
  unfold tailWord_3866158
  simp only [CollatzResearch.WordTrace]
  refine ⟨17626295840947166007919891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94006911151718218708906085 17626295840947166007919891)
  ·
    refine ⟨26439443761420749011879837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17626295840947166007919891 26439443761420749011879837)
    ·
      refine ⟨9914791410532780879454939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26439443761420749011879837 9914791410532780879454939)
      ·
        refine ⟨14872187115799171319182409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9914791410532780879454939 14872187115799171319182409)
        ·
          refine ⟨11154140336849378489386807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14872187115799171319182409 11154140336849378489386807)
          ·
            refine ⟨16731210505274067734080211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11154140336849378489386807 16731210505274067734080211)
            ·
              refine ⟨25096815757911101601120317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16731210505274067734080211 25096815757911101601120317)
              ·
                refine ⟨9411305909216663100420119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25096815757911101601120317 9411305909216663100420119)
                ·
                  refine ⟨14116958863824994650630179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9411305909216663100420119 14116958863824994650630179)
                  ·
                    refine ⟨21175438295737491975945269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14116958863824994650630179 21175438295737491975945269)
                    ·
                      refine ⟨1985197340225389872744869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21175438295737491975945269 1985197340225389872744869)
                      ·
                        rfl

theorem cell23_3866158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_3866158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866158 prefixEnd_3866158 := by exact prefixLift 3866158
  have htrace : WordTrace (prefixWord ++ tailWord_3866158) baseStart_3866158 baseEnd_3866158 := by
    simpa [prefixWord, tailWord_3866158, baseEnd_3866158] using wordTrace_append hprefix tailTrace_3866158
  have hstable : (prefixWord ++ tailWord_3866158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866158).length < 2 ^ (prefixWord ++ tailWord_3866158).sum := by decide
  have hdescent : baseEnd_3866158 < baseStart_3866158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866166 : List Nat := [5, 1, 2, 1, 3, 1, 3, 2, 1, 1, 3]
def baseStart_3866166 : Nat := 118140960795 + 3866166 * 2 ^ 59
def prefixEnd_3866166 : Nat := 4983230072969 + 3 ^ 40 * 3866166 * 2
def baseEnd_3866166 : Nat := 1985201448070625841444833

theorem tailTrace_3866166 : CollatzResearch.WordTrace tailWord_3866166 prefixEnd_3866166 1985201448070625841444833 := by
  unfold tailWord_3866166
  simp only [CollatzResearch.WordTrace]
  refine ⟨8813166156971771589353147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94007105674365563619766901 8813166156971771589353147)
  ·
    refine ⟨13219749235457657384029721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8813166156971771589353147 13219749235457657384029721)
    ·
      refine ⟨9914811926593243038022291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13219749235457657384029721 9914811926593243038022291)
      ·
        refine ⟨14872217889889864557033437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9914811926593243038022291 14872217889889864557033437)
        ·
          refine ⟨5577081708708699208887539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14872217889889864557033437 5577081708708699208887539)
          ·
            refine ⟨8365622563063048813331309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5577081708708699208887539 8365622563063048813331309)
            ·
              refine ⟨3137108461148643304999241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8365622563063048813331309 3137108461148643304999241)
              ·
                refine ⟨2352831345861482478749431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3137108461148643304999241 2352831345861482478749431)
                ·
                  refine ⟨3529247018792223718124147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2352831345861482478749431 3529247018792223718124147)
                  ·
                    refine ⟨5293870528188335577186221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3529247018792223718124147 5293870528188335577186221)
                    ·
                      refine ⟨1985201448070625841444833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5293870528188335577186221 1985201448070625841444833)
                      ·
                        rfl

theorem cell23_3866166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_3866166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866166 prefixEnd_3866166 := by exact prefixLift 3866166
  have htrace : WordTrace (prefixWord ++ tailWord_3866166) baseStart_3866166 baseEnd_3866166 := by
    simpa [prefixWord, tailWord_3866166, baseEnd_3866166] using wordTrace_append hprefix tailTrace_3866166
  have hstable : (prefixWord ++ tailWord_3866166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866166).length < 2 ^ (prefixWord ++ tailWord_3866166).sum := by decide
  have hdescent : baseEnd_3866166 < baseStart_3866166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866189 : List Nat := [1, 6, 1, 1, 4, 1, 1, 2, 1, 1, 4]
def baseStart_3866189 : Nat := 118140960795 + 3866189 * 2 ^ 59
def prefixEnd_3866189 : Nat := 4983230072969 + 3 ^ 40 * 3866189 * 2
def baseEnd_3866189 : Nat := 1985213258125679251457227

theorem tailTrace_3866189 : CollatzResearch.WordTrace tailWord_3866189 prefixEnd_3866189 1985213258125679251457227 := by
  unfold tailWord_3866189
  simp only [CollatzResearch.WordTrace]
  refine ⟨141011497390465020357737621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94007664926976680238491747 141011497390465020357737621)
  ·
    refine ⟨6609913940178047829268951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 141011497390465020357737621 6609913940178047829268951)
    ·
      refine ⟨9914870910267071743903427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6609913940178047829268951 9914870910267071743903427)
      ·
        refine ⟨14872306365400607615855141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9914870910267071743903427 14872306365400607615855141)
        ·
          refine ⟨2788557443512613927972839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14872306365400607615855141 2788557443512613927972839)
          ·
            refine ⟨4182836165268920891959259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2788557443512613927972839 4182836165268920891959259)
            ·
              refine ⟨6274254247903381337938889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4182836165268920891959259 6274254247903381337938889)
              ·
                refine ⟨4705690685927536003454167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6274254247903381337938889 4705690685927536003454167)
                ·
                  refine ⟨7058536028891304005181251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4705690685927536003454167 7058536028891304005181251)
                  ·
                    refine ⟨10587804043336956007771877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7058536028891304005181251 10587804043336956007771877)
                    ·
                      refine ⟨1985213258125679251457227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10587804043336956007771877 1985213258125679251457227)
                      ·
                        rfl

theorem cell23_3866189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_3866189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866189 prefixEnd_3866189 := by exact prefixLift 3866189
  have htrace : WordTrace (prefixWord ++ tailWord_3866189) baseStart_3866189 baseEnd_3866189 := by
    simpa [prefixWord, tailWord_3866189, baseEnd_3866189] using wordTrace_append hprefix tailTrace_3866189
  have hstable : (prefixWord ++ tailWord_3866189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866189).length < 2 ^ (prefixWord ++ tailWord_3866189).sum := by decide
  have hdescent : baseEnd_3866189 < baseStart_3866189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866215 : List Nat := [1, 1, 5, 1, 1, 1, 2, 5, 1, 3, 2]
def baseStart_3866215 : Nat := 118140960795 + 3866215 * 2 ^ 59
def prefixEnd_3866215 : Nat := 4983230072969 + 3 ^ 40 * 3866215 * 2
def baseEnd_3866215 : Nat := 1985226608622696149732107

theorem tailTrace_3866215 : CollatzResearch.WordTrace tailWord_3866215 prefixEnd_3866215 1985226608622696149732107 := by
  unfold tailWord_3866215
  simp only [CollatzResearch.WordTrace]
  refine ⟨141012445688370826798184099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94008297125580551198789399 141012445688370826798184099)
  ·
    refine ⟨211518668532556240197276149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141012445688370826798184099 211518668532556240197276149)
    ·
      refine ⟨19829875174927147518494639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211518668532556240197276149 19829875174927147518494639)
      ·
        refine ⟨29744812762390721277741959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19829875174927147518494639 29744812762390721277741959)
        ·
          refine ⟨44617219143586081916612939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29744812762390721277741959 44617219143586081916612939)
          ·
            refine ⟨66925828715379122874919409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44617219143586081916612939 66925828715379122874919409)
            ·
              refine ⟨50194371536534342156189557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66925828715379122874919409 50194371536534342156189557)
              ·
                refine ⟨4705722331550094577142771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50194371536534342156189557 4705722331550094577142771)
                ·
                  refine ⟨7058583497325141865714157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4705722331550094577142771 7058583497325141865714157)
                  ·
                    refine ⟨2646968811496928199642809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7058583497325141865714157 2646968811496928199642809)
                    ·
                      refine ⟨1985226608622696149732107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2646968811496928199642809 1985226608622696149732107)
                      ·
                        rfl

theorem cell23_3866215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_3866215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866215 prefixEnd_3866215 := by exact prefixLift 3866215
  have htrace : WordTrace (prefixWord ++ tailWord_3866215) baseStart_3866215 baseEnd_3866215 := by
    simpa [prefixWord, tailWord_3866215, baseEnd_3866215] using wordTrace_append hprefix tailTrace_3866215
  have hstable : (prefixWord ++ tailWord_3866215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866215).length < 2 ^ (prefixWord ++ tailWord_3866215).sum := by decide
  have hdescent : baseEnd_3866215 < baseStart_3866215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866245 : List Nat := [1, 3, 1, 1, 4, 1, 4, 1, 1, 4, 2]
def baseStart_3866245 : Nat := 118140960795 + 3866245 * 2 ^ 59
def prefixEnd_3866245 : Nat := 4983230072969 + 3 ^ 40 * 3866245 * 2
def baseEnd_3866245 : Nat := 1985242013042331032356969

theorem tailTrace_3866245 : CollatzResearch.WordTrace tailWord_3866245 prefixEnd_3866245 1985242013042331032356969 := by
  unfold tailWord_3866245
  simp only [CollatzResearch.WordTrace]
  refine ⟨141013539878262141921776189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94009026585508094614517459 141013539878262141921776189)
  ·
    refine ⟨52880077454348303220666071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141013539878262141921776189 52880077454348303220666071)
    ·
      refine ⟨79320116181522454830999107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52880077454348303220666071 79320116181522454830999107)
      ·
        refine ⟨118980174272283682246498661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79320116181522454830999107 118980174272283682246498661)
        ·
          refine ⟨22308782676053190421218499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118980174272283682246498661 22308782676053190421218499)
          ·
            refine ⟨33463174014079785631827749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22308782676053190421218499 33463174014079785631827749)
            ·
              refine ⟨6274345127639959805967703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33463174014079785631827749 6274345127639959805967703)
              ·
                refine ⟨9411517691459939708951555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6274345127639959805967703 9411517691459939708951555)
                ·
                  refine ⟨14117276537189909563427333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9411517691459939708951555 14117276537189909563427333)
                  ·
                    refine ⟨2646989350723108043142625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14117276537189909563427333 2646989350723108043142625)
                    ·
                      refine ⟨1985242013042331032356969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2646989350723108043142625 1985242013042331032356969)
                      ·
                        rfl

theorem cell23_3866245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 4, 2].length) (baseStart_3866245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866245 prefixEnd_3866245 := by exact prefixLift 3866245
  have htrace : WordTrace (prefixWord ++ tailWord_3866245) baseStart_3866245 baseEnd_3866245 := by
    simpa [prefixWord, tailWord_3866245, baseEnd_3866245] using wordTrace_append hprefix tailTrace_3866245
  have hstable : (prefixWord ++ tailWord_3866245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866245).length < 2 ^ (prefixWord ++ tailWord_3866245).sum := by decide
  have hdescent : baseEnd_3866245 < baseStart_3866245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866251 : List Nat := [1, 1, 1, 1, 4, 1, 5, 2, 7]
def baseStart_3866251 : Nat := 118140960795 + 3866251 * 2 ^ 59
def prefixEnd_3866251 : Nat := 4983230072969 + 3 ^ 40 * 3866251 * 2
def baseEnd_3866251 : Nat := 220582788214028667653549

theorem tailTrace_3866251 : CollatzResearch.WordTrace tailWord_3866251 prefixEnd_3866251 220582788214028667653549 := by
  unfold tailWord_3866251
  simp only [CollatzResearch.WordTrace]
  refine ⟨141013758716240404946494607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94009172477493603297663071 141013758716240404946494607)
  ·
    refine ⟨211520638074360607419741911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141013758716240404946494607 211520638074360607419741911)
    ·
      refine ⟨317280957111540911129612867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211520638074360607419741911 317280957111540911129612867)
      ·
        refine ⟨475921435667311366694419301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317280957111540911129612867 475921435667311366694419301)
        ·
          refine ⟨89235269187620881255203619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 475921435667311366694419301 89235269187620881255203619)
          ·
            refine ⟨133852903781431321882805429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89235269187620881255203619 133852903781431321882805429)
            ·
              refine ⟨12548709729509186426513009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133852903781431321882805429 12548709729509186426513009)
              ·
                refine ⟨9411532297131889819884757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12548709729509186426513009 9411532297131889819884757)
                ·
                  refine ⟨220582788214028667653549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9411532297131889819884757 220582788214028667653549)
                  ·
                    rfl

theorem cell23_3866251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 7].length) (baseStart_3866251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866251 prefixEnd_3866251 := by exact prefixLift 3866251
  have htrace : WordTrace (prefixWord ++ tailWord_3866251) baseStart_3866251 baseEnd_3866251 := by
    simpa [prefixWord, tailWord_3866251, baseEnd_3866251] using wordTrace_append hprefix tailTrace_3866251
  have hstable : (prefixWord ++ tailWord_3866251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866251).length < 2 ^ (prefixWord ++ tailWord_3866251).sum := by decide
  have hdescent : baseEnd_3866251 < baseStart_3866251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866285 : List Nat := [1, 5, 2, 1, 1, 1, 1, 6, 5]
def baseStart_3866285 : Nat := 118140960795 + 3866285 * 2 ^ 59
def prefixEnd_3866285 : Nat := 4983230072969 + 3 ^ 40 * 3866285 * 2
def baseEnd_3866285 : Nat := 220584728029834541761865

theorem tailTrace_3866285 : CollatzResearch.WordTrace tailWord_3866285 prefixEnd_3866285 220584728029834541761865 := by
  unfold tailWord_3866285
  simp only [CollatzResearch.WordTrace]
  refine ⟨141014998798117228753232309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94009999198744819168821539 141014998798117228753232309)
  ·
    refine ⟨13220156137323490195615529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141014998798117228753232309 13220156137323490195615529)
    ·
      refine ⟨9915117102992617646711647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13220156137323490195615529 9915117102992617646711647)
      ·
        refine ⟨14872675654488926470067471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9915117102992617646711647 14872675654488926470067471)
        ·
          refine ⟨22309013481733389705101207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14872675654488926470067471 22309013481733389705101207)
          ·
            refine ⟨33463520222600084557651811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22309013481733389705101207 33463520222600084557651811)
            ·
              refine ⟨50195280333900126836477717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33463520222600084557651811 50195280333900126836477717)
              ·
                refine ⟨2352903765651568445459893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50195280333900126836477717 2352903765651568445459893)
                ·
                  refine ⟨220584728029834541761865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2352903765651568445459893 220584728029834541761865)
                  ·
                    rfl

theorem cell23_3866285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_3866285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866285 prefixEnd_3866285 := by exact prefixLift 3866285
  have htrace : WordTrace (prefixWord ++ tailWord_3866285) baseStart_3866285 baseEnd_3866285 := by
    simpa [prefixWord, tailWord_3866285, baseEnd_3866285] using wordTrace_append hprefix tailTrace_3866285
  have hstable : (prefixWord ++ tailWord_3866285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866285).length < 2 ^ (prefixWord ++ tailWord_3866285).sum := by decide
  have hdescent : baseEnd_3866285 < baseStart_3866285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866288 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 1, 7, 2]
def baseStart_3866288 : Nat := 118140960795 + 3866288 * 2 ^ 59
def prefixEnd_3866288 : Nat := 4983230072969 + 3 ^ 40 * 3866288 * 2
def baseEnd_3866288 : Nat := 1985264092710474364119271

theorem tailTrace_3866288 : CollatzResearch.WordTrace tailWord_3866288 prefixEnd_3866288 1985264092710474364119271 := by
  unfold tailWord_3866288
  simp only [CollatzResearch.WordTrace]
  refine ⟨70507554108553180132795759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94010072144737573510394345 70507554108553180132795759)
  ·
    refine ⟨105761331162829770199193639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70507554108553180132795759 105761331162829770199193639)
    ·
      refine ⟨158641996744244655298790459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105761331162829770199193639 158641996744244655298790459)
      ·
        refine ⟨237962995116366982948185689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158641996744244655298790459 237962995116366982948185689)
        ·
          refine ⟨178472246337275237211139267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237962995116366982948185689 178472246337275237211139267)
          ·
            refine ⟨267708369505912855816708901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178472246337275237211139267 267708369505912855816708901)
            ·
              refine ⟨50195319282358660465632919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 267708369505912855816708901 50195319282358660465632919)
              ·
                refine ⟨75292978923537990698449379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50195319282358660465632919 75292978923537990698449379)
                ·
                  refine ⟨112939468385306986047674069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75292978923537990698449379 112939468385306986047674069)
                  ·
                    refine ⟨2647018790280632485492361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 112939468385306986047674069 2647018790280632485492361)
                    ·
                      refine ⟨1985264092710474364119271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2647018790280632485492361 1985264092710474364119271)
                      ·
                        rfl

theorem cell23_3866288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 7, 2].length) (baseStart_3866288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866288 prefixEnd_3866288 := by exact prefixLift 3866288
  have htrace : WordTrace (prefixWord ++ tailWord_3866288) baseStart_3866288 baseEnd_3866288 := by
    simpa [prefixWord, tailWord_3866288, baseEnd_3866288] using wordTrace_append hprefix tailTrace_3866288
  have hstable : (prefixWord ++ tailWord_3866288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866288).length < 2 ^ (prefixWord ++ tailWord_3866288).sum := by decide
  have hdescent : baseEnd_3866288 < baseStart_3866288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866291 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 7]
def baseStart_3866291 : Nat := 118140960795 + 3866291 * 2 ^ 59
def prefixEnd_3866291 : Nat := 4983230072969 + 3 ^ 40 * 3866291 * 2
def baseEnd_3866291 : Nat := 1985265633152437852381757

theorem tailTrace_3866291 : CollatzResearch.WordTrace tailWord_3866291 prefixEnd_3866291 1985265633152437852381757 := by
  unfold tailWord_3866291
  simp only [CollatzResearch.WordTrace]
  refine ⟨141015217636095491777950727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94010145090730327851967151 141015217636095491777950727)
  ·
    refine ⟨211522826454143237666926091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141015217636095491777950727 211522826454143237666926091)
    ·
      refine ⟨317284239681214856500389137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211522826454143237666926091 317284239681214856500389137)
      ·
        refine ⟨237963179760911142375291853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317284239681214856500389137 237963179760911142375291853)
        ·
          refine ⟨89236192410341678390734445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237963179760911142375291853 89236192410341678390734445)
          ·
            refine ⟨33463572153878129396525417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89236192410341678390734445 33463572153878129396525417)
            ·
              refine ⟨25097679115408597047394063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33463572153878129396525417 25097679115408597047394063)
              ·
                refine ⟨37646518673112895571091095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25097679115408597047394063 37646518673112895571091095)
                ·
                  refine ⟨56469778009669343356636643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37646518673112895571091095 56469778009669343356636643)
                  ·
                    refine ⟨84704667014504015034954965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56469778009669343356636643 84704667014504015034954965)
                    ·
                      refine ⟨1985265633152437852381757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84704667014504015034954965 1985265633152437852381757)
                      ·
                        rfl

theorem cell23_3866291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_3866291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866291 prefixEnd_3866291 := by exact prefixLift 3866291
  have htrace : WordTrace (prefixWord ++ tailWord_3866291) baseStart_3866291 baseEnd_3866291 := by
    simpa [prefixWord, tailWord_3866291, baseEnd_3866291] using wordTrace_append hprefix tailTrace_3866291
  have hstable : (prefixWord ++ tailWord_3866291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866291).length < 2 ^ (prefixWord ++ tailWord_3866291).sum := by decide
  have hdescent : baseEnd_3866291 < baseStart_3866291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866311 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 2, 8]
def baseStart_3866311 : Nat := 118140960795 + 3866311 * 2 ^ 59
def prefixEnd_3866311 : Nat := 4983230072969 + 3 ^ 40 * 3866311 * 2
def baseEnd_3866311 : Nat := 661758634255175924710555

theorem tailTrace_3866311 : CollatzResearch.WordTrace tailWord_3866311 prefixEnd_3866311 661758634255175924710555 := by
  unfold tailWord_3866311
  simp only [CollatzResearch.WordTrace]
  refine ⟨141015947096023035193678787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94010631397348690129119191 141015947096023035193678787)
  ·
    refine ⟨211523920644034552790518181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141015947096023035193678787 211523920644034552790518181)
    ·
      refine ⟨39660735120756478648222159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211523920644034552790518181 39660735120756478648222159)
      ·
        refine ⟨59491102681134717972333239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39660735120756478648222159 59491102681134717972333239)
        ·
          refine ⟨89236654021702076958499859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59491102681134717972333239 89236654021702076958499859)
          ·
            refine ⟨133854981032553115437749789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89236654021702076958499859 133854981032553115437749789)
            ·
              refine ⟨50195617887207418289156171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133854981032553115437749789 50195617887207418289156171)
              ·
                refine ⟨75293426830811127433734257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50195617887207418289156171 75293426830811127433734257)
                ·
                  refine ⟨56470070123108345575300693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75293426830811127433734257 56470070123108345575300693)
                  ·
                    refine ⟨661758634255175924710555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56470070123108345575300693 661758634255175924710555)
                    ·
                      rfl

theorem cell23_3866311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_3866311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866311 prefixEnd_3866311 := by exact prefixLift 3866311
  have htrace : WordTrace (prefixWord ++ tailWord_3866311) baseStart_3866311 baseEnd_3866311 := by
    simpa [prefixWord, tailWord_3866311, baseEnd_3866311] using wordTrace_append hprefix tailTrace_3866311
  have hstable : (prefixWord ++ tailWord_3866311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866311).length < 2 ^ (prefixWord ++ tailWord_3866311).sum := by decide
  have hdescent : baseEnd_3866311 < baseStart_3866311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866318 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4]
def baseStart_3866318 : Nat := 118140960795 + 3866318 * 2 ^ 59
def prefixEnd_3866318 : Nat := 4983230072969 + 3 ^ 40 * 3866318 * 2
def baseEnd_3866318 : Nat := 1985279497130109246744133

theorem tailTrace_3866318 : CollatzResearch.WordTrace tailWord_3866318 prefixEnd_3866318 1985279497130109246744133 := by
  unfold tailWord_3866318
  simp only [CollatzResearch.WordTrace]
  refine ⟨17627025300874709423647951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94010801604665116926122405 17627025300874709423647951)
  ·
    refine ⟨26440537951312064135471927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17627025300874709423647951 26440537951312064135471927)
    ·
      refine ⟨39660806926968096203207891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26440537951312064135471927 39660806926968096203207891)
      ·
        refine ⟨59491210390452144304811837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39660806926968096203207891 59491210390452144304811837)
        ·
          refine ⟨22309203896419554114304439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59491210390452144304811837 22309203896419554114304439)
          ·
            refine ⟨33463805844629331171456659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22309203896419554114304439 33463805844629331171456659)
            ·
              refine ⟨50195708766943996757184989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33463805844629331171456659 50195708766943996757184989)
              ·
                refine ⟨18823390787603998783944371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50195708766943996757184989 18823390787603998783944371)
                ·
                  refine ⟨28235086181405998175916557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18823390787603998783944371 28235086181405998175916557)
                  ·
                    refine ⟨10588157318027249315968709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28235086181405998175916557 10588157318027249315968709)
                    ·
                      refine ⟨1985279497130109246744133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10588157318027249315968709 1985279497130109246744133)
                      ·
                        rfl

theorem cell23_3866318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_3866318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866318 prefixEnd_3866318 := by exact prefixLift 3866318
  have htrace : WordTrace (prefixWord ++ tailWord_3866318) baseStart_3866318 baseEnd_3866318 := by
    simpa [prefixWord, tailWord_3866318, baseEnd_3866318] using wordTrace_append hprefix tailTrace_3866318
  have hstable : (prefixWord ++ tailWord_3866318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866318).length < 2 ^ (prefixWord ++ tailWord_3866318).sum := by decide
  have hdescent : baseEnd_3866318 < baseStart_3866318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866332 : List Nat := [2, 2, 5, 1, 2, 1, 1, 2, 2, 5]
def baseStart_3866332 : Nat := 118140960795 + 3866332 * 2 ^ 59
def prefixEnd_3866332 : Nat := 4983230072969 + 3 ^ 40 * 3866332 * 2
def baseEnd_3866332 : Nat := 661762228619757397323023

theorem tailTrace_3866332 : CollatzResearch.WordTrace tailWord_3866332 prefixEnd_3866332 661762228619757397323023 := by
  unfold tailWord_3866332
  simp only [CollatzResearch.WordTrace]
  refine ⟨70508356514473477890096625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94011142019297970520128833 70508356514473477890096625)
  ·
    refine ⟨52881267385855108417572469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70508356514473477890096625 52881267385855108417572469)
    ·
      refine ⟨4957618817423916414147419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52881267385855108417572469 4957618817423916414147419)
      ·
        refine ⟨7436428226135874621221129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4957618817423916414147419 7436428226135874621221129)
        ·
          refine ⟨5577321169601905965915847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7436428226135874621221129 5577321169601905965915847)
          ·
            refine ⟨8365981754402858948873771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5577321169601905965915847 8365981754402858948873771)
            ·
              refine ⟨12548972631604288423310657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8365981754402858948873771 12548972631604288423310657)
              ·
                refine ⟨9411729473703216317482993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12548972631604288423310657 9411729473703216317482993)
                ·
                  refine ⟨7058797105277412238112245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9411729473703216317482993 7058797105277412238112245)
                  ·
                    refine ⟨661762228619757397323023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7058797105277412238112245 661762228619757397323023)
                    ·
                      rfl

theorem cell23_3866332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_3866332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866332 prefixEnd_3866332 := by exact prefixLift 3866332
  have htrace : WordTrace (prefixWord ++ tailWord_3866332) baseStart_3866332 baseEnd_3866332 := by
    simpa [prefixWord, tailWord_3866332, baseEnd_3866332] using wordTrace_append hprefix tailTrace_3866332
  have hstable : (prefixWord ++ tailWord_3866332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866332).length < 2 ^ (prefixWord ++ tailWord_3866332).sum := by decide
  have hdescent : baseEnd_3866332 < baseStart_3866332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866372 : List Nat := [2, 3, 2, 2, 1, 3, 2, 1, 2, 2, 3]
def baseStart_3866372 : Nat := 118140960795 + 3866372 * 2 ^ 59
def prefixEnd_3866372 : Nat := 4983230072969 + 3 ^ 40 * 3866372 * 2
def baseEnd_3866372 : Nat := 1985307225085452035468885

theorem tailTrace_3866372 : CollatzResearch.WordTrace tailWord_3866372 prefixEnd_3866372 1985307225085452035468885 := by
  unfold tailWord_3866372
  simp only [CollatzResearch.WordTrace]
  refine ⟨70509085974401021305824685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94012114632534695074432913 70509085974401021305824685)
  ·
    refine ⟨26440907240400382989684257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70509085974401021305824685 26440907240400382989684257)
    ·
      refine ⟨19830680430300287242263193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26440907240400382989684257 19830680430300287242263193)
      ·
        refine ⟨14873010322725215431697395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19830680430300287242263193 14873010322725215431697395)
        ·
          refine ⟨22309515484087823147546093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14873010322725215431697395 22309515484087823147546093)
          ·
            refine ⟨8366068306532933680329785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22309515484087823147546093 8366068306532933680329785)
            ·
              refine ⟨6274551229899700260247339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8366068306532933680329785 6274551229899700260247339)
              ·
                refine ⟨9411826844849550390371009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6274551229899700260247339 9411826844849550390371009)
                ·
                  refine ⟨7058870133637162792778257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9411826844849550390371009 7058870133637162792778257)
                  ·
                    refine ⟨5294152600227872094583693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7058870133637162792778257 5294152600227872094583693)
                    ·
                      refine ⟨1985307225085452035468885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5294152600227872094583693 1985307225085452035468885)
                      ·
                        rfl

theorem cell23_3866372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_3866372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866372 prefixEnd_3866372 := by exact prefixLift 3866372
  have htrace : WordTrace (prefixWord ++ tailWord_3866372) baseStart_3866372 baseEnd_3866372 := by
    simpa [prefixWord, tailWord_3866372, baseEnd_3866372] using wordTrace_append hprefix tailTrace_3866372
  have hstable : (prefixWord ++ tailWord_3866372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866372).length < 2 ^ (prefixWord ++ tailWord_3866372).sum := by decide
  have hdescent : baseEnd_3866372 < baseStart_3866372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866402 : List Nat := [3, 3, 1, 1, 2, 1, 2, 3, 3, 1, 3]
def baseStart_3866402 : Nat := 118140960795 + 3866402 * 2 ^ 59
def prefixEnd_3866402 : Nat := 4983230072969 + 3 ^ 40 * 3866402 * 2
def baseEnd_3866402 : Nat := 1985322629505086918093747

theorem tailTrace_3866402 : CollatzResearch.WordTrace tailWord_3866402 prefixEnd_3866402 1985322629505086918093747 := by
  unfold tailWord_3866402
  simp only [CollatzResearch.WordTrace]
  refine ⟨35254816534673339433810365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94012844092462238490160973 35254816534673339433810365)
  ·
    refine ⟨13220556200502502287678887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35254816534673339433810365 13220556200502502287678887)
    ·
      refine ⟨19830834300753753431518331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13220556200502502287678887 19830834300753753431518331)
      ·
        refine ⟨29746251451130630147277497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19830834300753753431518331 29746251451130630147277497)
        ·
          refine ⟨22309688588347972610458123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29746251451130630147277497 22309688588347972610458123)
          ·
            refine ⟨33464532882521958915687185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22309688588347972610458123 33464532882521958915687185)
            ·
              refine ⟨25098399661891469186765389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33464532882521958915687185 25098399661891469186765389)
              ·
                refine ⟨9411899873209300945037021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25098399661891469186765389 9411899873209300945037021)
                ·
                  refine ⟨3529462452453487854388883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9411899873209300945037021 3529462452453487854388883)
                  ·
                    refine ⟨5294193678680231781583325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3529462452453487854388883 5294193678680231781583325)
                    ·
                      refine ⟨1985322629505086918093747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5294193678680231781583325 1985322629505086918093747)
                      ·
                        rfl

theorem cell23_3866402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_3866402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866402 prefixEnd_3866402 := by exact prefixLift 3866402
  have htrace : WordTrace (prefixWord ++ tailWord_3866402) baseStart_3866402 baseEnd_3866402 := by
    simpa [prefixWord, tailWord_3866402, baseEnd_3866402] using wordTrace_append hprefix tailTrace_3866402
  have hstable : (prefixWord ++ tailWord_3866402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866402).length < 2 ^ (prefixWord ++ tailWord_3866402).sum := by decide
  have hdescent : baseEnd_3866402 < baseStart_3866402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866422 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 3, 5]
def baseStart_3866422 : Nat := 118140960795 + 3866422 * 2 ^ 59
def prefixEnd_3866422 : Nat := 4983230072969 + 3 ^ 40 * 3866422 * 2
def baseEnd_3866422 : Nat := 661777633039392279947885

theorem tailTrace_3866422 : CollatzResearch.WordTrace tailWord_3866422 prefixEnd_3866422 661777633039392279947885 := by
  unfold tailWord_3866422
  simp only [CollatzResearch.WordTrace]
  refine ⟨8813749724913806321935595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94013330399080600767313013 8813749724913806321935595)
  ·
    refine ⟨13220624587370709482903393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8813749724913806321935595 13220624587370709482903393)
    ·
      refine ⟨9915468440528032112177545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13220624587370709482903393 9915468440528032112177545)
      ·
        refine ⟨7436601330396024084133159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9915468440528032112177545 7436601330396024084133159)
        ·
          refine ⟨11154901995594036126199739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7436601330396024084133159 11154901995594036126199739)
          ·
            refine ⟨16732352993391054189299609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11154901995594036126199739 16732352993391054189299609)
            ·
              refine ⟨12549264745043290641974707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16732352993391054189299609 12549264745043290641974707)
              ·
                refine ⟨18823897117564935962962061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12549264745043290641974707 18823897117564935962962061)
                ·
                  refine ⟨7058961419086850986110773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18823897117564935962962061 7058961419086850986110773)
                  ·
                    refine ⟨661777633039392279947885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7058961419086850986110773 661777633039392279947885)
                    ·
                      rfl

theorem cell23_3866422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_3866422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866422 prefixEnd_3866422 := by exact prefixLift 3866422
  have htrace : WordTrace (prefixWord ++ tailWord_3866422) baseStart_3866422 baseEnd_3866422 := by
    simpa [prefixWord, tailWord_3866422, baseEnd_3866422] using wordTrace_append hprefix tailTrace_3866422
  have hstable : (prefixWord ++ tailWord_3866422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866422).length < 2 ^ (prefixWord ++ tailWord_3866422).sum := by decide
  have hdescent : baseEnd_3866422 < baseStart_3866422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866429 : List Nat := [1, 4, 1, 4, 1, 1, 3, 1, 2, 3, 2]
def baseStart_3866429 : Nat := 118140960795 + 3866429 * 2 ^ 59
def prefixEnd_3866429 : Nat := 4983230072969 + 3 ^ 40 * 3866429 * 2
def baseEnd_3866429 : Nat := 1985336493482758312456123

theorem tailTrace_3866429 : CollatzResearch.WordTrace tailWord_3866429 prefixEnd_3866429 1985336493482758312456123 := by
  unfold tailWord_3866429
  simp only [CollatzResearch.WordTrace]
  refine ⟨141020250909595541346474341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94013500606397027564316227 141020250909595541346474341)
  ·
    refine ⟨26441297045549164002463939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141020250909595541346474341 26441297045549164002463939)
    ·
      refine ⟨39661945568323746003695909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26441297045549164002463939 39661945568323746003695909)
      ·
        refine ⟨7436614794060702375692983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39661945568323746003695909 7436614794060702375692983)
        ·
          refine ⟨11154922191091053563539475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7436614794060702375692983 11154922191091053563539475)
          ·
            refine ⟨16732383286636580345309213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11154922191091053563539475 16732383286636580345309213)
            ·
              refine ⟨6274643732488717629490955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16732383286636580345309213 6274643732488717629490955)
              ·
                refine ⟨9411965598733076444236433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6274643732488717629490955 9411965598733076444236433)
                ·
                  refine ⟨7058974199049807333177325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9411965598733076444236433 7058974199049807333177325)
                  ·
                    refine ⟨2647115324643677749941497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7058974199049807333177325 2647115324643677749941497)
                    ·
                      refine ⟨1985336493482758312456123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2647115324643677749941497 1985336493482758312456123)
                      ·
                        rfl

theorem cell23_3866429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_3866429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866429 prefixEnd_3866429 := by exact prefixLift 3866429
  have htrace : WordTrace (prefixWord ++ tailWord_3866429) baseStart_3866429 baseEnd_3866429 := by
    simpa [prefixWord, tailWord_3866429, baseEnd_3866429] using wordTrace_append hprefix tailTrace_3866429
  have hstable : (prefixWord ++ tailWord_3866429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866429).length < 2 ^ (prefixWord ++ tailWord_3866429).sum := by decide
  have hdescent : baseEnd_3866429 < baseStart_3866429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866442 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 5, 2, 2]
def baseStart_3866442 : Nat := 118140960795 + 3866442 * 2 ^ 59
def prefixEnd_3866442 : Nat := 4983230072969 + 3 ^ 40 * 3866442 * 2
def baseEnd_3866442 : Nat := 1985343168731266761593563

theorem tailTrace_3866442 : CollatzResearch.WordTrace tailWord_3866442 prefixEnd_3866442 1985343168731266761593563 := by
  unfold tailWord_3866442
  simp only [CollatzResearch.WordTrace]
  refine ⟨35255181264637111141674395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94013816705698963044465053 35255181264637111141674395)
  ·
    refine ⟨52882771896955666712511593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35255181264637111141674395 52882771896955666712511593)
    ·
      refine ⟨39662078922716750034383695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52882771896955666712511593 39662078922716750034383695)
      ·
        refine ⟨59493118384075125051575543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39662078922716750034383695 59493118384075125051575543)
        ·
          refine ⟨89239677576112687577363315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59493118384075125051575543 89239677576112687577363315)
          ·
            refine ⟨133859516364169031366044973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89239677576112687577363315 133859516364169031366044973)
            ·
              refine ⟨50197318636563386762266865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133859516364169031366044973 50197318636563386762266865)
              ·
                refine ⟨37647988977422540071700149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50197318636563386762266865 37647988977422540071700149)
                ·
                  refine ⟨3529498966633363131721889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37647988977422540071700149 3529498966633363131721889)
                  ·
                    refine ⟨2647124224975022348791417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3529498966633363131721889 2647124224975022348791417)
                    ·
                      refine ⟨1985343168731266761593563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2647124224975022348791417 1985343168731266761593563)
                      ·
                        rfl

theorem cell23_3866442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 5, 2, 2].length) (baseStart_3866442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866442 prefixEnd_3866442 := by exact prefixLift 3866442
  have htrace : WordTrace (prefixWord ++ tailWord_3866442) baseStart_3866442 baseEnd_3866442 := by
    simpa [prefixWord, tailWord_3866442, baseEnd_3866442] using wordTrace_append hprefix tailTrace_3866442
  have hstable : (prefixWord ++ tailWord_3866442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866442).length < 2 ^ (prefixWord ++ tailWord_3866442).sum := by decide
  have hdescent : baseEnd_3866442 < baseStart_3866442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866452 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 4, 4]
def baseStart_3866452 : Nat := 118140960795 + 3866452 * 2 ^ 59
def prefixEnd_3866452 : Nat := 4983230072969 + 3 ^ 40 * 3866452 * 2
def baseEnd_3866452 : Nat := 661782767845937240822839

theorem tailTrace_3866452 : CollatzResearch.WordTrace tailWord_3866452 prefixEnd_3866452 661782767845937240822839 := by
  unfold tailWord_3866452
  simp only [CollatzResearch.WordTrace]
  refine ⟨70510544894256108137280805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94014059859008144183041073 70510544894256108137280805)
  ·
    refine ⟨13220727167673020275740151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70510544894256108137280805 13220727167673020275740151)
    ·
      refine ⟨19831090751509530413610227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13220727167673020275740151 19831090751509530413610227)
      ·
        refine ⟨29746636127264295620415341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19831090751509530413610227 29746636127264295620415341)
        ·
          refine ⟨11154988547724110857655753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29746636127264295620415341 11154988547724110857655753)
          ·
            refine ⟨8366241410793083143241815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11154988547724110857655753 8366241410793083143241815)
            ·
              refine ⟨12549362116189624714862723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8366241410793083143241815 12549362116189624714862723)
              ·
                refine ⟨18824043174284437072294085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12549362116189624714862723 18824043174284437072294085)
                ·
                  refine ⟨3529508095178331951055141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18824043174284437072294085 3529508095178331951055141)
                  ·
                    refine ⟨661782767845937240822839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3529508095178331951055141 661782767845937240822839)
                    ·
                      rfl

theorem cell23_3866452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_3866452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866452 prefixEnd_3866452 := by exact prefixLift 3866452
  have htrace : WordTrace (prefixWord ++ tailWord_3866452) baseStart_3866452 baseEnd_3866452 := by
    simpa [prefixWord, tailWord_3866452, baseEnd_3866452] using wordTrace_append hprefix tailTrace_3866452
  have hstable : (prefixWord ++ tailWord_3866452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866452).length < 2 ^ (prefixWord ++ tailWord_3866452).sum := by decide
  have hdescent : baseEnd_3866452 < baseStart_3866452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866510 : List Nat := [4, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2]
def baseStart_3866510 : Nat := 118140960795 + 3866510 * 2 ^ 59
def prefixEnd_3866510 : Nat := 4983230072969 + 3 ^ 40 * 3866510 * 2
def baseEnd_3866510 : Nat := 1985378085415772495543251

theorem tailTrace_3866510 : CollatzResearch.WordTrace tailWord_3866510 prefixEnd_3866510 1985378085415772495543251 := by
  unfold tailWord_3866510
  simp only [CollatzResearch.WordTrace]
  refine ⟨17627900652787761522521623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94015470148201394786781989 17627900652787761522521623)
  ·
    refine ⟨26441850979181642283782435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17627900652787761522521623 26441850979181642283782435)
    ·
      refine ⟨39662776468772463425673653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26441850979181642283782435 39662776468772463425673653)
      ·
        refine ⟨3718385293947418446156905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39662776468772463425673653 3718385293947418446156905)
        ·
          refine ⟨2788788970460563834617679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3718385293947418446156905 2788788970460563834617679)
          ·
            refine ⟨4183183455690845751926519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2788788970460563834617679 4183183455690845751926519)
            ·
              refine ⟨6274775183536268627889779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4183183455690845751926519 6274775183536268627889779)
              ·
                refine ⟨9412162775304402941834669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6274775183536268627889779 9412162775304402941834669)
                ·
                  refine ⟨3529561040739151103188001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9412162775304402941834669 3529561040739151103188001)
                  ·
                    refine ⟨2647170780554363327391001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3529561040739151103188001 2647170780554363327391001)
                    ·
                      refine ⟨1985378085415772495543251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2647170780554363327391001 1985378085415772495543251)
                      ·
                        rfl

theorem cell23_3866510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_3866510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866510 prefixEnd_3866510 := by exact prefixLift 3866510
  have htrace : WordTrace (prefixWord ++ tailWord_3866510) baseStart_3866510 baseEnd_3866510 := by
    simpa [prefixWord, tailWord_3866510, baseEnd_3866510] using wordTrace_append hprefix tailTrace_3866510
  have hstable : (prefixWord ++ tailWord_3866510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866510).length < 2 ^ (prefixWord ++ tailWord_3866510).sum := by decide
  have hdescent : baseEnd_3866510 < baseStart_3866510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866549 : List Nat := [1, 3, 3, 2, 1, 3, 1, 2, 1, 4, 2]
def baseStart_3866549 : Nat := 118140960795 + 3866549 * 2 ^ 59
def prefixEnd_3866549 : Nat := 4983230072969 + 3 ^ 40 * 3866549 * 2
def baseEnd_3866549 : Nat := 1985398111161297842955571

theorem tailTrace_3866549 : CollatzResearch.WordTrace tailWord_3866549 prefixEnd_3866549 1985398111161297842955571 := by
  unfold tailWord_3866549
  simp only [CollatzResearch.WordTrace]
  refine ⟨141024627669160801840842701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94016418446107201227228467 141024627669160801840842701)
  ·
    refine ⟨52884235375935300690316013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141024627669160801840842701 52884235375935300690316013)
    ·
      refine ⟨19831588265975737758868505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52884235375935300690316013 19831588265975737758868505)
      ·
        refine ⟨14873691199481803319151379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19831588265975737758868505 14873691199481803319151379)
        ·
          refine ⟨22310536799222704978727069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14873691199481803319151379 22310536799222704978727069)
          ·
            refine ⟨8366451299708514367022651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22310536799222704978727069 8366451299708514367022651)
            ·
              refine ⟨12549676949562771550533977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8366451299708514367022651 12549676949562771550533977)
              ·
                refine ⟨9412257712172078662900483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12549676949562771550533977 9412257712172078662900483)
                ·
                  refine ⟨14118386568258117994350725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9412257712172078662900483 14118386568258117994350725)
                  ·
                    refine ⟨2647197481548397123940761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14118386568258117994350725 2647197481548397123940761)
                    ·
                      refine ⟨1985398111161297842955571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2647197481548397123940761 1985398111161297842955571)
                      ·
                        rfl

theorem cell23_3866549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_3866549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866549 prefixEnd_3866549 := by exact prefixLift 3866549
  have htrace : WordTrace (prefixWord ++ tailWord_3866549) baseStart_3866549 baseEnd_3866549 := by
    simpa [prefixWord, tailWord_3866549, baseEnd_3866549] using wordTrace_append hprefix tailTrace_3866549
  have hstable : (prefixWord ++ tailWord_3866549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866549).length < 2 ^ (prefixWord ++ tailWord_3866549).sum := by decide
  have hdescent : baseEnd_3866549 < baseStart_3866549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866635 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 6]
def baseStart_3866635 : Nat := 118140960795 + 3866635 * 2 ^ 59
def prefixEnd_3866635 : Nat := 4983230072969 + 3 ^ 40 * 3866635 * 2
def baseEnd_3866635 : Nat := 1985442270497584506480175

theorem tailTrace_3866635 : CollatzResearch.WordTrace tailWord_3866635 prefixEnd_3866635 1985442270497584506480175 := by
  unfold tailWord_3866635
  simp only [CollatzResearch.WordTrace]
  refine ⟨141027764346849238528473359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94018509564566159018982239 141027764346849238528473359)
  ·
    refine ⟨211541646520273857792710039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141027764346849238528473359 211541646520273857792710039)
    ·
      refine ⟨317312469780410786689065059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211541646520273857792710039 317312469780410786689065059)
      ·
        refine ⟨475968704670616180033597589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317312469780410786689065059 475968704670616180033597589)
        ·
          refine ⟨22311033031435133439074887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 475968704670616180033597589 22311033031435133439074887)
          ·
            refine ⟨33466549547152700158612331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22311033031435133439074887 33466549547152700158612331)
            ·
              refine ⟨50199824320729050237918497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33466549547152700158612331 50199824320729050237918497)
              ·
                refine ⟨37649868240546787678438873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50199824320729050237918497 37649868240546787678438873)
                ·
                  refine ⟨28237401180410090758829155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37649868240546787678438873 28237401180410090758829155)
                  ·
                    refine ⟨42356101770615136138243733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28237401180410090758829155 42356101770615136138243733)
                    ·
                      refine ⟨1985442270497584506480175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42356101770615136138243733 1985442270497584506480175)
                      ·
                        rfl

theorem cell23_3866635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 6].length) (baseStart_3866635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866635 prefixEnd_3866635 := by exact prefixLift 3866635
  have htrace : WordTrace (prefixWord ++ tailWord_3866635) baseStart_3866635 baseEnd_3866635 := by
    simpa [prefixWord, tailWord_3866635, baseEnd_3866635] using wordTrace_append hprefix tailTrace_3866635
  have hstable : (prefixWord ++ tailWord_3866635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866635).length < 2 ^ (prefixWord ++ tailWord_3866635).sum := by decide
  have hdescent : baseEnd_3866635 < baseStart_3866635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866709 : List Nat := [1, 3, 2, 2, 1, 3, 3, 2, 1, 5]
def baseStart_3866709 : Nat := 118140960795 + 3866709 * 2 ^ 59
def prefixEnd_3866709 : Nat := 4983230072969 + 3 ^ 40 * 3866709 * 2
def baseEnd_3866709 : Nat := 661826756022005738984945

theorem tailTrace_3866709 : CollatzResearch.WordTrace tailWord_3866709 prefixEnd_3866709 661826756022005738984945 := by
  unfold tailWord_3866709
  simp only [CollatzResearch.WordTrace]
  refine ⟨141030463348581149166667181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94020308899054099444444787 141030463348581149166667181)
  ·
    refine ⟨52886423755717930937500193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141030463348581149166667181 52886423755717930937500193)
    ·
      refine ⟨39664817816788448203125145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52886423755717930937500193 39664817816788448203125145)
      ·
        refine ⟨29748613362591336152343859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39664817816788448203125145 29748613362591336152343859)
        ·
          refine ⟨44622920043887004228515789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29748613362591336152343859 44622920043887004228515789)
          ·
            refine ⟨16733595016457626585693421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44622920043887004228515789 16733595016457626585693421)
            ·
              refine ⟨6275098131171609969635033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16733595016457626585693421 6275098131171609969635033)
              ·
                refine ⟨4706323598378707477226275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6275098131171609969635033 4706323598378707477226275)
                ·
                  refine ⟨7059485397568061215839413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4706323598378707477226275 7059485397568061215839413)
                  ·
                    refine ⟨661826756022005738984945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7059485397568061215839413 661826756022005738984945)
                    ·
                      rfl

theorem cell23_3866709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_3866709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866709 prefixEnd_3866709 := by exact prefixLift 3866709
  have htrace : WordTrace (prefixWord ++ tailWord_3866709) baseStart_3866709 baseEnd_3866709 := by
    simpa [prefixWord, tailWord_3866709, baseEnd_3866709] using wordTrace_append hprefix tailTrace_3866709
  have hstable : (prefixWord ++ tailWord_3866709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866709).length < 2 ^ (prefixWord ++ tailWord_3866709).sum := by decide
  have hdescent : baseEnd_3866709 < baseStart_3866709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866716 : List Nat := [2, 2, 4, 1, 1, 2, 1, 3, 2, 3, 2]
def baseStart_3866716 : Nat := 118140960795 + 3866716 * 2 ^ 59
def prefixEnd_3866716 : Nat := 4983230072969 + 3 ^ 40 * 3866716 * 2
def baseEnd_3866716 : Nat := 1985483862430598689567303

theorem tailTrace_3866716 : CollatzResearch.WordTrace tailWord_3866716 prefixEnd_3866716 1985483862430598689567303 := by
  unfold tailWord_3866716
  simp only [CollatzResearch.WordTrace]
  refine ⟨70515359329777894681086001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94020479106370526241448001 70515359329777894681086001)
  ·
    refine ⟨52886519497333421010814501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70515359329777894681086001 52886519497333421010814501)
    ·
      refine ⟨9916222405750016439527719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52886519497333421010814501 9916222405750016439527719)
      ·
        refine ⟨14874333608625024659291579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9916222405750016439527719 14874333608625024659291579)
        ·
          refine ⟨22311500412937536988937369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14874333608625024659291579 22311500412937536988937369)
          ·
            refine ⟨16733625309703152741703027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22311500412937536988937369 16733625309703152741703027)
            ·
              refine ⟨25100437964554729112554541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16733625309703152741703027 25100437964554729112554541)
              ·
                refine ⟨9412664236708023417207953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25100437964554729112554541 9412664236708023417207953)
                ·
                  refine ⟨7059498177531017562905965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9412664236708023417207953 7059498177531017562905965)
                  ·
                    refine ⟨2647311816574131586089737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7059498177531017562905965 2647311816574131586089737)
                    ·
                      refine ⟨1985483862430598689567303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2647311816574131586089737 1985483862430598689567303)
                      ·
                        rfl

theorem cell23_3866716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_3866716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866716 prefixEnd_3866716 := by exact prefixLift 3866716
  have htrace : WordTrace (prefixWord ++ tailWord_3866716) baseStart_3866716 baseEnd_3866716 := by
    simpa [prefixWord, tailWord_3866716, baseEnd_3866716] using wordTrace_append hprefix tailTrace_3866716
  have hstable : (prefixWord ++ tailWord_3866716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866716).length < 2 ^ (prefixWord ++ tailWord_3866716).sum := by decide
  have hdescent : baseEnd_3866716 < baseStart_3866716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866735 : List Nat := [1, 1, 2, 1, 3, 15]
def baseStart_3866735 : Nat := 118140960795 + 3866735 * 2 ^ 59
def prefixEnd_3866735 : Nat := 4983230072969 + 3 ^ 40 * 3866735 * 2
def baseEnd_3866735 : Nat := 8170755631946642449505

theorem tailTrace_3866735 : CollatzResearch.WordTrace tailWord_3866735 prefixEnd_3866735 8170755631946642449505 := by
  unfold tailWord_3866735
  simp only [CollatzResearch.WordTrace]
  refine ⟨141031411646486955607113659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94020941097657970404742439 141031411646486955607113659)
  ·
    refine ⟨211547117469730433410670489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141031411646486955607113659 211547117469730433410670489)
    ·
      refine ⟨158660338102297825058002867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211547117469730433410670489 158660338102297825058002867)
      ·
        refine ⟨237990507153446737587004301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158660338102297825058002867 237990507153446737587004301)
        ·
          refine ⟨89246440182542526595126613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237990507153446737587004301 89246440182542526595126613)
          ·
            refine ⟨8170755631946642449505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 89246440182542526595126613 8170755631946642449505)
            ·
              rfl

theorem cell23_3866735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 15].length) (baseStart_3866735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866735 prefixEnd_3866735 := by exact prefixLift 3866735
  have htrace : WordTrace (prefixWord ++ tailWord_3866735) baseStart_3866735 baseEnd_3866735 := by
    simpa [prefixWord, tailWord_3866735, baseEnd_3866735] using wordTrace_append hprefix tailTrace_3866735
  have hstable : (prefixWord ++ tailWord_3866735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866735).length < 2 ^ (prefixWord ++ tailWord_3866735).sum := by decide
  have hdescent : baseEnd_3866735 < baseStart_3866735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866749 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 3, 2, 3]
def baseStart_3866749 : Nat := 118140960795 + 3866749 * 2 ^ 59
def prefixEnd_3866749 : Nat := 4983230072969 + 3 ^ 40 * 3866749 * 2
def baseEnd_3866749 : Nat := 1985500807292197060454651

theorem tailTrace_3866749 : CollatzResearch.WordTrace tailWord_3866749 prefixEnd_3866749 1985500807292197060454651 := by
  unfold tailWord_3866749
  simp only [CollatzResearch.WordTrace]
  refine ⟨141031922268436235998123301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94021281512290823998748867 141031922268436235998123301)
  ·
    refine ⟨26443485425331794249648119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141031922268436235998123301 26443485425331794249648119)
    ·
      refine ⟨39665228137997691374472179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26443485425331794249648119 39665228137997691374472179)
      ·
        refine ⟨59497842206996537061708269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39665228137997691374472179 59497842206996537061708269)
        ·
          refine ⟨22311690827623701398140601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59497842206996537061708269 22311690827623701398140601)
          ·
            refine ⟨16733768120717776048605451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22311690827623701398140601 16733768120717776048605451)
            ·
              refine ⟨25100652181076664072908177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16733768120717776048605451 25100652181076664072908177)
              ·
                refine ⟨18825489135807498054681133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25100652181076664072908177 18825489135807498054681133)
                ·
                  refine ⟨7059558425927811770505425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18825489135807498054681133 7059558425927811770505425)
                  ·
                    refine ⟨5294668819445858827879069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7059558425927811770505425 5294668819445858827879069)
                    ·
                      refine ⟨1985500807292197060454651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5294668819445858827879069 1985500807292197060454651)
                      ·
                        rfl

theorem cell23_3866749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_3866749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866749 prefixEnd_3866749 := by exact prefixLift 3866749
  have htrace : WordTrace (prefixWord ++ tailWord_3866749) baseStart_3866749 baseEnd_3866749 := by
    simpa [prefixWord, tailWord_3866749, baseEnd_3866749] using wordTrace_append hprefix tailTrace_3866749
  have hstable : (prefixWord ++ tailWord_3866749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866749).length < 2 ^ (prefixWord ++ tailWord_3866749).sum := by decide
  have hdescent : baseEnd_3866749 < baseStart_3866749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866780 : List Nat := [2, 2, 3, 2, 1, 1, 4, 3, 1, 2, 2]
def baseStart_3866780 : Nat := 118140960795 + 3866780 * 2 ^ 59
def prefixEnd_3866780 : Nat := 4983230072969 + 3 ^ 40 * 3866780 * 2
def baseEnd_3866780 : Nat := 1985516725192486439167009

theorem tailTrace_3866780 : CollatzResearch.WordTrace tailWord_3866780 prefixEnd_3866780 1985516725192486439167009 := by
  unfold tailWord_3866780
  simp only [CollatzResearch.WordTrace]
  refine ⟨70516526465661964146250897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94022035287549285528334529 70516526465661964146250897)
  ·
    refine ⟨52887394849246473109688173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70516526465661964146250897 52887394849246473109688173)
    ·
      refine ⟨19832773068467427416133065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52887394849246473109688173 19832773068467427416133065)
      ·
        refine ⟨14874579801350570562099799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19832773068467427416133065 14874579801350570562099799)
        ·
          refine ⟨22311869702025855843149699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14874579801350570562099799 22311869702025855843149699)
          ·
            refine ⟨33467804553038783764724549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22311869702025855843149699 33467804553038783764724549)
            ·
              refine ⟨6275213353694771955885853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33467804553038783764724549 6275213353694771955885853)
              ·
                refine ⟨2353205007635539483457195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6275213353694771955885853 2353205007635539483457195)
                ·
                  refine ⟨3529807511453309225185793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2353205007635539483457195 3529807511453309225185793)
                  ·
                    refine ⟨2647355633589981918889345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3529807511453309225185793 2647355633589981918889345)
                    ·
                      refine ⟨1985516725192486439167009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2647355633589981918889345 1985516725192486439167009)
                      ·
                        rfl

theorem cell23_3866780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_3866780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866780 prefixEnd_3866780 := by exact prefixLift 3866780
  have htrace : WordTrace (prefixWord ++ tailWord_3866780) baseStart_3866780 baseEnd_3866780 := by
    simpa [prefixWord, tailWord_3866780, baseEnd_3866780] using wordTrace_append hprefix tailTrace_3866780
  have hstable : (prefixWord ++ tailWord_3866780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866780).length < 2 ^ (prefixWord ++ tailWord_3866780).sum := by decide
  have hdescent : baseEnd_3866780 < baseStart_3866780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866783 : List Nat := [1, 1, 2, 6, 1, 1, 4, 1, 1, 2, 3]
def baseStart_3866783 : Nat := 118140960795 + 3866783 * 2 ^ 59
def prefixEnd_3866783 : Nat := 4983230072969 + 3 ^ 40 * 3866783 * 2
def baseEnd_3866783 : Nat := 1985518265634449927429495

theorem tailTrace_3866783 : CollatzResearch.WordTrace tailWord_3866783 prefixEnd_3866783 1985518265634449927429495 := by
  unfold tailWord_3866783
  simp only [CollatzResearch.WordTrace]
  refine ⟨141033162350313059804861003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94022108233542039869907335 141033162350313059804861003)
  ·
    refine ⟨211549743525469589707291505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141033162350313059804861003 211549743525469589707291505)
    ·
      refine ⟨158662307644102192280468629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211549743525469589707291505 158662307644102192280468629)
      ·
        refine ⟨7437295670817290263146967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 158662307644102192280468629 7437295670817290263146967)
        ·
          refine ⟨11155943506225935394720451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7437295670817290263146967 11155943506225935394720451)
          ·
            refine ⟨16733915259338903092080677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11155943506225935394720451 16733915259338903092080677)
            ·
              refine ⟨3137609111126044329765127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16733915259338903092080677 3137609111126044329765127)
              ·
                refine ⟨4706413666689066494647691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3137609111126044329765127 4706413666689066494647691)
                ·
                  refine ⟨7059620500033599741971537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4706413666689066494647691 7059620500033599741971537)
                  ·
                    refine ⟨5294715375025199806478653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7059620500033599741971537 5294715375025199806478653)
                    ·
                      refine ⟨1985518265634449927429495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5294715375025199806478653 1985518265634449927429495)
                      ·
                        rfl

theorem cell23_3866783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_3866783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866783 prefixEnd_3866783 := by exact prefixLift 3866783
  have htrace : WordTrace (prefixWord ++ tailWord_3866783) baseStart_3866783 baseEnd_3866783 := by
    simpa [prefixWord, tailWord_3866783, baseEnd_3866783] using wordTrace_append hprefix tailTrace_3866783
  have hstable : (prefixWord ++ tailWord_3866783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866783).length < 2 ^ (prefixWord ++ tailWord_3866783).sum := by decide
  have hdescent : baseEnd_3866783 < baseStart_3866783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866842 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 9]
def baseStart_3866842 : Nat := 118140960795 + 3866842 * 2 ^ 59
def prefixEnd_3866842 : Nat := 4983230072969 + 3 ^ 40 * 3866842 * 2
def baseEnd_3866842 : Nat := 220616506777007244065747

theorem tailTrace_3866842 : CollatzResearch.WordTrace tailWord_3866842 prefixEnd_3866842 220616506777007244065747 := by
  unfold tailWord_3866842
  simp only [CollatzResearch.WordTrace]
  refine ⟨35258828564274828220314695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94023542838066208587505853 35258828564274828220314695)
  ·
    refine ⟨52888242846412242330472043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35258828564274828220314695 52888242846412242330472043)
    ·
      refine ⟨79332364269618363495708065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52888242846412242330472043 79332364269618363495708065)
      ·
        refine ⟨59499273202213772621781049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79332364269618363495708065 59499273202213772621781049)
        ·
          refine ⟨44624454901660329466335787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59499273202213772621781049 44624454901660329466335787)
          ·
            refine ⟨66936682352490494199503681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44624454901660329466335787 66936682352490494199503681)
            ·
              refine ⟨50202511764367870649627761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66936682352490494199503681 50202511764367870649627761)
              ·
                refine ⟨37651883823275902987220821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50202511764367870649627761 37651883823275902987220821)
                ·
                  refine ⟨220616506777007244065747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37651883823275902987220821 220616506777007244065747)
                  ·
                    rfl

theorem cell23_3866842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 9].length) (baseStart_3866842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866842 prefixEnd_3866842 := by exact prefixLift 3866842
  have htrace : WordTrace (prefixWord ++ tailWord_3866842) baseStart_3866842 baseEnd_3866842 := by
    simpa [prefixWord, tailWord_3866842, baseEnd_3866842] using wordTrace_append hprefix tailTrace_3866842
  have hstable : (prefixWord ++ tailWord_3866842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866842).length < 2 ^ (prefixWord ++ tailWord_3866842).sum := by decide
  have hdescent : baseEnd_3866842 < baseStart_3866842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866852 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 1, 1, 9]
def baseStart_3866852 : Nat := 118140960795 + 3866852 * 2 ^ 59
def prefixEnd_3866852 : Nat := 4983230072969 + 3 ^ 40 * 3866852 * 2
def baseEnd_3866852 : Nat := 1985553695799610157466677

theorem tailTrace_3866852 : CollatzResearch.WordTrace tailWord_3866852 prefixEnd_3866852 1985553695799610157466677 := by
  unfold tailWord_3866852
  simp only [CollatzResearch.WordTrace]
  refine ⟨70517839493531542294561405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94023785991375389726081873 70517839493531542294561405)
  ·
    refine ⟨26444189810074328360460527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70517839493531542294561405 26444189810074328360460527)
    ·
      refine ⟨39666284715111492540690791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26444189810074328360460527 39666284715111492540690791)
      ·
        refine ⟨59499427072667238811036187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39666284715111492540690791 59499427072667238811036187)
        ·
          refine ⟨89249140609000858216554281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59499427072667238811036187 89249140609000858216554281)
          ·
            refine ⟨66936855456750643662415711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89249140609000858216554281 66936855456750643662415711)
            ·
              refine ⟨100405283185125965493623567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66936855456750643662415711 100405283185125965493623567)
              ·
                refine ⟨150607924777688948240435351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100405283185125965493623567 150607924777688948240435351)
                ·
                  refine ⟨225911887166533422360653027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150607924777688948240435351 225911887166533422360653027)
                  ·
                    refine ⟨338867830749800133540979541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 225911887166533422360653027 338867830749800133540979541)
                    ·
                      refine ⟨1985553695799610157466677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 338867830749800133540979541 1985553695799610157466677)
                      ·
                        rfl

theorem cell23_3866852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_3866852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866852 prefixEnd_3866852 := by exact prefixLift 3866852
  have htrace : WordTrace (prefixWord ++ tailWord_3866852) baseStart_3866852 baseEnd_3866852 := by
    simpa [prefixWord, tailWord_3866852, baseEnd_3866852] using wordTrace_append hprefix tailTrace_3866852
  have hstable : (prefixWord ++ tailWord_3866852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866852).length < 2 ^ (prefixWord ++ tailWord_3866852).sum := by decide
  have hdescent : baseEnd_3866852 < baseStart_3866852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866853 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 4, 2, 2]
def baseStart_3866853 : Nat := 118140960795 + 3866853 * 2 ^ 59
def prefixEnd_3866853 : Nat := 4983230072969 + 3 ^ 40 * 3866853 * 2
def baseEnd_3866853 : Nat := 1985554209280264653554173

theorem tailTrace_3866853 : CollatzResearch.WordTrace tailWord_3866853 prefixEnd_3866853 1985554209280264653554173 := by
  unfold tailWord_3866853
  simp only [CollatzResearch.WordTrace]
  refine ⟨141035715460059461759909213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94023810306706307839939475 141035715460059461759909213)
  ·
    refine ⟨52888393297522298159965955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141035715460059461759909213 52888393297522298159965955)
    ·
      refine ⟨79332589946283447239948933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52888393297522298159965955 79332589946283447239948933)
      ·
        refine ⟨14874860614928146357490425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79332589946283447239948933 14874860614928146357490425)
        ·
          refine ⟨11156145461196109768117819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14874860614928146357490425 11156145461196109768117819)
          ·
            refine ⟨16734218191794164652176729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11156145461196109768117819 16734218191794164652176729)
            ·
              refine ⟨12550663643845623489132547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16734218191794164652176729 12550663643845623489132547)
              ·
                refine ⟨18825995465768435233698821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12550663643845623489132547 18825995465768435233698821)
                ·
                  refine ⟨3529874149831581606318529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18825995465768435233698821 3529874149831581606318529)
                  ·
                    refine ⟨2647405612373686204738897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3529874149831581606318529 2647405612373686204738897)
                    ·
                      refine ⟨1985554209280264653554173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2647405612373686204738897 1985554209280264653554173)
                      ·
                        rfl

theorem cell23_3866853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_3866853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866853 prefixEnd_3866853 := by exact prefixLift 3866853
  have htrace : WordTrace (prefixWord ++ tailWord_3866853) baseStart_3866853 baseEnd_3866853 := by
    simpa [prefixWord, tailWord_3866853, baseEnd_3866853] using wordTrace_append hprefix tailTrace_3866853
  have hstable : (prefixWord ++ tailWord_3866853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866853).length < 2 ^ (prefixWord ++ tailWord_3866853).sum := by decide
  have hdescent : baseEnd_3866853 < baseStart_3866853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
