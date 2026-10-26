import V185TrunkScan23Chunk0762

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4511907 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 8]
def baseStart_4511907 : Nat := 118140960795 + 4511907 * 2 ^ 59
def prefixEnd_4511907 : Nat := 4983230072969 + 3 ^ 40 * 4511907 * 2
def baseEnd_4511907 : Nat := 2316776959385583876812623

theorem tailTrace_4511907 : CollatzResearch.WordTrace tailWord_4511907 prefixEnd_4511907 2316776959385583876812623 := by
  unfold tailWord_4511907
  simp only [CollatzResearch.WordTrace]
  refine ⟨164562767665138986212309975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109708511776759324141539983 164562767665138986212309975)
  ·
    refine ⟨246844151497708479318464963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164562767665138986212309975 246844151497708479318464963)
    ·
      refine ⟨370266227246562718977697445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246844151497708479318464963 370266227246562718977697445)
      ·
        refine ⟨69424917608730509808318271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 370266227246562718977697445 69424917608730509808318271)
        ·
          refine ⟨104137376413095764712477407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69424917608730509808318271 104137376413095764712477407)
          ·
            refine ⟨156206064619643647068716111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104137376413095764712477407 156206064619643647068716111)
            ·
              refine ⟨234309096929465470603074167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156206064619643647068716111 234309096929465470603074167)
              ·
                refine ⟨351463645394198205904611251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234309096929465470603074167 351463645394198205904611251)
                ·
                  refine ⟨527195468091297308856916877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 351463645394198205904611251 527195468091297308856916877)
                  ·
                    refine ⟨197698300534236490821343829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 527195468091297308856916877 197698300534236490821343829)
                    ·
                      refine ⟨2316776959385583876812623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 197698300534236490821343829 2316776959385583876812623)
                      ·
                        rfl

theorem cell23_4511907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_4511907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511907 prefixEnd_4511907 := by exact prefixLift 4511907
  have htrace : WordTrace (prefixWord ++ tailWord_4511907) baseStart_4511907 baseEnd_4511907 := by
    simpa [prefixWord, tailWord_4511907, baseEnd_4511907] using wordTrace_append hprefix tailTrace_4511907
  have hstable : (prefixWord ++ tailWord_4511907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511907).length < 2 ^ (prefixWord ++ tailWord_4511907).sum := by decide
  have hdescent : baseEnd_4511907 < baseStart_4511907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511921 : List Nat := [1, 2, 2, 5, 2, 1, 1, 2, 7]
def baseStart_4511921 : Nat := 118140960795 + 4511921 * 2 ^ 59
def prefixEnd_4511921 : Nat := 4983230072969 + 3 ^ 40 * 4511921 * 2
def baseEnd_4511921 : Nat := 257420460901638535781951

theorem tailTrace_4511921 : CollatzResearch.WordTrace tailWord_4511921 prefixEnd_4511921 257420460901638535781951 := by
  unfold tailWord_4511921
  simp only [CollatzResearch.WordTrace]
  refine ⟨164563278287088266603319617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109708852191392177735546411 164563278287088266603319617)
  ·
    refine ⟨123422458715316199952489713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164563278287088266603319617 123422458715316199952489713)
    ·
      refine ⟨92566844036487149964367285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123422458715316199952489713 92566844036487149964367285)
      ·
        refine ⟨8678141628420670309159433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92566844036487149964367285 8678141628420670309159433)
        ·
          refine ⟨6508606221315502731869575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8678141628420670309159433 6508606221315502731869575)
          ·
            refine ⟨9762909331973254097804363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6508606221315502731869575 9762909331973254097804363)
            ·
              refine ⟨14644363997959881146706545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9762909331973254097804363 14644363997959881146706545)
              ·
                refine ⟨10983272998469910860029909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14644363997959881146706545 10983272998469910860029909)
                ·
                  refine ⟨257420460901638535781951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10983272998469910860029909 257420460901638535781951)
                  ·
                    rfl

theorem cell23_4511921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 7].length) (baseStart_4511921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511921 prefixEnd_4511921 := by exact prefixLift 4511921
  have htrace : WordTrace (prefixWord ++ tailWord_4511921) baseStart_4511921 baseEnd_4511921 := by
    simpa [prefixWord, tailWord_4511921, baseEnd_4511921] using wordTrace_append hprefix tailTrace_4511921
  have hstable : (prefixWord ++ tailWord_4511921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511921).length < 2 ^ (prefixWord ++ tailWord_4511921).sum := by decide
  have hdescent : baseEnd_4511921 < baseStart_4511921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511994 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 8]
def baseStart_4511994 : Nat := 118140960795 + 4511994 * 2 ^ 59
def prefixEnd_4511994 : Nat := 4983230072969 + 3 ^ 40 * 4511994 * 2
def baseEnd_4511994 : Nat := 257424625800280559602747

theorem tailTrace_4511994 : CollatzResearch.WordTrace tailWord_4511994 prefixEnd_4511994 257424625800280559602747 := by
  unfold tailWord_4511994
  simp only [CollatzResearch.WordTrace]
  refine ⟨41141485203955950017681759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109710627210549200047151357 41141485203955950017681759)
  ·
    refine ⟨61712227805933925026522639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41141485203955950017681759 61712227805933925026522639)
    ·
      refine ⟨92568341708900887539783959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61712227805933925026522639 92568341708900887539783959)
      ·
        refine ⟨138852512563351331309675939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92568341708900887539783959 138852512563351331309675939)
        ·
          refine ⟨208278768845026996964513909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138852512563351331309675939 208278768845026996964513909)
          ·
            refine ⟨19526134579221280965423179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 208278768845026996964513909 19526134579221280965423179)
            ·
              refine ⟨29289201868831921448134769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19526134579221280965423179 29289201868831921448134769)
              ·
                refine ⟨21966901401623941086101077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29289201868831921448134769 21966901401623941086101077)
                ·
                  refine ⟨257424625800280559602747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21966901401623941086101077 257424625800280559602747)
                  ·
                    rfl

theorem cell23_4511994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 8].length) (baseStart_4511994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511994 prefixEnd_4511994 := by exact prefixLift 4511994
  have htrace : WordTrace (prefixWord ++ tailWord_4511994) baseStart_4511994 baseEnd_4511994 := by
    simpa [prefixWord, tailWord_4511994, baseEnd_4511994] using wordTrace_append hprefix tailTrace_4511994
  have hstable : (prefixWord ++ tailWord_4511994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511994).length < 2 ^ (prefixWord ++ tailWord_4511994).sum := by decide
  have hdescent : baseEnd_4511994 < baseStart_4511994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512008 : List Nat := [2, 1, 3, 2, 3, 2, 1, 2, 2, 2, 3]
def baseStart_4512008 : Nat := 118140960795 + 4512008 * 2 ^ 59
def prefixEnd_4512008 : Nat := 4983230072969 + 3 ^ 40 * 4512008 * 2
def baseEnd_4512008 : Nat := 2316828820931687981649659

theorem tailTrace_4512008 : CollatzResearch.WordTrace tailWord_4512008 prefixEnd_4512008 2316828820931687981649659 := by
  unfold tailWord_4512008
  simp only [CollatzResearch.WordTrace]
  refine ⟨82283225718886540230868339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109710967625182053641157785 82283225718886540230868339)
  ·
    refine ⟨123424838578329810346302509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82283225718886540230868339 123424838578329810346302509)
    ·
      refine ⟨46284314466873678879863441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123424838578329810346302509 46284314466873678879863441)
      ·
        refine ⟨34713235850155259159897581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46284314466873678879863441 34713235850155259159897581)
        ·
          refine ⟨13017463443808222184961593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34713235850155259159897581 13017463443808222184961593)
          ·
            refine ⟨9763097582856166638721195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13017463443808222184961593 9763097582856166638721195)
            ·
              refine ⟨14644646374284249958081793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9763097582856166638721195 14644646374284249958081793)
              ·
                refine ⟨10983484780713187468561345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14644646374284249958081793 10983484780713187468561345)
                ·
                  refine ⟨8237613585534890601421009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10983484780713187468561345 8237613585534890601421009)
                  ·
                    refine ⟨6178210189151167951065757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8237613585534890601421009 6178210189151167951065757)
                    ·
                      refine ⟨2316828820931687981649659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6178210189151167951065757 2316828820931687981649659)
                      ·
                        rfl

theorem cell23_4512008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_4512008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512008 prefixEnd_4512008 := by exact prefixLift 4512008
  have htrace : WordTrace (prefixWord ++ tailWord_4512008) baseStart_4512008 baseEnd_4512008 := by
    simpa [prefixWord, tailWord_4512008, baseEnd_4512008] using wordTrace_append hprefix tailTrace_4512008
  have hstable : (prefixWord ++ tailWord_4512008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512008).length < 2 ^ (prefixWord ++ tailWord_4512008).sum := by decide
  have hdescent : baseEnd_4512008 < baseStart_4512008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512072 : List Nat := [2, 1, 3, 1, 1, 2, 6, 2, 1, 1, 3]
def baseStart_4512072 : Nat := 118140960795 + 4512072 * 2 ^ 59
def prefixEnd_4512072 : Nat := 4983230072969 + 3 ^ 40 * 4512072 * 2
def baseEnd_4512072 : Nat := 2316861683693575731249365

theorem tailTrace_4512072 : CollatzResearch.WordTrace tailWord_4512072 prefixEnd_4512072 2316861683693575731249365 := by
  unfold tailWord_4512072
  simp only [CollatzResearch.WordTrace]
  refine ⟨82284392854770609696033235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109712523806360812928044313 82284392854770609696033235)
  ·
    refine ⟨123426589282155914544049853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82284392854770609696033235 123426589282155914544049853)
    ·
      refine ⟨46284970980808467954018695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123426589282155914544049853 46284970980808467954018695)
      ·
        refine ⟨69427456471212701931028043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46284970980808467954018695 69427456471212701931028043)
        ·
          refine ⟨104141184706819052896542065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69427456471212701931028043 104141184706819052896542065)
          ·
            refine ⟨78105888530114289672406549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104141184706819052896542065 78105888530114289672406549)
            ·
              refine ⟨3661213524849107328394057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78105888530114289672406549 3661213524849107328394057)
              ·
                refine ⟨2745910143636830496295543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3661213524849107328394057 2745910143636830496295543)
                ·
                  refine ⟨4118865215455245744443315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2745910143636830496295543 4118865215455245744443315)
                  ·
                    refine ⟨6178297823182868616664973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4118865215455245744443315 6178297823182868616664973)
                    ·
                      refine ⟨2316861683693575731249365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6178297823182868616664973 2316861683693575731249365)
                      ·
                        rfl

theorem cell23_4512072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 1, 1, 3].length) (baseStart_4512072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512072 prefixEnd_4512072 := by exact prefixLift 4512072
  have htrace : WordTrace (prefixWord ++ tailWord_4512072) baseStart_4512072 baseEnd_4512072 := by
    simpa [prefixWord, tailWord_4512072, baseEnd_4512072] using wordTrace_append hprefix tailTrace_4512072
  have hstable : (prefixWord ++ tailWord_4512072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512072).length < 2 ^ (prefixWord ++ tailWord_4512072).sum := by decide
  have hdescent : baseEnd_4512072 < baseStart_4512072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512111 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 3]
def baseStart_4512111 : Nat := 118140960795 + 4512111 * 2 ^ 59
def prefixEnd_4512111 : Nat := 4983230072969 + 3 ^ 40 * 4512111 * 2
def baseEnd_4512111 : Nat := 2316881709439101078661685

theorem tailTrace_4512111 : CollatzResearch.WordTrace tailWord_4512111 prefixEnd_4512111 2316881709439101078661685 := by
  unfold tailWord_4512111
  simp only [CollatzResearch.WordTrace]
  refine ⟨164570208156399929052736187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109713472104266619368490791 164570208156399929052736187)
  ·
    refine ⟨246855312234599893579104281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164570208156399929052736187 246855312234599893579104281)
    ·
      refine ⟨185141484175949920184328211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246855312234599893579104281 185141484175949920184328211)
      ·
        refine ⟨277712226263924880276492317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185141484175949920184328211 277712226263924880276492317)
        ·
          refine ⟨104142084848971830103684619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 277712226263924880276492317 104142084848971830103684619)
          ·
            refine ⟨156213127273457745155526929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104142084848971830103684619 156213127273457745155526929)
            ·
              refine ⟨117159845455093308866645197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156213127273457745155526929 117159845455093308866645197)
              ·
                refine ⟨43934942045659990824991949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117159845455093308866645197 43934942045659990824991949)
                ·
                  refine ⟨16475603267122496559371981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43934942045659990824991949 16475603267122496559371981)
                  ·
                    refine ⟨6178351225170936209764493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16475603267122496559371981 6178351225170936209764493)
                    ·
                      refine ⟨2316881709439101078661685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6178351225170936209764493 2316881709439101078661685)
                      ·
                        rfl

theorem cell23_4512111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 3].length) (baseStart_4512111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512111 prefixEnd_4512111 := by exact prefixLift 4512111
  have htrace : WordTrace (prefixWord ++ tailWord_4512111) baseStart_4512111 baseEnd_4512111 := by
    simpa [prefixWord, tailWord_4512111, baseEnd_4512111] using wordTrace_append hprefix tailTrace_4512111
  have hstable : (prefixWord ++ tailWord_4512111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512111).length < 2 ^ (prefixWord ++ tailWord_4512111).sum := by decide
  have hdescent : baseEnd_4512111 < baseStart_4512111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512112 : List Nat := [2, 1, 1, 1, 4, 3, 1, 5, 1, 2, 2]
def baseStart_4512112 : Nat := 118140960795 + 4512112 * 2 ^ 59
def prefixEnd_4512112 : Nat := 4983230072969 + 3 ^ 40 * 4512112 * 2
def baseEnd_4512112 : Nat := 2316882222919755574749181

theorem tailTrace_4512112 : CollatzResearch.WordTrace tailWord_4512112 prefixEnd_4512112 2316882222919755574749181 := by
  unfold tailWord_4512112
  simp only [CollatzResearch.WordTrace]
  refine ⟨82285122314698153111761295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109713496419597537482348393 82285122314698153111761295)
  ·
    refine ⟨123427683472047229667641943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82285122314698153111761295 123427683472047229667641943)
    ·
      refine ⟨185141525208070844501462915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123427683472047229667641943 185141525208070844501462915)
      ·
        refine ⟨277712287812106266752194373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185141525208070844501462915 277712287812106266752194373)
        ·
          refine ⟨52071053964769925016036445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 277712287812106266752194373 52071053964769925016036445)
          ·
            refine ⟨19526645236788721881013667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52071053964769925016036445 19526645236788721881013667)
            ·
              refine ⟨29289967855183082821520501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19526645236788721881013667 29289967855183082821520501)
              ·
                refine ⟨2745934486423414014517547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29289967855183082821520501 2745934486423414014517547)
                ·
                  refine ⟨4118901729635121021776321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2745934486423414014517547 4118901729635121021776321)
                  ·
                    refine ⟨3089176297226340766332241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4118901729635121021776321 3089176297226340766332241)
                    ·
                      refine ⟨2316882222919755574749181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3089176297226340766332241 2316882222919755574749181)
                      ·
                        rfl

theorem cell23_4512112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 1, 2, 2].length) (baseStart_4512112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512112 prefixEnd_4512112 := by exact prefixLift 4512112
  have htrace : WordTrace (prefixWord ++ tailWord_4512112) baseStart_4512112 baseEnd_4512112 := by
    simpa [prefixWord, tailWord_4512112, baseEnd_4512112] using wordTrace_append hprefix tailTrace_4512112
  have hstable : (prefixWord ++ tailWord_4512112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512112).length < 2 ^ (prefixWord ++ tailWord_4512112).sum := by decide
  have hdescent : baseEnd_4512112 < baseStart_4512112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512129 : List Nat := [1, 2, 4, 3, 1, 1, 2, 4, 1, 2, 2]
def baseStart_4512129 : Nat := 118140960795 + 4512129 * 2 ^ 59
def prefixEnd_4512129 : Nat := 4983230072969 + 3 ^ 40 * 4512129 * 2
def baseEnd_4512129 : Nat := 2316890952090882008236603

theorem tailTrace_4512129 : CollatzResearch.WordTrace tailWord_4512129 prefixEnd_4512129 2316890952090882008236603 := by
  unfold tailWord_4512129
  simp only [CollatzResearch.WordTrace]
  refine ⟨164570864670334718126891441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109713909780223145417927627 164570864670334718126891441)
  ·
    refine ⟨123428148502751038595168581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164570864670334718126891441 123428148502751038595168581)
    ·
      refine ⟨23142777844265819736594109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123428148502751038595168581 23142777844265819736594109)
      ·
        refine ⟨8678541691599682401222791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23142777844265819736594109 8678541691599682401222791)
        ·
          refine ⟨13017812537399523601834187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8678541691599682401222791 13017812537399523601834187)
          ·
            refine ⟨19526718806099285402751281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13017812537399523601834187 19526718806099285402751281)
            ·
              refine ⟨14645039104574464052063461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19526718806099285402751281 14645039104574464052063461)
              ·
                refine ⟨2745944832107712009761899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14645039104574464052063461 2745944832107712009761899)
                ·
                  refine ⟨4118917248161568014642849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2745944832107712009761899 4118917248161568014642849)
                  ·
                    refine ⟨3089187936121176010982137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4118917248161568014642849 3089187936121176010982137)
                    ·
                      refine ⟨2316890952090882008236603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3089187936121176010982137 2316890952090882008236603)
                      ·
                        rfl

theorem cell23_4512129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_4512129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512129 prefixEnd_4512129 := by exact prefixLift 4512129
  have htrace : WordTrace (prefixWord ++ tailWord_4512129) baseStart_4512129 baseEnd_4512129 := by
    simpa [prefixWord, tailWord_4512129, baseEnd_4512129] using wordTrace_append hprefix tailTrace_4512129
  have hstable : (prefixWord ++ tailWord_4512129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512129).length < 2 ^ (prefixWord ++ tailWord_4512129).sum := by decide
  have hdescent : baseEnd_4512129 < baseStart_4512129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512151 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 4]
def baseStart_4512151 : Nat := 118140960795 + 4512151 * 2 ^ 59
def prefixEnd_4512151 : Nat := 4983230072969 + 3 ^ 40 * 4512151 * 2
def baseEnd_4512151 : Nat := 2316902248665280922161501

theorem tailTrace_4512151 : CollatzResearch.WordTrace tailWord_4512151 prefixEnd_4512151 2316902248665280922161501 := by
  unfold tailWord_4512151
  simp only [CollatzResearch.WordTrace]
  refine ⟨164571667076255015884192307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109714444717503343922794871 164571667076255015884192307)
  ·
    refine ⟨246857500614382523826288461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164571667076255015884192307 246857500614382523826288461)
    ·
      refine ⟨92571562730393446434858173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246857500614382523826288461 92571562730393446434858173)
      ·
        refine ⟨34714336023897542413071815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92571562730393446434858173 34714336023897542413071815)
        ·
          refine ⟨52071504035846313619607723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34714336023897542413071815 52071504035846313619607723)
          ·
            refine ⟨78107256053769470429411585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52071504035846313619607723 78107256053769470429411585)
            ·
              refine ⟨58580442040327102822058689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78107256053769470429411585 58580442040327102822058689)
              ·
                refine ⟨43935331530245327116544017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58580442040327102822058689 43935331530245327116544017)
                ·
                  refine ⟨32951498647683995337408013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43935331530245327116544017 32951498647683995337408013)
                  ·
                    refine ⟨12356811992881498251528005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32951498647683995337408013 12356811992881498251528005)
                    ·
                      refine ⟨2316902248665280922161501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12356811992881498251528005 2316902248665280922161501)
                      ·
                        rfl

theorem cell23_4512151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_4512151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512151 prefixEnd_4512151 := by exact prefixLift 4512151
  have htrace : WordTrace (prefixWord ++ tailWord_4512151) baseStart_4512151 baseEnd_4512151 := by
    simpa [prefixWord, tailWord_4512151, baseEnd_4512151] using wordTrace_append hprefix tailTrace_4512151
  have hstable : (prefixWord ++ tailWord_4512151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512151).length < 2 ^ (prefixWord ++ tailWord_4512151).sum := by decide
  have hdescent : baseEnd_4512151 < baseStart_4512151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512180 : List Nat := [2, 5, 2, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_4512180 : Nat := 118140960795 + 4512180 * 2 ^ 59
def prefixEnd_4512180 : Nat := 4983230072969 + 3 ^ 40 * 4512180 * 2
def baseEnd_4512180 : Nat := 2316917139604261308698869

theorem tailTrace_4512180 : CollatzResearch.WordTrace tailWord_4512180 prefixEnd_4512180 2316917139604261308698869 := by
  unfold tailWord_4512180
  simp only [CollatzResearch.WordTrace]
  refine ⟨82286362396574976918498997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109715149862099969224665329 82286362396574976918498997)
  ·
    refine ⟨7714346474678904086109281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82286362396574976918498997 7714346474678904086109281)
    ·
      refine ⟨5785759856009178064581961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7714346474678904086109281 5785759856009178064581961)
      ·
        refine ⟨4339319892006883548436471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5785759856009178064581961 4339319892006883548436471)
        ·
          refine ⟨6508979838010325322654707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4339319892006883548436471 6508979838010325322654707)
          ·
            refine ⟨9763469757015487983982061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6508979838010325322654707 9763469757015487983982061)
            ·
              refine ⟨3661301158880807993993273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9763469757015487983982061 3661301158880807993993273)
              ·
                refine ⟨2745975869160605995494955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3661301158880807993993273 2745975869160605995494955)
                ·
                  refine ⟨4118963803740908993242433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2745975869160605995494955 4118963803740908993242433)
                  ·
                    refine ⟨3089222852805681744931825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4118963803740908993242433 3089222852805681744931825)
                    ·
                      refine ⟨2316917139604261308698869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3089222852805681744931825 2316917139604261308698869)
                      ·
                        rfl

theorem cell23_4512180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_4512180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512180 prefixEnd_4512180 := by exact prefixLift 4512180
  have htrace : WordTrace (prefixWord ++ tailWord_4512180) baseStart_4512180 baseEnd_4512180 := by
    simpa [prefixWord, tailWord_4512180, baseEnd_4512180] using wordTrace_append hprefix tailTrace_4512180
  have hstable : (prefixWord ++ tailWord_4512180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512180).length < 2 ^ (prefixWord ++ tailWord_4512180).sum := by decide
  have hdescent : baseEnd_4512180 < baseStart_4512180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512196 : List Nat := [2, 3, 3, 2, 2, 2, 2, 1, 2, 1, 3]
def baseStart_4512196 : Nat := 118140960795 + 4512196 * 2 ^ 59
def prefixEnd_4512196 : Nat := 4983230072969 + 3 ^ 40 * 4512196 * 2
def baseEnd_4512196 : Nat := 2316925355294733246098795

theorem tailTrace_4512196 : CollatzResearch.WordTrace tailWord_4512196 prefixEnd_4512196 2316925355294733246098795 := by
  unfold tailWord_4512196
  simp only [CollatzResearch.WordTrace]
  refine ⟨82286654180545994284790221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109715538907394659046386961 82286654180545994284790221)
  ·
    refine ⟨30857495317704747856796333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82286654180545994284790221 30857495317704747856796333)
    ·
      refine ⟨11571560744139280446298625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30857495317704747856796333 11571560744139280446298625)
      ·
        refine ⟨8678670558104460334723969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11571560744139280446298625 8678670558104460334723969)
        ·
          refine ⟨6509002918578345251042977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8678670558104460334723969 6509002918578345251042977)
          ·
            refine ⟨4881752188933758938282233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6509002918578345251042977 4881752188933758938282233)
            ·
              refine ⟨3661314141700319203711675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4881752188933758938282233 3661314141700319203711675)
              ·
                refine ⟨5491971212550478805567513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3661314141700319203711675 5491971212550478805567513)
                ·
                  refine ⟨4118978409412859104175635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5491971212550478805567513 4118978409412859104175635)
                  ·
                    refine ⟨6178467614119288656263453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4118978409412859104175635 6178467614119288656263453)
                    ·
                      refine ⟨2316925355294733246098795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6178467614119288656263453 2316925355294733246098795)
                      ·
                        rfl

theorem cell23_4512196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_4512196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512196 prefixEnd_4512196 := by exact prefixLift 4512196
  have htrace : WordTrace (prefixWord ++ tailWord_4512196) baseStart_4512196 baseEnd_4512196 := by
    simpa [prefixWord, tailWord_4512196, baseEnd_4512196] using wordTrace_append hprefix tailTrace_4512196
  have hstable : (prefixWord ++ tailWord_4512196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512196).length < 2 ^ (prefixWord ++ tailWord_4512196).sum := by decide
  have hdescent : baseEnd_4512196 < baseStart_4512196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512202 : List Nat := [3, 1, 2, 1, 2, 2, 3, 3, 2, 2, 2]
def baseStart_4512202 : Nat := 118140960795 + 4512202 * 2 ^ 59
def prefixEnd_4512202 : Nat := 4983230072969 + 3 ^ 40 * 4512202 * 2
def baseEnd_4512202 : Nat := 2316928436178660222623767

theorem tailTrace_4512202 : CollatzResearch.WordTrace tailWord_4512202 prefixEnd_4512202 2316928436178660222623767 := by
  unfold tailWord_4512202
  simp only [CollatzResearch.WordTrace]
  refine ⟨41143381799767562898574715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109715684799380167729532573 41143381799767562898574715)
  ·
    refine ⟨61715072699651344347862073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41143381799767562898574715 61715072699651344347862073)
    ·
      refine ⟨46286304524738508260896555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61715072699651344347862073 46286304524738508260896555)
      ·
        refine ⟨69429456787107762391344833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46286304524738508260896555 69429456787107762391344833)
        ·
          refine ⟨52072092590330821793508625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69429456787107762391344833 52072092590330821793508625)
          ·
            refine ⟨39054069442748116345131469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52072092590330821793508625 39054069442748116345131469)
            ·
              refine ⟨14645276041030543629424301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39054069442748116345131469 14645276041030543629424301)
              ·
                refine ⟨5491978515386453861034113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14645276041030543629424301 5491978515386453861034113)
                ·
                  refine ⟨4118983886539840395775585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5491978515386453861034113 4118983886539840395775585)
                  ·
                    refine ⟨3089237914904880296831689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4118983886539840395775585 3089237914904880296831689)
                    ·
                      refine ⟨2316928436178660222623767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3089237914904880296831689 2316928436178660222623767)
                      ·
                        rfl

theorem cell23_4512202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 2, 2, 2].length) (baseStart_4512202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512202 prefixEnd_4512202 := by exact prefixLift 4512202
  have htrace : WordTrace (prefixWord ++ tailWord_4512202) baseStart_4512202 baseEnd_4512202 := by
    simpa [prefixWord, tailWord_4512202, baseEnd_4512202] using wordTrace_append hprefix tailTrace_4512202
  have hstable : (prefixWord ++ tailWord_4512202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512202).length < 2 ^ (prefixWord ++ tailWord_4512202).sum := by decide
  have hdescent : baseEnd_4512202 < baseStart_4512202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512242 : List Nat := [3, 2, 1, 4, 2, 1, 1, 4, 5]
def baseStart_4512242 : Nat := 118140960795 + 4512242 * 2 ^ 59
def prefixEnd_4512242 : Nat := 4983230072969 + 3 ^ 40 * 4512242 * 2
def baseEnd_4512242 : Nat := 257438775044982229569287

theorem tailTrace_4512242 : CollatzResearch.WordTrace tailWord_4512242 prefixEnd_4512242 257438775044982229569287 := by
  unfold tailWord_4512242
  simp only [CollatzResearch.WordTrace]
  refine ⟨41143746529731334606438745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109716657412616892283836653 41143746529731334606438745)
  ·
    refine ⟨30857809897298500954829059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41143746529731334606438745 30857809897298500954829059)
    ·
      refine ⟨46286714845947751432243589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30857809897298500954829059 46286714845947751432243589)
      ·
        refine ⟨8678759033615203393545673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46286714845947751432243589 8678759033615203393545673)
        ·
          refine ⟨6509069275211402545159255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8678759033615203393545673 6509069275211402545159255)
          ·
            refine ⟨9763603912817103817738883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6509069275211402545159255 9763603912817103817738883)
            ·
              refine ⟨14645405869225655726608325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9763603912817103817738883 14645405869225655726608325)
              ·
                refine ⟨2746013600479810448739061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14645405869225655726608325 2746013600479810448739061)
                ·
                  refine ⟨257438775044982229569287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2746013600479810448739061 257438775044982229569287)
                  ·
                    rfl

theorem cell23_4512242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_4512242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512242 prefixEnd_4512242 := by exact prefixLift 4512242
  have htrace : WordTrace (prefixWord ++ tailWord_4512242) baseStart_4512242 baseEnd_4512242 := by
    simpa [prefixWord, tailWord_4512242, baseEnd_4512242] using wordTrace_append hprefix tailTrace_4512242
  have hstable : (prefixWord ++ tailWord_4512242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512242).length < 2 ^ (prefixWord ++ tailWord_4512242).sum := by decide
  have hdescent : baseEnd_4512242 < baseStart_4512242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512271 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 6]
def baseStart_4512271 : Nat := 118140960795 + 4512271 * 2 ^ 59
def prefixEnd_4512271 : Nat := 4983230072969 + 3 ^ 40 * 4512271 * 2
def baseEnd_4512271 : Nat := 2316963866343820452660949

theorem tailTrace_4512271 : CollatzResearch.WordTrace tailWord_4512271 prefixEnd_4512271 2316963866343820452660949 := by
  unfold tailWord_4512271
  simp only [CollatzResearch.WordTrace]
  refine ⟨164576043835820276378560667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109717362557213517585707111 164576043835820276378560667)
  ·
    refine ⟨246864065753730414567841001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164576043835820276378560667 246864065753730414567841001)
    ·
      refine ⟨185148049315297810925880751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246864065753730414567841001 185148049315297810925880751)
      ·
        refine ⟨277722073972946716388821127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185148049315297810925880751 277722073972946716388821127)
        ·
          refine ⟨416583110959420074583231691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277722073972946716388821127 416583110959420074583231691)
          ·
            refine ⟨624874666439130111874847537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416583110959420074583231691 624874666439130111874847537)
            ·
              refine ⟨468655999829347583906135653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 624874666439130111874847537 468655999829347583906135653)
              ·
                refine ⟨87872999968002671982400435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 468655999829347583906135653 87872999968002671982400435)
                ·
                  refine ⟨131809499952004007973600653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87872999968002671982400435 131809499952004007973600653)
                  ·
                    refine ⟨49428562482001502990100245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 131809499952004007973600653 49428562482001502990100245)
                    ·
                      refine ⟨2316963866343820452660949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49428562482001502990100245 2316963866343820452660949)
                      ·
                        rfl

theorem cell23_4512271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_4512271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512271 prefixEnd_4512271 := by exact prefixLift 4512271
  have htrace : WordTrace (prefixWord ++ tailWord_4512271) baseStart_4512271 baseEnd_4512271 := by
    simpa [prefixWord, tailWord_4512271, baseEnd_4512271] using wordTrace_append hprefix tailTrace_4512271
  have hstable : (prefixWord ++ tailWord_4512271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512271).length < 2 ^ (prefixWord ++ tailWord_4512271).sum := by decide
  have hdescent : baseEnd_4512271 < baseStart_4512271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512281 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 10]
def baseStart_4512281 : Nat := 118140960795 + 4512281 * 2 ^ 59
def prefixEnd_4512281 : Nat := 4983230072969 + 3 ^ 40 * 4512281 * 2
def baseEnd_4512281 : Nat := 257441000127818379281767

theorem tailTrace_4512281 : CollatzResearch.WordTrace tailWord_4512281 prefixEnd_4512281 257441000127818379281767 := by
  unfold tailWord_4512281
  simp only [CollatzResearch.WordTrace]
  refine ⟨164576408565784048086424697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109717605710522698724283131 164576408565784048086424697)
  ·
    refine ⟨123432306424338036064818523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164576408565784048086424697 123432306424338036064818523)
    ·
      refine ⟨185148459636507054097227785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123432306424338036064818523 185148459636507054097227785)
      ·
        refine ⟨138861344727380290572920839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185148459636507054097227785 138861344727380290572920839)
        ·
          refine ⟨208292017091070435859381259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138861344727380290572920839 208292017091070435859381259)
          ·
            refine ⟨312438025636605653789071889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208292017091070435859381259 312438025636605653789071889)
            ·
              refine ⟨234328519227454240341803917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 312438025636605653789071889 234328519227454240341803917)
              ·
                refine ⟨87873194710295340128176469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234328519227454240341803917 87873194710295340128176469)
                ·
                  refine ⟨257441000127818379281767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 87873194710295340128176469 257441000127818379281767)
                  ·
                    rfl

theorem cell23_4512281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 10].length) (baseStart_4512281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512281 prefixEnd_4512281 := by exact prefixLift 4512281
  have htrace : WordTrace (prefixWord ++ tailWord_4512281) baseStart_4512281 baseEnd_4512281 := by
    simpa [prefixWord, tailWord_4512281, baseEnd_4512281] using wordTrace_append hprefix tailTrace_4512281
  have hstable : (prefixWord ++ tailWord_4512281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512281).length < 2 ^ (prefixWord ++ tailWord_4512281).sum := by decide
  have hdescent : baseEnd_4512281 < baseStart_4512281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512328 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 3, 5]
def baseStart_4512328 : Nat := 118140960795 + 4512328 * 2 ^ 59
def prefixEnd_4512328 : Nat := 4983230072969 + 3 ^ 40 * 4512328 * 2
def baseEnd_4512328 : Nat := 772331044913708909882729

theorem tailTrace_4512328 : CollatzResearch.WordTrace tailWord_4512328 prefixEnd_4512328 772331044913708909882729 := by
  unfold tailWord_4512328
  simp only [CollatzResearch.WordTrace]
  refine ⟨82289061398306887556692819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109718748531075850075590425 82289061398306887556692819)
  ·
    refine ⟨123433592097460331335039229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82289061398306887556692819 123433592097460331335039229)
    ·
      refine ⟨46287597036547624250639711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123433592097460331335039229 46287597036547624250639711)
      ·
        refine ⟨69431395554821436375959567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46287597036547624250639711 69431395554821436375959567)
        ·
          refine ⟨104147093332232154563939351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69431395554821436375959567 104147093332232154563939351)
          ·
            refine ⟨156220639998348231845909027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104147093332232154563939351 156220639998348231845909027)
            ·
              refine ⟨234330959997522347768863541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156220639998348231845909027 234330959997522347768863541)
              ·
                refine ⟨21968527499767720103330957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 234330959997522347768863541 21968527499767720103330957)
                ·
                  refine ⟨8238197812412895038749109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21968527499767720103330957 8238197812412895038749109)
                  ·
                    refine ⟨772331044913708909882729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8238197812412895038749109 772331044913708909882729)
                    ·
                      rfl

theorem cell23_4512328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_4512328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512328 prefixEnd_4512328 := by exact prefixLift 4512328
  have htrace : WordTrace (prefixWord ++ tailWord_4512328) baseStart_4512328 baseEnd_4512328 := by
    simpa [prefixWord, tailWord_4512328, baseEnd_4512328] using wordTrace_append hprefix tailTrace_4512328
  have hstable : (prefixWord ++ tailWord_4512328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512328).length < 2 ^ (prefixWord ++ tailWord_4512328).sum := by decide
  have hdescent : baseEnd_4512328 < baseStart_4512328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512335 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 1, 5, 2]
def baseStart_4512335 : Nat := 118140960795 + 4512335 * 2 ^ 59
def prefixEnd_4512335 : Nat := 4983230072969 + 3 ^ 40 * 4512335 * 2
def baseEnd_4512335 : Nat := 2316996729105708202260655

theorem tailTrace_4512335 : CollatzResearch.WordTrace tailWord_4512335 prefixEnd_4512335 2316996729105708202260655 := by
  unfold tailWord_4512335
  simp only [CollatzResearch.WordTrace]
  refine ⟨164578378107588415308890459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109718918738392276872593639 164578378107588415308890459)
  ·
    refine ⟨246867567161382622963335689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164578378107588415308890459 246867567161382622963335689)
    ·
      refine ⟨185150675371036967222501767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246867567161382622963335689 185150675371036967222501767)
      ·
        refine ⟨277726013056555450833752651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185150675371036967222501767 277726013056555450833752651)
        ·
          refine ⟨416589019584833176250628977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277726013056555450833752651 416589019584833176250628977)
          ·
            refine ⟨312441764688624882187971733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 416589019584833176250628977 312441764688624882187971733)
            ·
              refine ⟨14645707719779291352561175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 312441764688624882187971733 14645707719779291352561175)
              ·
                refine ⟨21968561579668937028841763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14645707719779291352561175 21968561579668937028841763)
                ·
                  refine ⟨32952842369503405543262645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21968561579668937028841763 32952842369503405543262645)
                  ·
                    refine ⟨3089328972140944269680873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32952842369503405543262645 3089328972140944269680873)
                    ·
                      refine ⟨2316996729105708202260655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3089328972140944269680873 2316996729105708202260655)
                      ·
                        rfl

theorem cell23_4512335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 5, 2].length) (baseStart_4512335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512335 prefixEnd_4512335 := by exact prefixLift 4512335
  have htrace : WordTrace (prefixWord ++ tailWord_4512335) baseStart_4512335 baseEnd_4512335 := by
    simpa [prefixWord, tailWord_4512335, baseEnd_4512335] using wordTrace_append hprefix tailTrace_4512335
  have hstable : (prefixWord ++ tailWord_4512335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512335).length < 2 ^ (prefixWord ++ tailWord_4512335).sum := by decide
  have hdescent : baseEnd_4512335 < baseStart_4512335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512402 : List Nat := [3, 2, 3, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_4512402 : Nat := 118140960795 + 4512402 * 2 ^ 59
def prefixEnd_4512402 : Nat := 4983230072969 + 3 ^ 40 * 4512402 * 2
def baseEnd_4512402 : Nat := 2317031132309559440122847

theorem tailTrace_4512402 : CollatzResearch.WordTrace tailWord_4512402 prefixEnd_4512402 2317031132309559440122847 := by
  unfold tailWord_4512402
  simp only [CollatzResearch.WordTrace]
  refine ⟨41145205449586421437894865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109720547865563790501052973 41145205449586421437894865)
  ·
    refine ⟨30858904087189816078421149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41145205449586421437894865 30858904087189816078421149)
    ·
      refine ⟨11572089032696181029407931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30858904087189816078421149 11572089032696181029407931)
      ·
        refine ⟨17358133549044271544111897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11572089032696181029407931 17358133549044271544111897)
        ·
          refine ⟨13018600161783203658083923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17358133549044271544111897 13018600161783203658083923)
          ·
            refine ⟨19527900242674805487125885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13018600161783203658083923 19527900242674805487125885)
            ·
              refine ⟨7322962591003052057672207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19527900242674805487125885 7322962591003052057672207)
              ·
                refine ⟨10984443886504578086508311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7322962591003052057672207 10984443886504578086508311)
                ·
                  refine ⟨16476665829756867129762467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10984443886504578086508311 16476665829756867129762467)
                  ·
                    refine ⟨24714998744635300694643701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16476665829756867129762467 24714998744635300694643701)
                    ·
                      refine ⟨2317031132309559440122847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24714998744635300694643701 2317031132309559440122847)
                      ·
                        rfl

theorem cell23_4512402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_4512402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512402 prefixEnd_4512402 := by exact prefixLift 4512402
  have htrace : WordTrace (prefixWord ++ tailWord_4512402) baseStart_4512402 baseEnd_4512402 := by
    simpa [prefixWord, tailWord_4512402, baseEnd_4512402] using wordTrace_append hprefix tailTrace_4512402
  have hstable : (prefixWord ++ tailWord_4512402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512402).length < 2 ^ (prefixWord ++ tailWord_4512402).sum := by decide
  have hdescent : baseEnd_4512402 < baseStart_4512402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512410 : List Nat := [3, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3]
def baseStart_4512410 : Nat := 118140960795 + 4512410 * 2 ^ 59
def prefixEnd_4512410 : Nat := 4983230072969 + 3 ^ 40 * 4512410 * 2
def baseEnd_4512410 : Nat := 2317035240154795408822811

theorem tailTrace_4512410 : CollatzResearch.WordTrace tailWord_4512410 prefixEnd_4512410 2317035240154795408822811 := by
  unfold tailWord_4512410
  simp only [CollatzResearch.WordTrace]
  refine ⟨41145278395579175779467671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109720742388211135411913789 41145278395579175779467671)
  ·
    refine ⟨61717917593368763669201507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41145278395579175779467671 61717917593368763669201507)
    ·
      refine ⟨92576876390053145503802261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61717917593368763669201507 92576876390053145503802261)
      ·
        refine ⟨4339541080783741195490731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 92576876390053145503802261 4339541080783741195490731)
        ·
          refine ⟨6509311621175611793236097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4339541080783741195490731 6509311621175611793236097)
          ·
            refine ⟨4881983715881708844927073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6509311621175611793236097 4881983715881708844927073)
            ·
              refine ⟨3661487786911281633695305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4881983715881708844927073 3661487786911281633695305)
              ·
                refine ⟨2746115840183461225271479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3661487786911281633695305 2746115840183461225271479)
                ·
                  refine ⟨4119173760275191837907219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2746115840183461225271479 4119173760275191837907219)
                  ·
                    refine ⟨6178760640412787756860829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4119173760275191837907219 6178760640412787756860829)
                    ·
                      refine ⟨2317035240154795408822811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6178760640412787756860829 2317035240154795408822811)
                      ·
                        rfl

theorem cell23_4512410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_4512410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512410 prefixEnd_4512410 := by exact prefixLift 4512410
  have htrace : WordTrace (prefixWord ++ tailWord_4512410) baseStart_4512410 baseEnd_4512410 := by
    simpa [prefixWord, tailWord_4512410, baseEnd_4512410] using wordTrace_append hprefix tailTrace_4512410
  have hstable : (prefixWord ++ tailWord_4512410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512410).length < 2 ^ (prefixWord ++ tailWord_4512410).sum := by decide
  have hdescent : baseEnd_4512410 < baseStart_4512410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512425 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 2, 7, 2]
def baseStart_4512425 : Nat := 118140960795 + 4512425 * 2 ^ 59
def prefixEnd_4512425 : Nat := 4983230072969 + 3 ^ 40 * 4512425 * 2
def baseEnd_4512425 : Nat := 2317042942364612850135241

theorem tailTrace_4512425 : CollatzResearch.WordTrace tailWord_4512425 prefixEnd_4512425 2317042942364612850135241 := by
  unfold tailWord_4512425
  simp only [CollatzResearch.WordTrace]
  refine ⟨164581660677262360679666729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109721107118174907119777819 164581660677262360679666729)
  ·
    refine ⟨123436245507946770509750047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164581660677262360679666729 123436245507946770509750047)
    ·
      refine ⟨185154368261920155764625071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123436245507946770509750047 185154368261920155764625071)
      ·
        refine ⟨277731552392880233646937607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185154368261920155764625071 277731552392880233646937607)
        ·
          refine ⟨416597328589320350470406411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277731552392880233646937607 416597328589320350470406411)
          ·
            refine ⟨624895992883980525705609617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416597328589320350470406411 624895992883980525705609617)
            ·
              refine ⟨468671994662985394279207213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 624895992883980525705609617 468671994662985394279207213)
              ·
                refine ⟨175751997998619522854702705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 468671994662985394279207213 175751997998619522854702705)
                ·
                  refine ⟨131813998498964642141027029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175751997998619522854702705 131813998498964642141027029)
                  ·
                    refine ⟨3089390589819483800180321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 131813998498964642141027029 3089390589819483800180321)
                    ·
                      refine ⟨2317042942364612850135241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3089390589819483800180321 2317042942364612850135241)
                      ·
                        rfl

theorem cell23_4512425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 7, 2].length) (baseStart_4512425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512425 prefixEnd_4512425 := by exact prefixLift 4512425
  have htrace : WordTrace (prefixWord ++ tailWord_4512425) baseStart_4512425 baseEnd_4512425 := by
    simpa [prefixWord, tailWord_4512425, baseEnd_4512425] using wordTrace_append hprefix tailTrace_4512425
  have hstable : (prefixWord ++ tailWord_4512425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512425).length < 2 ^ (prefixWord ++ tailWord_4512425).sum := by decide
  have hdescent : baseEnd_4512425 < baseStart_4512425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512442 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2]
def baseStart_4512442 : Nat := 118140960795 + 4512442 * 2 ^ 59
def prefixEnd_4512442 : Nat := 4983230072969 + 3 ^ 40 * 4512442 * 2
def baseEnd_4512442 : Nat := 2317051671535739283622663

theorem tailTrace_4512442 : CollatzResearch.WordTrace tailWord_4512442 prefixEnd_4512442 2317051671535739283622663 := by
  unfold tailWord_4512442
  simp only [CollatzResearch.WordTrace]
  refine ⟨41145570179550193145758895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109721520478800515055357053 41145570179550193145758895)
  ·
    refine ⟨61718355269325289718638343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41145570179550193145758895 61718355269325289718638343)
    ·
      refine ⟨92577532903987934577957515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61718355269325289718638343 92577532903987934577957515)
      ·
        refine ⟨138866299355981901866936273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92577532903987934577957515 138866299355981901866936273)
        ·
          refine ⟨104149724516986426400202205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138866299355981901866936273 104149724516986426400202205)
          ·
            refine ⟨39056146693869909900075827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104149724516986426400202205 39056146693869909900075827)
            ·
              refine ⟨58584220040804864850113741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39056146693869909900075827 58584220040804864850113741)
              ·
                refine ⟨21969082515301824318792653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58584220040804864850113741 21969082515301824318792653)
                ·
                  refine ⟨8238405943238184119547245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21969082515301824318792653 8238405943238184119547245)
                  ·
                    refine ⟨3089402228714319044830217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8238405943238184119547245 3089402228714319044830217)
                    ·
                      refine ⟨2317051671535739283622663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3089402228714319044830217 2317051671535739283622663)
                      ·
                        rfl

theorem cell23_4512442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2].length) (baseStart_4512442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512442 prefixEnd_4512442 := by exact prefixLift 4512442
  have htrace : WordTrace (prefixWord ++ tailWord_4512442) baseStart_4512442 baseEnd_4512442 := by
    simpa [prefixWord, tailWord_4512442, baseEnd_4512442] using wordTrace_append hprefix tailTrace_4512442
  have hstable : (prefixWord ++ tailWord_4512442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512442).length < 2 ^ (prefixWord ++ tailWord_4512442).sum := by decide
  have hdescent : baseEnd_4512442 < baseStart_4512442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512489 : List Nat := [1, 2, 1, 1, 1, 2, 4, 5, 2, 2, 2]
def baseStart_4512489 : Nat := 118140960795 + 4512489 * 2 ^ 59
def prefixEnd_4512489 : Nat := 4983230072969 + 3 ^ 40 * 4512489 * 2
def baseEnd_4512489 : Nat := 2317075805126500599734947

theorem tailTrace_4512489 : CollatzResearch.WordTrace tailWord_4512489 prefixEnd_4512489 2317075805126500599734947 := by
  unfold tailWord_4512489
  simp only [CollatzResearch.WordTrace]
  refine ⟨164583994949030499609996521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109722663299353666406664347 164583994949030499609996521)
  ·
    refine ⟨123437996211772874707497391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164583994949030499609996521 123437996211772874707497391)
    ·
      refine ⟨185156994317659312061246087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123437996211772874707497391 185156994317659312061246087)
      ·
        refine ⟨277735491476488968091869131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185156994317659312061246087 277735491476488968091869131)
        ·
          refine ⟨416603237214733452137803697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277735491476488968091869131 416603237214733452137803697)
          ·
            refine ⟨312452427911050089103352773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 416603237214733452137803697 312452427911050089103352773)
            ·
              refine ⟨58584830233321891706878645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 312452427911050089103352773 58584830233321891706878645)
              ·
                refine ⟨5492327834373927347519873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58584830233321891706878645 5492327834373927347519873)
                ·
                  refine ⟨4119245875780445510639905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5492327834373927347519873 4119245875780445510639905)
                  ·
                    refine ⟨3089434406835334132979929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4119245875780445510639905 3089434406835334132979929)
                    ·
                      refine ⟨2317075805126500599734947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3089434406835334132979929 2317075805126500599734947)
                      ·
                        rfl

theorem cell23_4512489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 2, 2].length) (baseStart_4512489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512489 prefixEnd_4512489 := by exact prefixLift 4512489
  have htrace : WordTrace (prefixWord ++ tailWord_4512489) baseStart_4512489 baseEnd_4512489 := by
    simpa [prefixWord, tailWord_4512489, baseEnd_4512489] using wordTrace_append hprefix tailTrace_4512489
  have hstable : (prefixWord ++ tailWord_4512489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512489).length < 2 ^ (prefixWord ++ tailWord_4512489).sum := by decide
  have hdescent : baseEnd_4512489 < baseStart_4512489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512495 : List Nat := [1, 1, 2, 1, 5, 2, 2, 2, 7]
def baseStart_4512495 : Nat := 118140960795 + 4512495 * 2 ^ 59
def prefixEnd_4512495 : Nat := 4983230072969 + 3 ^ 40 * 4512495 * 2
def baseEnd_4512495 : Nat := 257453209556714175139991

theorem tailTrace_4512495 : CollatzResearch.WordTrace tailWord_4512495 prefixEnd_4512495 257453209556714175139991 := by
  unfold tailWord_4512495
  simp only [CollatzResearch.WordTrace]
  refine ⟨164584213787008762634714939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109722809191339175089809959 164584213787008762634714939)
  ·
    refine ⟨246876320680513143952072409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164584213787008762634714939 246876320680513143952072409)
    ·
      refine ⟨185157240510384857964054307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246876320680513143952072409 185157240510384857964054307)
      ·
        refine ⟨277735860765577286946081461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185157240510384857964054307 277735860765577286946081461)
        ·
          refine ⟨26037736946772870651195137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 277735860765577286946081461 26037736946772870651195137)
          ·
            refine ⟨19528302710079652988396353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26037736946772870651195137 19528302710079652988396353)
            ·
              refine ⟨14646227032559739741297265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19528302710079652988396353 14646227032559739741297265)
              ·
                refine ⟨10984670274419804805972949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14646227032559739741297265 10984670274419804805972949)
                ·
                  refine ⟨257453209556714175139991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10984670274419804805972949 257453209556714175139991)
                  ·
                    rfl

theorem cell23_4512495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 7].length) (baseStart_4512495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512495 prefixEnd_4512495 := by exact prefixLift 4512495
  have htrace : WordTrace (prefixWord ++ tailWord_4512495) baseStart_4512495 baseEnd_4512495 := by
    simpa [prefixWord, tailWord_4512495, baseEnd_4512495] using wordTrace_append hprefix tailTrace_4512495
  have hstable : (prefixWord ++ tailWord_4512495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512495).length < 2 ^ (prefixWord ++ tailWord_4512495).sum := by decide
  have hdescent : baseEnd_4512495 < baseStart_4512495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512505 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 1, 5, 3]
def baseStart_4512505 : Nat := 118140960795 + 4512505 * 2 ^ 59
def prefixEnd_4512505 : Nat := 4983230072969 + 3 ^ 40 * 4512505 * 2
def baseEnd_4512505 : Nat := 2317084020816972537134873

theorem tailTrace_4512505 : CollatzResearch.WordTrace tailWord_4512505 prefixEnd_4512505 2317084020816972537134873 := by
  unfold tailWord_4512505
  simp only [CollatzResearch.WordTrace]
  refine ⟨164584578516972534342578969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109723052344648356228385979 164584578516972534342578969)
  ·
    refine ⟨123438433887729400756934227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164584578516972534342578969 123438433887729400756934227)
    ·
      refine ⟨185157650831594101135401341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123438433887729400756934227 185157650831594101135401341)
      ·
        refine ⟨69434119061847787925775503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185157650831594101135401341 69434119061847787925775503)
        ·
          refine ⟨104151178592771681888663255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69434119061847787925775503 104151178592771681888663255)
          ·
            refine ⟨156226767889157522832994883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104151178592771681888663255 156226767889157522832994883)
            ·
              refine ⟨234340151833736284249492325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156226767889157522832994883 234340151833736284249492325)
              ·
                refine ⟨43938778468825553296779811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 234340151833736284249492325 43938778468825553296779811)
                ·
                  refine ⟨65908167703238329945169717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43938778468825553296779811 65908167703238329945169717)
                  ·
                    refine ⟨6178890722178593432359661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65908167703238329945169717 6178890722178593432359661)
                    ·
                      refine ⟨2317084020816972537134873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6178890722178593432359661 2317084020816972537134873)
                      ·
                        rfl

theorem cell23_4512505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_4512505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512505 prefixEnd_4512505 := by exact prefixLift 4512505
  have htrace : WordTrace (prefixWord ++ tailWord_4512505) baseStart_4512505 baseEnd_4512505 := by
    simpa [prefixWord, tailWord_4512505, baseEnd_4512505] using wordTrace_append hprefix tailTrace_4512505
  have hstable : (prefixWord ++ tailWord_4512505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512505).length < 2 ^ (prefixWord ++ tailWord_4512505).sum := by decide
  have hdescent : baseEnd_4512505 < baseStart_4512505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512580 : List Nat := [2, 3, 4, 2, 1, 2, 2, 2, 5]
def baseStart_4512580 : Nat := 118140960795 + 4512580 * 2 ^ 59
def prefixEnd_4512580 : Nat := 4983230072969 + 3 ^ 40 * 4512580 * 2
def baseEnd_4512580 : Nat := 257458059096228860410781

theorem tailTrace_4512580 : CollatzResearch.WordTrace tailWord_4512580 prefixEnd_4512580 257458059096228860410781 := by
  unfold tailWord_4512580
  simp only [CollatzResearch.WordTrace]
  refine ⟨82293656995850411075779597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109724875994467214767706129 82293656995850411075779597)
  ·
    refine ⟨30860121373443904153417349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82293656995850411075779597 30860121373443904153417349)
    ·
      refine ⟨5786272757520732028765753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30860121373443904153417349 5786272757520732028765753)
      ·
        refine ⟨4339704568140549021574315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5786272757520732028765753 4339704568140549021574315)
        ·
          refine ⟨6509556852210823532361473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4339704568140549021574315 6509556852210823532361473)
          ·
            refine ⟨4882167639158117649271105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6509556852210823532361473 4882167639158117649271105)
            ·
              refine ⟨3661625729368588236953329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4882167639158117649271105 3661625729368588236953329)
              ·
                refine ⟨2746219297026441177714997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3661625729368588236953329 2746219297026441177714997)
                ·
                  refine ⟨257458059096228860410781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2746219297026441177714997 257458059096228860410781)
                  ·
                    rfl

theorem cell23_4512580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_4512580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512580 prefixEnd_4512580 := by exact prefixLift 4512580
  have htrace : WordTrace (prefixWord ++ tailWord_4512580) baseStart_4512580 baseEnd_4512580 := by
    simpa [prefixWord, tailWord_4512580, baseEnd_4512580] using wordTrace_append hprefix tailTrace_4512580
  have hstable : (prefixWord ++ tailWord_4512580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512580).length < 2 ^ (prefixWord ++ tailWord_4512580).sum := by decide
  have hdescent : baseEnd_4512580 < baseStart_4512580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512596 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 2, 4, 2]
def baseStart_4512596 : Nat := 118140960795 + 4512596 * 2 ^ 59
def prefixEnd_4512596 : Nat := 4983230072969 + 3 ^ 40 * 4512596 * 2
def baseEnd_4512596 : Nat := 2317130747556531681096955

theorem tailTrace_4512596 : CollatzResearch.WordTrace tailWord_4512596 prefixEnd_4512596 2317130747556531681096955 := by
  unfold tailWord_4512596
  simp only [CollatzResearch.WordTrace]
  refine ⟨82293948779821428442070821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109725265039761904589427761 82293948779821428442070821)
  ·
    refine ⟨15430115396216517832888279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82293948779821428442070821 15430115396216517832888279)
    ·
      refine ⟨23145173094324776749332419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15430115396216517832888279 23145173094324776749332419)
      ·
        refine ⟨34717759641487165123998629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23145173094324776749332419 34717759641487165123998629)
        ·
          refine ⟨6509579932778843460749743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34717759641487165123998629 6509579932778843460749743)
          ·
            refine ⟨9764369899168265191124615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6509579932778843460749743 9764369899168265191124615)
            ·
              refine ⟨14646554848752397786686923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9764369899168265191124615 14646554848752397786686923)
              ·
                refine ⟨21969832273128596680030385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14646554848752397786686923 21969832273128596680030385)
                ·
                  refine ⟨16477374204846447510022789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21969832273128596680030385 16477374204846447510022789)
                  ·
                    refine ⟨3089507663408708908129273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16477374204846447510022789 3089507663408708908129273)
                    ·
                      refine ⟨2317130747556531681096955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3089507663408708908129273 2317130747556531681096955)
                      ·
                        rfl

theorem cell23_4512596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_4512596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512596 prefixEnd_4512596 := by exact prefixLift 4512596
  have htrace : WordTrace (prefixWord ++ tailWord_4512596) baseStart_4512596 baseEnd_4512596 := by
    simpa [prefixWord, tailWord_4512596, baseEnd_4512596] using wordTrace_append hprefix tailTrace_4512596
  have hstable : (prefixWord ++ tailWord_4512596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512596).length < 2 ^ (prefixWord ++ tailWord_4512596).sum := by decide
  have hdescent : baseEnd_4512596 < baseStart_4512596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512602 : List Nat := [3, 1, 1, 2, 1, 4, 2, 3, 6]
def baseStart_4512602 : Nat := 118140960795 + 4512602 * 2 ^ 59
def prefixEnd_4512602 : Nat := 4983230072969 + 3 ^ 40 * 4512602 * 2
def baseEnd_4512602 : Nat := 257459314271162073069103

theorem tailTrace_4512602 : CollatzResearch.WordTrace tailWord_4512602 prefixEnd_4512602 257459314271162073069103 := by
  unfold tailWord_4512602
  simp only [CollatzResearch.WordTrace]
  refine ⟨41147029099405279977215015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109725410931747413272573373 41147029099405279977215015)
  ·
    refine ⟨61720543649107919965822523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41147029099405279977215015 61720543649107919965822523)
    ·
      refine ⟨92580815473661879948733785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61720543649107919965822523 92580815473661879948733785)
      ·
        refine ⟨69435611605246409961550339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92580815473661879948733785 69435611605246409961550339)
        ·
          refine ⟨104153417407869614942325509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69435611605246409961550339 104153417407869614942325509)
          ·
            refine ⟨19528765763975552801686033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104153417407869614942325509 19528765763975552801686033)
            ·
              refine ⟨14646574322981664601264525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19528765763975552801686033 14646574322981664601264525)
              ·
                refine ⟨5492465371118124225474197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14646574322981664601264525 5492465371118124225474197)
                ·
                  refine ⟨257459314271162073069103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5492465371118124225474197 257459314271162073069103)
                  ·
                    rfl

theorem cell23_4512602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 6].length) (baseStart_4512602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512602 prefixEnd_4512602 := by exact prefixLift 4512602
  have htrace : WordTrace (prefixWord ++ tailWord_4512602) baseStart_4512602 baseEnd_4512602 := by
    simpa [prefixWord, tailWord_4512602, baseEnd_4512602] using wordTrace_append hprefix tailTrace_4512602
  have hstable : (prefixWord ++ tailWord_4512602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512602).length < 2 ^ (prefixWord ++ tailWord_4512602).sum := by decide
  have hdescent : baseEnd_4512602 < baseStart_4512602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512616 : List Nat := [2, 1, 4, 2, 1, 4, 1, 1, 2, 2, 3]
def baseStart_4512616 : Nat := 118140960795 + 4512616 * 2 ^ 59
def prefixEnd_4512616 : Nat := 4983230072969 + 3 ^ 40 * 4512616 * 2
def baseEnd_4512616 : Nat := 2317141017169621602846863

theorem tailTrace_4512616 : CollatzResearch.WordTrace tailWord_4512616 prefixEnd_4512616 2317141017169621602846863 := by
  unfold tailWord_4512616
  simp only [CollatzResearch.WordTrace]
  refine ⟨82294313509785200149934851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109725751346380266866579801 82294313509785200149934851)
  ·
    refine ⟨123441470264677800224902277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82294313509785200149934851 123441470264677800224902277)
    ·
      refine ⟨23145275674627087542169177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123441470264677800224902277 23145275674627087542169177)
      ·
        refine ⟨17358956755970315656626883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23145275674627087542169177 17358956755970315656626883)
        ·
          refine ⟨26038435133955473484940325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17358956755970315656626883 26038435133955473484940325)
          ·
            refine ⟨4882206587616651278426311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26038435133955473484940325 4882206587616651278426311)
            ·
              refine ⟨7323309881424976917639467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4882206587616651278426311 7323309881424976917639467)
              ·
                refine ⟨10984964822137465376459201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7323309881424976917639467 10984964822137465376459201)
                ·
                  refine ⟨8238723616603099032344401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10984964822137465376459201 8238723616603099032344401)
                  ·
                    refine ⟨6179042712452324274258301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8238723616603099032344401 6179042712452324274258301)
                    ·
                      refine ⟨2317141017169621602846863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6179042712452324274258301 2317141017169621602846863)
                      ·
                        rfl

theorem cell23_4512616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_4512616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512616 prefixEnd_4512616 := by exact prefixLift 4512616
  have htrace : WordTrace (prefixWord ++ tailWord_4512616) baseStart_4512616 baseEnd_4512616 := by
    simpa [prefixWord, tailWord_4512616, baseEnd_4512616] using wordTrace_append hprefix tailTrace_4512616
  have hstable : (prefixWord ++ tailWord_4512616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512616).length < 2 ^ (prefixWord ++ tailWord_4512616).sum := by decide
  have hdescent : baseEnd_4512616 < baseStart_4512616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512639 : List Nat := [1, 1, 2, 2, 1, 1, 4, 4, 2, 3, 2]
def baseStart_4512639 : Nat := 118140960795 + 4512639 * 2 ^ 59
def prefixEnd_4512639 : Nat := 4983230072969 + 3 ^ 40 * 4512639 * 2
def baseEnd_4512639 : Nat := 2317152827224675012859257

theorem tailTrace_4512639 : CollatzResearch.WordTrace tailWord_4512639 prefixEnd_4512639 2317152827224675012859257 := by
  unfold tailWord_4512639
  simp only [CollatzResearch.WordTrace]
  refine ⟨164589465898487075227956971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109726310598991383485304647 164589465898487075227956971)
  ·
    refine ⟨246884198847730612841935457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164589465898487075227956971 246884198847730612841935457)
    ·
      refine ⟨185163149135797959631451593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246884198847730612841935457 185163149135797959631451593)
      ·
        refine ⟨138872361851848469723588695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185163149135797959631451593 138872361851848469723588695)
        ·
          refine ⟨208308542777772704585383043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138872361851848469723588695 208308542777772704585383043)
          ·
            refine ⟨312462814166659056878074565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208308542777772704585383043 312462814166659056878074565)
            ·
              refine ⟨58586777656248573164638981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 312462814166659056878074565 58586777656248573164638981)
              ·
                refine ⟨10985020810546607468369809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58586777656248573164638981 10985020810546607468369809)
                ·
                  refine ⟨8238765607909955601277357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10985020810546607468369809 8238765607909955601277357)
                  ·
                    refine ⟨3089537102966233350479009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8238765607909955601277357 3089537102966233350479009)
                    ·
                      refine ⟨2317152827224675012859257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3089537102966233350479009 2317152827224675012859257)
                      ·
                        rfl

theorem cell23_4512639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 3, 2].length) (baseStart_4512639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512639 prefixEnd_4512639 := by exact prefixLift 4512639
  have htrace : WordTrace (prefixWord ++ tailWord_4512639) baseStart_4512639 baseEnd_4512639 := by
    simpa [prefixWord, tailWord_4512639, baseEnd_4512639] using wordTrace_append hprefix tailTrace_4512639
  have hstable : (prefixWord ++ tailWord_4512639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512639).length < 2 ^ (prefixWord ++ tailWord_4512639).sum := by decide
  have hdescent : baseEnd_4512639 < baseStart_4512639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512652 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 5, 1, 4]
def baseStart_4512652 : Nat := 118140960795 + 4512652 * 2 ^ 59
def prefixEnd_4512652 : Nat := 4983230072969 + 3 ^ 40 * 4512652 * 2
def baseEnd_4512652 : Nat := 2317159502473183461996697

theorem tailTrace_4512652 : CollatzResearch.WordTrace tailWord_4512652 prefixEnd_4512652 2317159502473183461996697 := by
  unfold tailWord_4512652
  simp only [CollatzResearch.WordTrace]
  refine ⟨82294970023719989224090105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109726626698293318965453473 82294970023719989224090105)
  ·
    refine ⟨61721227517789991918067579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82294970023719989224090105 61721227517789991918067579)
    ·
      refine ⟨92581841276684987877101369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61721227517789991918067579 92581841276684987877101369)
      ·
        refine ⟨69436380957513740907826027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92581841276684987877101369 69436380957513740907826027)
        ·
          refine ⟨104154571436270611361739041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69436380957513740907826027 104154571436270611361739041)
          ·
            refine ⟨78115928577202958521304281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104154571436270611361739041 78115928577202958521304281)
            ·
              refine ⟨58586946432902218890978211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78115928577202958521304281 58586946432902218890978211)
              ·
                refine ⟨87880419649353328336467317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58586946432902218890978211 87880419649353328336467317)
                ·
                  refine ⟨8238789342126874531543811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87880419649353328336467317 8238789342126874531543811)
                  ·
                    refine ⟨12358184013190311797315717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8238789342126874531543811 12358184013190311797315717)
                    ·
                      refine ⟨2317159502473183461996697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12358184013190311797315717 2317159502473183461996697)
                      ·
                        rfl

theorem cell23_4512652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_4512652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512652 prefixEnd_4512652 := by exact prefixLift 4512652
  have htrace : WordTrace (prefixWord ++ tailWord_4512652) baseStart_4512652 baseEnd_4512652 := by
    simpa [prefixWord, tailWord_4512652, baseEnd_4512652] using wordTrace_append hprefix tailTrace_4512652
  have hstable : (prefixWord ++ tailWord_4512652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512652).length < 2 ^ (prefixWord ++ tailWord_4512652).sum := by decide
  have hdescent : baseEnd_4512652 < baseStart_4512652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512666 : List Nat := [3, 1, 1, 4, 3, 1, 2, 2, 1, 5]
def baseStart_4512666 : Nat := 118140960795 + 4512666 * 2 ^ 59
def prefixEnd_4512666 : Nat := 4983230072969 + 3 ^ 40 * 4512666 * 2
def baseEnd_4512666 : Nat := 772388897067448802407211

theorem tailTrace_4512666 : CollatzResearch.WordTrace tailWord_4512666 prefixEnd_4512666 772388897067448802407211 := by
  unfold tailWord_4512666
  simp only [CollatzResearch.WordTrace]
  refine ⟨41147612667347314709797463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109726967112926172559459901 41147612667347314709797463)
  ·
    refine ⟨61721419001020972064696195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41147612667347314709797463 61721419001020972064696195)
    ·
      refine ⟨92582128501531458097044293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61721419001020972064696195 92582128501531458097044293)
      ·
        refine ⟨17359149094037148393195805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92582128501531458097044293 17359149094037148393195805)
        ·
          refine ⟨6509680910263930647448427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17359149094037148393195805 6509680910263930647448427)
          ·
            refine ⟨9764521365395895971172641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6509680910263930647448427 9764521365395895971172641)
            ·
              refine ⟨7323391024046921978379481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9764521365395895971172641 7323391024046921978379481)
              ·
                refine ⟨5492543268035191483784611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7323391024046921978379481 5492543268035191483784611)
                ·
                  refine ⟨8238814902052787225676917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5492543268035191483784611 8238814902052787225676917)
                  ·
                    refine ⟨772388897067448802407211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8238814902052787225676917 772388897067448802407211)
                    ·
                      rfl

theorem cell23_4512666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 1, 5].length) (baseStart_4512666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512666 prefixEnd_4512666 := by exact prefixLift 4512666
  have htrace : WordTrace (prefixWord ++ tailWord_4512666) baseStart_4512666 baseEnd_4512666 := by
    simpa [prefixWord, tailWord_4512666, baseEnd_4512666] using wordTrace_append hprefix tailTrace_4512666
  have hstable : (prefixWord ++ tailWord_4512666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512666).length < 2 ^ (prefixWord ++ tailWord_4512666).sum := by decide
  have hdescent : baseEnd_4512666 < baseStart_4512666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512669 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 2, 6, 2]
def baseStart_4512669 : Nat := 118140960795 + 4512669 * 2 ^ 59
def prefixEnd_4512669 : Nat := 4983230072969 + 3 ^ 40 * 4512669 * 2
def baseEnd_4512669 : Nat := 2317168231644309895484119

theorem tailTrace_4512669 : CollatzResearch.WordTrace tailWord_4512669 prefixEnd_4512669 2317168231644309895484119 := by
  unfold tailWord_4512669
  simp only [CollatzResearch.WordTrace]
  refine ⟨164590560088378390351549061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109727040058918926901032707 164590560088378390351549061)
  ·
    refine ⟨30860730016570948190915449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164590560088378390351549061 30860730016570948190915449)
    ·
      refine ⟨23145547512428211143186587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30860730016570948190915449 23145547512428211143186587)
      ·
        refine ⟨34718321268642316714779881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23145547512428211143186587 34718321268642316714779881)
        ·
          refine ⟨26038740951481737536084911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34718321268642316714779881 26038740951481737536084911)
          ·
            refine ⟨39058111427222606304127367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26038740951481737536084911 39058111427222606304127367)
            ·
              refine ⟨58587167140833909456191051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39058111427222606304127367 58587167140833909456191051)
              ·
                refine ⟨87880750711250864184286577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58587167140833909456191051 87880750711250864184286577)
                ·
                  refine ⟨65910563033438148138214933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87880750711250864184286577 65910563033438148138214933)
                  ·
                    refine ⟨3089557642192413193978825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65910563033438148138214933 3089557642192413193978825)
                    ·
                      refine ⟨2317168231644309895484119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3089557642192413193978825 2317168231644309895484119)
                      ·
                        rfl

theorem cell23_4512669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_4512669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512669 prefixEnd_4512669 := by exact prefixLift 4512669
  have htrace : WordTrace (prefixWord ++ tailWord_4512669) baseStart_4512669 baseEnd_4512669 := by
    simpa [prefixWord, tailWord_4512669, baseEnd_4512669] using wordTrace_append hprefix tailTrace_4512669
  have hstable : (prefixWord ++ tailWord_4512669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512669).length < 2 ^ (prefixWord ++ tailWord_4512669).sum := by decide
  have hdescent : baseEnd_4512669 < baseStart_4512669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512717 : List Nat := [1, 6, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_4512717 : Nat := 118140960795 + 4512717 * 2 ^ 59
def prefixEnd_4512717 : Nat := 4983230072969 + 3 ^ 40 * 4512717 * 2
def baseEnd_4512717 : Nat := 772397626238575235894633

theorem tailTrace_4512717 : CollatzResearch.WordTrace tailWord_4512717 prefixEnd_4512717 772397626238575235894633 := by
  unfold tailWord_4512717
  simp only [CollatzResearch.WordTrace]
  refine ⟨164592310792204494549296405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109728207194802996366197603 164592310792204494549296405)
  ·
    refine ⟨7715264568384585681998269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 164592310792204494549296405 7715264568384585681998269)
    ·
      refine ⟨2893224213144219630749351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7715264568384585681998269 2893224213144219630749351)
      ·
        refine ⟨4339836319716329446124027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2893224213144219630749351 4339836319716329446124027)
        ·
          refine ⟨6509754479574494169186041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4339836319716329446124027 6509754479574494169186041)
          ·
            refine ⟨4882315859680870626889531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6509754479574494169186041 4882315859680870626889531)
            ·
              refine ⟨7323473789521305940334297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4882315859680870626889531 7323473789521305940334297)
              ·
                refine ⟨5492605342140979455250723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7323473789521305940334297 5492605342140979455250723)
                ·
                  refine ⟨8238908013211469182876085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5492605342140979455250723 8238908013211469182876085)
                  ·
                    refine ⟨772397626238575235894633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8238908013211469182876085 772397626238575235894633)
                    ·
                      rfl

theorem cell23_4512717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_4512717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512717 prefixEnd_4512717 := by exact prefixLift 4512717
  have htrace : WordTrace (prefixWord ++ tailWord_4512717) baseStart_4512717 baseEnd_4512717 := by
    simpa [prefixWord, tailWord_4512717, baseEnd_4512717] using wordTrace_append hprefix tailTrace_4512717
  have hstable : (prefixWord ++ tailWord_4512717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512717).length < 2 ^ (prefixWord ++ tailWord_4512717).sum := by decide
  have hdescent : baseEnd_4512717 < baseStart_4512717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512752 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 2, 6]
def baseStart_4512752 : Nat := 118140960795 + 4512752 * 2 ^ 59
def prefixEnd_4512752 : Nat := 4983230072969 + 3 ^ 40 * 4512752 * 2
def baseEnd_4512752 : Nat := 772403616846211023582079

theorem tailTrace_4512752 : CollatzResearch.WordTrace tailWord_4512752 prefixEnd_4512752 772403616846211023582079 := by
  unfold tailWord_4512752
  simp only [CollatzResearch.WordTrace]
  refine ⟨82296793673538847763410255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109729058231385130351213673 82296793673538847763410255)
  ·
    refine ⟨123445190510308271645115383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82296793673538847763410255 123445190510308271645115383)
    ·
      refine ⟨185167785765462407467673075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123445190510308271645115383 185167785765462407467673075)
      ·
        refine ⟨277751678648193611201509613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185167785765462407467673075 277751678648193611201509613)
        ·
          refine ⟨104156879493072604200566105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 277751678648193611201509613 104156879493072604200566105)
          ·
            refine ⟨78117659619804453150424579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104156879493072604200566105 78117659619804453150424579)
            ·
              refine ⟨117176489429706679725636869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78117659619804453150424579 117176489429706679725636869)
              ·
                refine ⟨21970591768070002448556913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117176489429706679725636869 21970591768070002448556913)
                ·
                  refine ⟨16477943826052501836417685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21970591768070002448556913 16477943826052501836417685)
                  ·
                    refine ⟨772403616846211023582079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16477943826052501836417685 772403616846211023582079)
                    ·
                      rfl

theorem cell23_4512752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 2, 6].length) (baseStart_4512752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512752 prefixEnd_4512752 := by exact prefixLift 4512752
  have htrace : WordTrace (prefixWord ++ tailWord_4512752) baseStart_4512752 baseEnd_4512752 := by
    simpa [prefixWord, tailWord_4512752, baseEnd_4512752] using wordTrace_append hprefix tailTrace_4512752
  have hstable : (prefixWord ++ tailWord_4512752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512752).length < 2 ^ (prefixWord ++ tailWord_4512752).sum := by decide
  have hdescent : baseEnd_4512752 < baseStart_4512752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512753 : List Nat := [1, 2, 2, 2, 4, 2, 2, 2, 2, 1, 3]
def baseStart_4512753 : Nat := 118140960795 + 4512753 * 2 ^ 59
def prefixEnd_4512753 : Nat := 4983230072969 + 3 ^ 40 * 4512753 * 2
def baseEnd_4512753 : Nat := 2317211364019287566833733

theorem tailTrace_4512753 : CollatzResearch.WordTrace tailWord_4512753 prefixEnd_4512753 2317211364019287566833733 := by
  unfold tailWord_4512753
  simp only [CollatzResearch.WordTrace]
  refine ⟨164593623820074072697606913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109729082546716048465071275 164593623820074072697606913)
  ·
    refine ⟨123445217865055554523205185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164593623820074072697606913 123445217865055554523205185)
    ·
      refine ⟨92583913398791665892403889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123445217865055554523205185 92583913398791665892403889)
      ·
        refine ⟨69437935049093749419302917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92583913398791665892403889 69437935049093749419302917)
        ·
          refine ⟨13019612821705078016119297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69437935049093749419302917 13019612821705078016119297)
          ·
            refine ⟨9764709616278808512089473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13019612821705078016119297 9764709616278808512089473)
            ·
              refine ⟨7323532212209106384067105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9764709616278808512089473 7323532212209106384067105)
              ·
                refine ⟨5492649159156829788050329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7323532212209106384067105 5492649159156829788050329)
                ·
                  refine ⟨4119486869367622341037747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5492649159156829788050329 4119486869367622341037747)
                  ·
                    refine ⟨6179230304051433511556621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4119486869367622341037747 6179230304051433511556621)
                    ·
                      refine ⟨2317211364019287566833733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6179230304051433511556621 2317211364019287566833733)
                      ·
                        rfl

theorem cell23_4512753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_4512753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512753 prefixEnd_4512753 := by exact prefixLift 4512753
  have htrace : WordTrace (prefixWord ++ tailWord_4512753) baseStart_4512753 baseEnd_4512753 := by
    simpa [prefixWord, tailWord_4512753, baseEnd_4512753] using wordTrace_append hprefix tailTrace_4512753
  have hstable : (prefixWord ++ tailWord_4512753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512753).length < 2 ^ (prefixWord ++ tailWord_4512753).sum := by decide
  have hdescent : baseEnd_4512753 < baseStart_4512753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512762 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5]
def baseStart_4512762 : Nat := 118140960795 + 4512762 * 2 ^ 59
def prefixEnd_4512762 : Nat := 4983230072969 + 3 ^ 40 * 4512762 * 2
def baseEnd_4512762 : Nat := 2317215985345178031621191

theorem tailTrace_4512762 : CollatzResearch.WordTrace tailWord_4512762 prefixEnd_4512762 2317215985345178031621191 := by
  unfold tailWord_4512762
  simp only [CollatzResearch.WordTrace]
  refine ⟨41148488019260366808671135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109729301384694311489789693 41148488019260366808671135)
  ·
    refine ⟨61722732028890550213006703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41148488019260366808671135 61722732028890550213006703)
    ·
      refine ⟨92584098043335825319510055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61722732028890550213006703 92584098043335825319510055)
      ·
        refine ⟨138876147065003737979265083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92584098043335825319510055 138876147065003737979265083)
        ·
          refine ⟨208314220597505606968897625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138876147065003737979265083 208314220597505606968897625)
          ·
            refine ⟨156235665448129205226673219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208314220597505606968897625 156235665448129205226673219)
            ·
              refine ⟨234353498172193807840009829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156235665448129205226673219 234353498172193807840009829)
              ·
                refine ⟨43941280907286338970001843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 234353498172193807840009829 43941280907286338970001843)
                ·
                  refine ⟨65911921360929508455002765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43941280907286338970001843 65911921360929508455002765)
                  ·
                    refine ⟨24716970510348565670626037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65911921360929508455002765 24716970510348565670626037)
                    ·
                      refine ⟨2317215985345178031621191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24716970510348565670626037 2317215985345178031621191)
                      ·
                        rfl

theorem cell23_4512762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_4512762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512762 prefixEnd_4512762 := by exact prefixLift 4512762
  have htrace : WordTrace (prefixWord ++ tailWord_4512762) baseStart_4512762 baseEnd_4512762 := by
    simpa [prefixWord, tailWord_4512762, baseEnd_4512762] using wordTrace_append hprefix tailTrace_4512762
  have hstable : (prefixWord ++ tailWord_4512762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512762).length < 2 ^ (prefixWord ++ tailWord_4512762).sum := by decide
  have hdescent : baseEnd_4512762 < baseStart_4512762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512769 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 2, 6]
def baseStart_4512769 : Nat := 118140960795 + 4512769 * 2 ^ 59
def prefixEnd_4512769 : Nat := 4983230072969 + 3 ^ 40 * 4512769 * 2
def baseEnd_4512769 : Nat := 772406526569919834744553

theorem tailTrace_4512769 : CollatzResearch.WordTrace tailWord_4512769 prefixEnd_4512769 772406526569919834744553 := by
  unfold tailWord_4512769
  simp only [CollatzResearch.WordTrace]
  refine ⟨164594207388016107430189361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109729471592010738286792907 164594207388016107430189361)
  ·
    refine ⟨123445655541012080572642021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164594207388016107430189361 123445655541012080572642021)
    ·
      refine ⟨23146060413939765107370379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123445655541012080572642021 23146060413939765107370379)
      ·
        refine ⟨34719090620909647661055569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23146060413939765107370379 34719090620909647661055569)
        ·
          refine ⟨26039317965682235745791677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34719090620909647661055569 26039317965682235745791677)
          ·
            refine ⟨9764744237130838404671879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26039317965682235745791677 9764744237130838404671879)
            ·
              refine ⟨14647116355696257607007819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9764744237130838404671879 14647116355696257607007819)
              ·
                refine ⟨21970674533544386410511729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14647116355696257607007819 21970674533544386410511729)
                ·
                  refine ⟨16478005900158289807883797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21970674533544386410511729 16478005900158289807883797)
                  ·
                    refine ⟨772406526569919834744553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16478005900158289807883797 772406526569919834744553)
                    ·
                      rfl

theorem cell23_4512769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_4512769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512769 prefixEnd_4512769 := by exact prefixLift 4512769
  have htrace : WordTrace (prefixWord ++ tailWord_4512769) baseStart_4512769 baseEnd_4512769 := by
    simpa [prefixWord, tailWord_4512769, baseEnd_4512769] using wordTrace_append hprefix tailTrace_4512769
  have hstable : (prefixWord ++ tailWord_4512769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512769).length < 2 ^ (prefixWord ++ tailWord_4512769).sum := by decide
  have hdescent : baseEnd_4512769 < baseStart_4512769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512770 : List Nat := [3, 4, 1, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_4512770 : Nat := 118140960795 + 4512770 * 2 ^ 59
def prefixEnd_4512770 : Nat := 4983230072969 + 3 ^ 40 * 4512770 * 2
def baseEnd_4512770 : Nat := 2317220093190414000321155

theorem tailTrace_4512770 : CollatzResearch.WordTrace tailWord_4512770 prefixEnd_4512770 2317220093190414000321155 := by
  unfold tailWord_4512770
  simp only [CollatzResearch.WordTrace]
  refine ⟨41148560965253121150243941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109729495907341656400650509 41148560965253121150243941)
  ·
    refine ⟨7715355180984960215670739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41148560965253121150243941 7715355180984960215670739)
    ·
      refine ⟨11573032771477440323506109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7715355180984960215670739 11573032771477440323506109)
      ·
        refine ⟨4339887289304040121314791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11573032771477440323506109 4339887289304040121314791)
        ·
          refine ⟨6509830933956060181972187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4339887289304040121314791 6509830933956060181972187)
          ·
            refine ⟨9764746400934090272958281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6509830933956060181972187 9764746400934090272958281)
            ·
              refine ⟨7323559800700567704718711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9764746400934090272958281 7323559800700567704718711)
              ·
                refine ⟨10985339701050851557078067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7323559800700567704718711 10985339701050851557078067)
                ·
                  refine ⟨16478009551576277335617101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10985339701050851557078067 16478009551576277335617101)
                  ·
                    refine ⟨6179253581841104000856413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16478009551576277335617101 6179253581841104000856413)
                    ·
                      refine ⟨2317220093190414000321155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6179253581841104000856413 2317220093190414000321155)
                      ·
                        rfl

theorem cell23_4512770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_4512770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512770 prefixEnd_4512770 := by exact prefixLift 4512770
  have htrace : WordTrace (prefixWord ++ tailWord_4512770) baseStart_4512770 baseEnd_4512770 := by
    simpa [prefixWord, tailWord_4512770, baseEnd_4512770] using wordTrace_append hprefix tailTrace_4512770
  have hstable : (prefixWord ++ tailWord_4512770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512770).length < 2 ^ (prefixWord ++ tailWord_4512770).sum := by decide
  have hdescent : baseEnd_4512770 < baseStart_4512770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512776 : List Nat := [2, 1, 3, 2, 1, 3, 1, 3, 1, 4, 2]
def baseStart_4512776 : Nat := 118140960795 + 4512776 * 2 ^ 59
def prefixEnd_4512776 : Nat := 4983230072969 + 3 ^ 40 * 4512776 * 2
def baseEnd_4512776 : Nat := 2317223174074340976846127

theorem tailTrace_4512776 : CollatzResearch.WordTrace tailWord_4512776 prefixEnd_4512776 2317223174074340976846127 := by
  unfold tailWord_4512776
  simp only [CollatzResearch.WordTrace]
  refine ⟨82297231349495373812847091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109729641799327165083796121 82297231349495373812847091)
  ·
    refine ⟨123445847024243060719270637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82297231349495373812847091 123445847024243060719270637)
    ·
      refine ⟨46292192634091147769726489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123445847024243060719270637 46292192634091147769726489)
      ·
        refine ⟨34719144475568360827294867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46292192634091147769726489 34719144475568360827294867)
        ·
          refine ⟨52078716713352541240942301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34719144475568360827294867 52078716713352541240942301)
          ·
            refine ⟨19529518767507202965353363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52078716713352541240942301 19529518767507202965353363)
            ·
              refine ⟨29294278151260804448030045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19529518767507202965353363 29294278151260804448030045)
              ·
                refine ⟨10985354306722801668011267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29294278151260804448030045 10985354306722801668011267)
                ·
                  refine ⟨16478031460084202502016901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10985354306722801668011267 16478031460084202502016901)
                  ·
                    refine ⟨3089630898765787969128169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16478031460084202502016901 3089630898765787969128169)
                    ·
                      refine ⟨2317223174074340976846127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3089630898765787969128169 2317223174074340976846127)
                      ·
                        rfl

theorem cell23_4512776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_4512776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512776 prefixEnd_4512776 := by exact prefixLift 4512776
  have htrace : WordTrace (prefixWord ++ tailWord_4512776) baseStart_4512776 baseEnd_4512776 := by
    simpa [prefixWord, tailWord_4512776, baseEnd_4512776] using wordTrace_append hprefix tailTrace_4512776
  have hstable : (prefixWord ++ tailWord_4512776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512776).length < 2 ^ (prefixWord ++ tailWord_4512776).sum := by decide
  have hdescent : baseEnd_4512776 < baseStart_4512776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512797 : List Nat := [1, 4, 2, 2, 3, 2, 2, 1, 1, 3, 2]
def baseStart_4512797 : Nat := 118140960795 + 4512797 * 2 ^ 59
def prefixEnd_4512797 : Nat := 4983230072969 + 3 ^ 40 * 4512797 * 2
def baseEnd_4512797 : Nat := 2317233957168085394683531

theorem tailTrace_4512797 : CollatzResearch.WordTrace tailWord_4512797 prefixEnd_4512797 2317233957168085394683531 := by
  unfold tailWord_4512797
  simp only [CollatzResearch.WordTrace]
  refine ⟨164595228631914668212208645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109730152421276445474805763 164595228631914668212208645)
  ·
    refine ⟨30861605368484000289789121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164595228631914668212208645 30861605368484000289789121)
    ·
      refine ⟨23146204026363000217341841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30861605368484000289789121 23146204026363000217341841)
      ·
        refine ⟨17359653019772250163006381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23146204026363000217341841 17359653019772250163006381)
        ·
          refine ⟨6509869882414593811127393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17359653019772250163006381 6509869882414593811127393)
          ·
            refine ⟨4882402411810945358345545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6509869882414593811127393 4882402411810945358345545)
            ·
              refine ⟨3661801808858209018759159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4882402411810945358345545 3661801808858209018759159)
              ·
                refine ⟨5492702713287313528138739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3661801808858209018759159 5492702713287313528138739)
                ·
                  refine ⟨8239054069930970292208109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5492702713287313528138739 8239054069930970292208109)
                  ·
                    refine ⟨3089645276224113859578041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8239054069930970292208109 3089645276224113859578041)
                    ·
                      refine ⟨2317233957168085394683531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3089645276224113859578041 2317233957168085394683531)
                      ·
                        rfl

theorem cell23_4512797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_4512797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512797 prefixEnd_4512797 := by exact prefixLift 4512797
  have htrace : WordTrace (prefixWord ++ tailWord_4512797) baseStart_4512797 baseEnd_4512797 := by
    simpa [prefixWord, tailWord_4512797, baseEnd_4512797] using wordTrace_append hprefix tailTrace_4512797
  have hstable : (prefixWord ++ tailWord_4512797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512797).length < 2 ^ (prefixWord ++ tailWord_4512797).sum := by decide
  have hdescent : baseEnd_4512797 < baseStart_4512797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512810 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 4, 2, 2]
def baseStart_4512810 : Nat := 118140960795 + 4512810 * 2 ^ 59
def prefixEnd_4512810 : Nat := 4983230072969 + 3 ^ 40 * 4512810 * 2
def baseEnd_4512810 : Nat := 2317240632416593843820971

theorem tailTrace_4512810 : CollatzResearch.WordTrace tailWord_4512810 prefixEnd_4512810 2317240632416593843820971 := by
  unfold tailWord_4512810
  simp only [CollatzResearch.WordTrace]
  refine ⟨41148925695216892858107971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109730468520578380954954589 41148925695216892858107971)
  ·
    refine ⟨61723388542825339287161957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41148925695216892858107971 61723388542825339287161957)
    ·
      refine ⟨11573135351779751116342867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61723388542825339287161957 11573135351779751116342867)
      ·
        refine ⟨17359703027669626674514301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11573135351779751116342867 17359703027669626674514301)
        ·
          refine ⟨6509888635376110002942863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17359703027669626674514301 6509888635376110002942863)
          ·
            refine ⟨9764832953064165004414295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6509888635376110002942863 9764832953064165004414295)
            ·
              refine ⟨14647249429596247506621443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9764832953064165004414295 14647249429596247506621443)
              ·
                refine ⟨21970874144394371259932165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14647249429596247506621443 21970874144394371259932165)
                ·
                  refine ⟨4119538902073944611237281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21970874144394371259932165 4119538902073944611237281)
                  ·
                    refine ⟨3089654176555458458427961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4119538902073944611237281 3089654176555458458427961)
                    ·
                      refine ⟨2317240632416593843820971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3089654176555458458427961 2317240632416593843820971)
                      ·
                        rfl

theorem cell23_4512810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_4512810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512810 prefixEnd_4512810 := by exact prefixLift 4512810
  have htrace : WordTrace (prefixWord ++ tailWord_4512810) baseStart_4512810 baseEnd_4512810 := by
    simpa [prefixWord, tailWord_4512810, baseEnd_4512810] using wordTrace_append hprefix tailTrace_4512810
  have hstable : (prefixWord ++ tailWord_4512810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512810).length < 2 ^ (prefixWord ++ tailWord_4512810).sum := by decide
  have hdescent : baseEnd_4512810 < baseStart_4512810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512829 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 1, 7]
def baseStart_4512829 : Nat := 118140960795 + 4512829 * 2 ^ 59
def prefixEnd_4512829 : Nat := 4983230072969 + 3 ^ 40 * 4512829 * 2
def baseEnd_4512829 : Nat := 772416796183009756494461

theorem tailTrace_4512829 : CollatzResearch.WordTrace tailWord_4512829 prefixEnd_4512829 772416796183009756494461 := by
  unfold tailWord_4512829
  simp only [CollatzResearch.WordTrace]
  refine ⟨164596395767798737677373541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109730930511865825118249027 164596395767798737677373541)
  ·
    refine ⟨30861824206462263314507539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164596395767798737677373541 30861824206462263314507539)
    ·
      refine ⟨46292736309693394971761309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30861824206462263314507539 46292736309693394971761309)
      ·
        refine ⟨17359776116135023114410491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46292736309693394971761309 17359776116135023114410491)
        ·
          refine ⟨26039664174202534671615737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17359776116135023114410491 26039664174202534671615737)
          ·
            refine ⟨19529748130651901003711803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26039664174202534671615737 19529748130651901003711803)
            ·
              refine ⟨29294622195977851505567705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19529748130651901003711803 29294622195977851505567705)
              ·
                refine ⟨21970966646983388629175779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29294622195977851505567705 21970966646983388629175779)
                ·
                  refine ⟨32956449970475082943763669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21970966646983388629175779 32956449970475082943763669)
                  ·
                    refine ⟨772416796183009756494461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32956449970475082943763669 772416796183009756494461)
                    ·
                      rfl

theorem cell23_4512829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_4512829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512829 prefixEnd_4512829 := by exact prefixLift 4512829
  have htrace : WordTrace (prefixWord ++ tailWord_4512829) baseStart_4512829 baseEnd_4512829 := by
    simpa [prefixWord, tailWord_4512829, baseEnd_4512829] using wordTrace_append hprefix tailTrace_4512829
  have hstable : (prefixWord ++ tailWord_4512829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512829).length < 2 ^ (prefixWord ++ tailWord_4512829).sum := by decide
  have hdescent : baseEnd_4512829 < baseStart_4512829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512849 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 1, 3, 4]
def baseStart_4512849 : Nat := 118140960795 + 4512849 * 2 ^ 59
def prefixEnd_4512849 : Nat := 4983230072969 + 3 ^ 40 * 4512849 * 2
def baseEnd_4512849 : Nat := 2317260658162119191233291

theorem tailTrace_4512849 : CollatzResearch.WordTrace tailWord_4512849 prefixEnd_4512849 2317260658162119191233291 := by
  unfold tailWord_4512849
  simp only [CollatzResearch.WordTrace]
  refine ⟨164597125227726281093101601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109731416818484187395401067 164597125227726281093101601)
  ·
    refine ⟨123447843920794710819826201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164597125227726281093101601 123447843920794710819826201)
    ·
      refine ⟨92585882940596033114869651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123447843920794710819826201 92585882940596033114869651)
      ·
        refine ⟨138878824410894049672304477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92585882940596033114869651 138878824410894049672304477)
        ·
          refine ⟨52079559154085268627114179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138878824410894049672304477 52079559154085268627114179)
          ·
            refine ⟨78119338731127902940671269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52079559154085268627114179 78119338731127902940671269)
            ·
              refine ⟨14647376012086481801375863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78119338731127902940671269 14647376012086481801375863)
              ·
                refine ⟨21971064018129722702063795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14647376012086481801375863 21971064018129722702063795)
                ·
                  refine ⟨32956596027194584053095693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21971064018129722702063795 32956596027194584053095693)
                  ·
                    refine ⟨12358723510197969019910885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32956596027194584053095693 12358723510197969019910885)
                    ·
                      refine ⟨2317260658162119191233291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12358723510197969019910885 2317260658162119191233291)
                      ·
                        rfl

theorem cell23_4512849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_4512849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512849 prefixEnd_4512849 := by exact prefixLift 4512849
  have htrace : WordTrace (prefixWord ++ tailWord_4512849) baseStart_4512849 baseEnd_4512849 := by
    simpa [prefixWord, tailWord_4512849, baseEnd_4512849] using wordTrace_append hprefix tailTrace_4512849
  have hstable : (prefixWord ++ tailWord_4512849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512849).length < 2 ^ (prefixWord ++ tailWord_4512849).sum := by decide
  have hdescent : baseEnd_4512849 < baseStart_4512849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512969 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 2, 6, 4]
def baseStart_4512969 : Nat := 118140960795 + 4512969 * 2 ^ 59
def prefixEnd_4512969 : Nat := 4983230072969 + 3 ^ 40 * 4512969 * 2
def baseEnd_4512969 : Nat := 2317322275840658721732739

theorem tailTrace_4512969 : CollatzResearch.WordTrace tailWord_4512969 prefixEnd_4512969 2317322275840658721732739 := by
  unfold tailWord_4512969
  simp only [CollatzResearch.WordTrace]
  refine ⟨164601501987291541587469961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109734334658194361058313307 164601501987291541587469961)
  ·
    refine ⟨123451126490468656190602471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164601501987291541587469961 123451126490468656190602471)
    ·
      refine ⟨185176689735702984285903707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123451126490468656190602471 185176689735702984285903707)
      ·
        refine ⟨277765034603554476428855561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185176689735702984285903707 277765034603554476428855561)
        ·
          refine ⟨208323775952665857321641671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277765034603554476428855561 208323775952665857321641671)
          ·
            refine ⟨312485663928998785982462507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208323775952665857321641671 312485663928998785982462507)
            ·
              refine ⟨468728495893498178973693761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312485663928998785982462507 468728495893498178973693761)
              ·
                refine ⟨351546371920123634230270321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 468728495893498178973693761 351546371920123634230270321)
                ·
                  refine ⟨263659778940092725672702741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351546371920123634230270321 263659778940092725672702741)
                  ·
                    refine ⟨12359052137816846515907941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 263659778940092725672702741 12359052137816846515907941)
                    ·
                      refine ⟨2317322275840658721732739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12359052137816846515907941 2317322275840658721732739)
                      ·
                        rfl

theorem cell23_4512969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 6, 4].length) (baseStart_4512969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512969 prefixEnd_4512969 := by exact prefixLift 4512969
  have htrace : WordTrace (prefixWord ++ tailWord_4512969) baseStart_4512969 baseEnd_4512969 := by
    simpa [prefixWord, tailWord_4512969, baseEnd_4512969] using wordTrace_append hprefix tailTrace_4512969
  have hstable : (prefixWord ++ tailWord_4512969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512969).length < 2 ^ (prefixWord ++ tailWord_4512969).sum := by decide
  have hdescent : baseEnd_4512969 < baseStart_4512969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512970 : List Nat := [3, 1, 2, 1, 3, 4, 2, 1, 1, 5]
def baseStart_4512970 : Nat := 118140960795 + 4512970 * 2 ^ 59
def prefixEnd_4512970 : Nat := 4983230072969 + 3 ^ 40 * 4512970 * 2
def baseEnd_4512970 : Nat := 772440929773771072606745

theorem tailTrace_4512970 : CollatzResearch.WordTrace tailWord_4512970 prefixEnd_4512970 772440929773771072606745 := by
  unfold tailWord_4512970
  simp only [CollatzResearch.WordTrace]
  refine ⟨41150384615071979689564091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109734358973525279172170909 41150384615071979689564091)
  ·
    refine ⟨61725576922607969534346137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41150384615071979689564091 61725576922607969534346137)
    ·
      refine ⟨46294182691955977150759603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61725576922607969534346137 46294182691955977150759603)
      ·
        refine ⟨69441274037933965726139405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46294182691955977150759603 69441274037933965726139405)
        ·
          refine ⟨26040477764225237147302277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69441274037933965726139405 26040477764225237147302277)
          ·
            refine ⟨4882589580792231965119177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26040477764225237147302277 4882589580792231965119177)
            ·
              refine ⟨3661942185594173973839383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4882589580792231965119177 3661942185594173973839383)
              ·
                refine ⟨5492913278391260960759075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3661942185594173973839383 5492913278391260960759075)
                ·
                  refine ⟨8239369917586891441138613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5492913278391260960759075 8239369917586891441138613)
                  ·
                    refine ⟨772440929773771072606745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8239369917586891441138613 772440929773771072606745)
                    ·
                      rfl

theorem cell23_4512970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_4512970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512970 prefixEnd_4512970 := by exact prefixLift 4512970
  have htrace : WordTrace (prefixWord ++ tailWord_4512970) baseStart_4512970 baseEnd_4512970 := by
    simpa [prefixWord, tailWord_4512970, baseEnd_4512970] using wordTrace_append hprefix tailTrace_4512970
  have hstable : (prefixWord ++ tailWord_4512970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512970).length < 2 ^ (prefixWord ++ tailWord_4512970).sum := by decide
  have hdescent : baseEnd_4512970 < baseStart_4512970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4512983 : List Nat := [1, 1, 3, 2, 1, 2, 5, 2, 2, 4]
def baseStart_4512983 : Nat := 118140960795 + 4512983 * 2 ^ 59
def prefixEnd_4512983 : Nat := 4983230072969 + 3 ^ 40 * 4512983 * 2
def baseEnd_4512983 : Nat := 772443154856607222319225

theorem tailTrace_4512983 : CollatzResearch.WordTrace tailWord_4512983 prefixEnd_4512983 772443154856607222319225 := by
  unfold tailWord_4512983
  simp only [CollatzResearch.WordTrace]
  refine ⟨164602012609240821978479603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109734675072827214652319735 164602012609240821978479603)
  ·
    refine ⟨246903018913861232967719405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164602012609240821978479603 246903018913861232967719405)
    ·
      refine ⟨92588632092697962362894777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246903018913861232967719405 92588632092697962362894777)
      ·
        refine ⟨69441474069523471772171083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92588632092697962362894777 69441474069523471772171083)
        ·
          refine ⟨104162211104285207658256625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69441474069523471772171083 104162211104285207658256625)
          ·
            refine ⟨78121658328213905743692469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104162211104285207658256625 78121658328213905743692469)
            ·
              refine ⟨7323905468270053663471169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78121658328213905743692469 7323905468270053663471169)
              ·
                refine ⟨5492929101202540247603377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7323905468270053663471169 5492929101202540247603377)
                ·
                  refine ⟨4119696825901905185702533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5492929101202540247603377 4119696825901905185702533)
                  ·
                    refine ⟨772443154856607222319225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4119696825901905185702533 772443154856607222319225)
                    ·
                      rfl

theorem cell23_4512983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 4].length) (baseStart_4512983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4512983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4512983 prefixEnd_4512983 := by exact prefixLift 4512983
  have htrace : WordTrace (prefixWord ++ tailWord_4512983) baseStart_4512983 baseEnd_4512983 := by
    simpa [prefixWord, tailWord_4512983, baseEnd_4512983] using wordTrace_append hprefix tailTrace_4512983
  have hstable : (prefixWord ++ tailWord_4512983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4512983).length < 2 ^ (prefixWord ++ tailWord_4512983).sum := by decide
  have hdescent : baseEnd_4512983 < baseStart_4512983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4512983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513000 : List Nat := [2, 1, 4, 1, 2, 1, 5, 1, 2, 4]
def baseStart_4513000 : Nat := 118140960795 + 4513000 * 2 ^ 59
def prefixEnd_4513000 : Nat := 4983230072969 + 3 ^ 40 * 4513000 * 2
def baseEnd_4513000 : Nat := 772446064580316033481699

theorem tailTrace_4513000 : CollatzResearch.WordTrace tailWord_4513000 prefixEnd_4513000 772446064580316033481699 := by
  unfold tailWord_4513000
  simp only [CollatzResearch.WordTrace]
  refine ⟨82301316325089616940924227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109735088433452822587898969 82301316325089616940924227)
  ·
    refine ⟨123451974487634425411386341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82301316325089616940924227 123451974487634425411386341)
    ·
      refine ⟨23147245216431454764634939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123451974487634425411386341 23147245216431454764634939)
      ·
        refine ⟨34720867824647182146952409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23147245216431454764634939 34720867824647182146952409)
        ·
          refine ⟨26040650868485386610214307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34720867824647182146952409 26040650868485386610214307)
          ·
            refine ⟨39060976302728079915321461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26040650868485386610214307 39060976302728079915321461)
            ·
              refine ⟨3661966528380757492061387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39060976302728079915321461 3661966528380757492061387)
              ·
                refine ⟨5492949792571136238092081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3661966528380757492061387 5492949792571136238092081)
                ·
                  refine ⟨4119712344428352178569061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5492949792571136238092081 4119712344428352178569061)
                  ·
                    refine ⟨772446064580316033481699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4119712344428352178569061 772446064580316033481699)
                    ·
                      rfl

theorem cell23_4513000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_4513000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513000 prefixEnd_4513000 := by exact prefixLift 4513000
  have htrace : WordTrace (prefixWord ++ tailWord_4513000) baseStart_4513000 baseEnd_4513000 := by
    simpa [prefixWord, tailWord_4513000, baseEnd_4513000] using wordTrace_append hprefix tailTrace_4513000
  have hstable : (prefixWord ++ tailWord_4513000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513000).length < 2 ^ (prefixWord ++ tailWord_4513000).sum := by decide
  have hdescent : baseEnd_4513000 < baseStart_4513000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513003 : List Nat := [1, 1, 1, 1, 2, 8, 1, 1, 1, 2, 4]
def baseStart_4513003 : Nat := 118140960795 + 4513003 * 2 ^ 59
def prefixEnd_4513003 : Nat := 4983230072969 + 3 ^ 40 * 4513003 * 2
def baseEnd_4513003 : Nat := 2317339734182911588707583

theorem tailTrace_4513003 : CollatzResearch.WordTrace tailWord_4513003 prefixEnd_4513003 2317339734182911588707583 := by
  unfold tailWord_4513003
  simp only [CollatzResearch.WordTrace]
  refine ⟨164602742069168365394207663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109735161379445576929471775 164602742069168365394207663)
  ·
    refine ⟨246904113103752548091311495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164602742069168365394207663 246904113103752548091311495)
    ·
      refine ⟨370356169655628822136967243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246904113103752548091311495 370356169655628822136967243)
      ·
        refine ⟨555534254483443233205450865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370356169655628822136967243 555534254483443233205450865)
        ·
          refine ⟨416650690862582424904088149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 555534254483443233205450865 416650690862582424904088149)
          ·
            refine ⟨4882625283545887791844783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 416650690862582424904088149 4882625283545887791844783)
            ·
              refine ⟨7323937925318831687767175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4882625283545887791844783 7323937925318831687767175)
              ·
                refine ⟨10985906887978247531650763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7323937925318831687767175 10985906887978247531650763)
                ·
                  refine ⟨16478860331967371297476145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10985906887978247531650763 16478860331967371297476145)
                  ·
                    refine ⟨12359145248975528473107109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16478860331967371297476145 12359145248975528473107109)
                    ·
                      refine ⟨2317339734182911588707583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12359145248975528473107109 2317339734182911588707583)
                      ·
                        rfl

theorem cell23_4513003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 2, 4].length) (baseStart_4513003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513003 prefixEnd_4513003 := by exact prefixLift 4513003
  have htrace : WordTrace (prefixWord ++ tailWord_4513003) baseStart_4513003 baseEnd_4513003 := by
    simpa [prefixWord, tailWord_4513003, baseEnd_4513003] using wordTrace_append hprefix tailTrace_4513003
  have hstable : (prefixWord ++ tailWord_4513003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513003).length < 2 ^ (prefixWord ++ tailWord_4513003).sum := by decide
  have hdescent : baseEnd_4513003 < baseStart_4513003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513023 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 4, 1, 3]
def baseStart_4513023 : Nat := 118140960795 + 4513023 * 2 ^ 59
def prefixEnd_4513023 : Nat := 4983230072969 + 3 ^ 40 * 4513023 * 2
def baseEnd_4513023 : Nat := 2317350003796001510457491

theorem tailTrace_4513023 : CollatzResearch.WordTrace tailWord_4513023 prefixEnd_4513023 2317350003796001510457491 := by
  unfold tailWord_4513023
  simp only [CollatzResearch.WordTrace]
  refine ⟨164603471529095908809935723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109735647686063939206623815 164603471529095908809935723)
  ·
    refine ⟨246905207293643863214903585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164603471529095908809935723 246905207293643863214903585)
    ·
      refine ⟨185178905470232897411177689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246905207293643863214903585 185178905470232897411177689)
      ·
        refine ⟨138884179102674673058383267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185178905470232897411177689 138884179102674673058383267)
        ·
          refine ⟨208326268654012009587574901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138884179102674673058383267 208326268654012009587574901)
          ·
            refine ⟨19530587686313625898835147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 208326268654012009587574901 19530587686313625898835147)
            ·
              refine ⟨29295881529470438848252721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19530587686313625898835147 29295881529470438848252721)
              ·
                refine ⟨21971911147102829136189541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29295881529470438848252721 21971911147102829136189541)
                ·
                  refine ⟨4119733340081780463035539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21971911147102829136189541 4119733340081780463035539)
                  ·
                    refine ⟨6179600010122670694553309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4119733340081780463035539 6179600010122670694553309)
                    ·
                      refine ⟨2317350003796001510457491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6179600010122670694553309 2317350003796001510457491)
                      ·
                        rfl

theorem cell23_4513023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 1, 3].length) (baseStart_4513023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513023 prefixEnd_4513023 := by exact prefixLift 4513023
  have htrace : WordTrace (prefixWord ++ tailWord_4513023) baseStart_4513023 baseEnd_4513023 := by
    simpa [prefixWord, tailWord_4513023, baseEnd_4513023] using wordTrace_append hprefix tailTrace_4513023
  have hstable : (prefixWord ++ tailWord_4513023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513023).length < 2 ^ (prefixWord ++ tailWord_4513023).sum := by decide
  have hdescent : baseEnd_4513023 < baseStart_4513023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513106 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_4513106 : Nat := 118140960795 + 4513106 * 2 ^ 59
def prefixEnd_4513106 : Nat := 4983230072969 + 3 ^ 40 * 4513106 * 2
def baseEnd_4513106 : Nat := 2317392622690324685719609

theorem tailTrace_4513106 : CollatzResearch.WordTrace tailWord_4513106 prefixEnd_4513106 2317392622690324685719609 := by
  unfold tailWord_4513106
  simp only [CollatzResearch.WordTrace]
  refine ⟨41151624696948803496301793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109737665858530142656804781 41151624696948803496301793)
  ·
    refine ⟨30863718522711602622226345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41151624696948803496301793 30863718522711602622226345)
    ·
      refine ⟨23147788892033701966669759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30863718522711602622226345 23147788892033701966669759)
      ·
        refine ⟨34721683338050552950004639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23147788892033701966669759 34721683338050552950004639)
        ·
          refine ⟨52082525007075829425006959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34721683338050552950004639 52082525007075829425006959)
          ·
            refine ⟨78123787510613744137510439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52082525007075829425006959 78123787510613744137510439)
            ·
              refine ⟨117185681265920616206265659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78123787510613744137510439 117185681265920616206265659)
              ·
                refine ⟨175778521898880924309398489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117185681265920616206265659 175778521898880924309398489)
                ·
                  refine ⟨131833891424160693232048867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175778521898880924309398489 131833891424160693232048867)
                  ·
                    refine ⟨197750837136241039848073301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 131833891424160693232048867 197750837136241039848073301)
                    ·
                      refine ⟨2317392622690324685719609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 197750837136241039848073301 2317392622690324685719609)
                      ·
                        rfl

theorem cell23_4513106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_4513106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513106 prefixEnd_4513106 := by exact prefixLift 4513106
  have htrace : WordTrace (prefixWord ++ tailWord_4513106) baseStart_4513106 baseEnd_4513106 := by
    simpa [prefixWord, tailWord_4513106, baseEnd_4513106] using wordTrace_append hprefix tailTrace_4513106
  have hstable : (prefixWord ++ tailWord_4513106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513106).length < 2 ^ (prefixWord ++ tailWord_4513106).sum := by decide
  have hdescent : baseEnd_4513106 < baseStart_4513106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513133 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 1, 7]
def baseStart_4513133 : Nat := 118140960795 + 4513133 * 2 ^ 59
def prefixEnd_4513133 : Nat := 4983230072969 + 3 ^ 40 * 4513133 * 2
def baseEnd_4513133 : Nat := 772468828889332026693995

theorem tailTrace_4513133 : CollatzResearch.WordTrace tailWord_4513133 prefixEnd_4513133 772468828889332026693995 := by
  unfold tailWord_4513133
  simp only [CollatzResearch.WordTrace]
  refine ⟨164607483558697397596440053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109738322372464931730960035 164607483558697397596440053)
  ·
    refine ⟨15431951583627881024666255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 164607483558697397596440053 15431951583627881024666255)
    ·
      refine ⟨23147927375441821536999383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15431951583627881024666255 23147927375441821536999383)
      ·
        refine ⟨34721891063162732305499075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23147927375441821536999383 34721891063162732305499075)
        ·
          refine ⟨52082836594744098458248613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34721891063162732305499075 52082836594744098458248613)
          ·
            refine ⟨9765531861514518460921615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52082836594744098458248613 9765531861514518460921615)
            ·
              refine ⟨14648297792271777691382423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9765531861514518460921615 14648297792271777691382423)
              ·
                refine ⟨21972446688407666537073635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14648297792271777691382423 21972446688407666537073635)
                ·
                  refine ⟨32958670032611499805610453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21972446688407666537073635 32958670032611499805610453)
                  ·
                    refine ⟨772468828889332026693995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32958670032611499805610453 772468828889332026693995)
                    ·
                      rfl

theorem cell23_4513133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_4513133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513133 prefixEnd_4513133 := by exact prefixLift 4513133
  have htrace : WordTrace (prefixWord ++ tailWord_4513133) baseStart_4513133 baseEnd_4513133 := by
    simpa [prefixWord, tailWord_4513133, baseEnd_4513133] using wordTrace_append hprefix tailTrace_4513133
  have hstable : (prefixWord ++ tailWord_4513133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513133).length < 2 ^ (prefixWord ++ tailWord_4513133).sum := by decide
  have hdescent : baseEnd_4513133 < baseStart_4513133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513173 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 1, 4, 3]
def baseStart_4513173 : Nat := 118140960795 + 4513173 * 2 ^ 59
def prefixEnd_4513173 : Nat := 4983230072969 + 3 ^ 40 * 4513173 * 2
def baseEnd_4513173 : Nat := 2317427025894175923581801

theorem tailTrace_4513173 : CollatzResearch.WordTrace tailWord_4513173 prefixEnd_4513173 2317427025894175923581801 := by
  unfold tailWord_4513173
  simp only [CollatzResearch.WordTrace]
  refine ⟨164608942478552484427896173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109739294985701656285264115 164608942478552484427896173)
  ·
    refine ⟨61728353429457181660461065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164608942478552484427896173 61728353429457181660461065)
    ·
      refine ⟨46296265072092886245345799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61728353429457181660461065 46296265072092886245345799)
      ·
        refine ⟨69444397608139329368018699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46296265072092886245345799 69444397608139329368018699)
        ·
          refine ⟨104166596412208994052028049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69444397608139329368018699 104166596412208994052028049)
          ·
            refine ⟨78124947309156745539021037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104166596412208994052028049 78124947309156745539021037)
            ·
              refine ⟨29296855240933779577132889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78124947309156745539021037 29296855240933779577132889)
              ·
                refine ⟨21972641430700334682849667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29296855240933779577132889 21972641430700334682849667)
                ·
                  refine ⟨32958962146050502024274501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21972641430700334682849667 32958962146050502024274501)
                  ·
                    refine ⟨6179805402384469129551469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32958962146050502024274501 6179805402384469129551469)
                    ·
                      refine ⟨2317427025894175923581801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6179805402384469129551469 2317427025894175923581801)
                      ·
                        rfl

theorem cell23_4513173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_4513173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513173 prefixEnd_4513173 := by exact prefixLift 4513173
  have htrace : WordTrace (prefixWord ++ tailWord_4513173) baseStart_4513173 baseEnd_4513173 := by
    simpa [prefixWord, tailWord_4513173, baseEnd_4513173] using wordTrace_append hprefix tailTrace_4513173
  have hstable : (prefixWord ++ tailWord_4513173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513173).length < 2 ^ (prefixWord ++ tailWord_4513173).sum := by decide
  have hdescent : baseEnd_4513173 < baseStart_4513173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513223 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 3, 5]
def baseStart_4513223 : Nat := 118140960795 + 4513223 * 2 ^ 59
def prefixEnd_4513223 : Nat := 4983230072969 + 3 ^ 40 * 4513223 * 2
def baseEnd_4513223 : Nat := 772484233308966909318857

theorem tailTrace_4513223 : CollatzResearch.WordTrace tailWord_4513223 prefixEnd_4513223 772484233308966909318857 := by
  unfold tailWord_4513223
  simp only [CollatzResearch.WordTrace]
  refine ⟨164610766128371342967216323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109740510752247561978144215 164610766128371342967216323)
  ·
    refine ⟨246916149192557014450824485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164610766128371342967216323 246916149192557014450824485)
    ·
      refine ⟨46296777973604440209529591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 246916149192557014450824485 46296777973604440209529591)
      ·
        refine ⟨69445166960406660314294387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46296777973604440209529591 69445166960406660314294387)
        ·
          refine ⟨104167750440609990471441581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69445166960406660314294387 104167750440609990471441581)
          ·
            refine ⟨39062906415228746426790593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104167750440609990471441581 39062906415228746426790593)
            ·
              refine ⟨29297179811421559820092945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39062906415228746426790593 29297179811421559820092945)
              ·
                refine ⟨21972884858566169865069709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29297179811421559820092945 21972884858566169865069709)
                ·
                  refine ⟨8239831821962313699401141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21972884858566169865069709 8239831821962313699401141)
                  ·
                    refine ⟨772484233308966909318857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8239831821962313699401141 772484233308966909318857)
                    ·
                      rfl

theorem cell23_4513223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_4513223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513223 prefixEnd_4513223 := by exact prefixLift 4513223
  have htrace : WordTrace (prefixWord ++ tailWord_4513223) baseStart_4513223 baseEnd_4513223 := by
    simpa [prefixWord, tailWord_4513223, baseEnd_4513223] using wordTrace_append hprefix tailTrace_4513223
  have hstable : (prefixWord ++ tailWord_4513223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513223).length < 2 ^ (prefixWord ++ tailWord_4513223).sum := by decide
  have hdescent : baseEnd_4513223 < baseStart_4513223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513230 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2]
def baseStart_4513230 : Nat := 118140960795 + 4513230 * 2 ^ 59
def prefixEnd_4513230 : Nat := 4983230072969 + 3 ^ 40 * 4513230 * 2
def baseEnd_4513230 : Nat := 2317456294291482200569039

theorem tailTrace_4513230 : CollatzResearch.WordTrace tailWord_4513230 prefixEnd_4513230 2317456294291482200569039 := by
  unfold tailWord_4513230
  simp only [CollatzResearch.WordTrace]
  refine ⟨20576377679918247895340143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109740680959563988775147429 20576377679918247895340143)
  ·
    refine ⟨30864566519877371843010215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20576377679918247895340143 30864566519877371843010215)
    ·
      refine ⟨46296849779816057764515323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30864566519877371843010215 46296849779816057764515323)
      ·
        refine ⟨69445274669724086646772985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46296849779816057764515323 69445274669724086646772985)
        ·
          refine ⟨52083956002293064985079739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69445274669724086646772985 52083956002293064985079739)
          ·
            refine ⟨78125934003439597477619609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52083956002293064985079739 78125934003439597477619609)
            ·
              refine ⟨58594450502579698108214707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78125934003439597477619609 58594450502579698108214707)
              ·
                refine ⟨87891675753869547162322061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58594450502579698108214707 87891675753869547162322061)
                ·
                  refine ⟨32959378407701080185870773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87891675753869547162322061 32959378407701080185870773)
                  ·
                    refine ⟨3089941725721976267425385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32959378407701080185870773 3089941725721976267425385)
                    ·
                      refine ⟨2317456294291482200569039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3089941725721976267425385 2317456294291482200569039)
                      ·
                        rfl

theorem cell23_4513230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2].length) (baseStart_4513230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513230 prefixEnd_4513230 := by exact prefixLift 4513230
  have htrace : WordTrace (prefixWord ++ tailWord_4513230) baseStart_4513230 baseEnd_4513230 := by
    simpa [prefixWord, tailWord_4513230, baseEnd_4513230] using wordTrace_append hprefix tailTrace_4513230
  have hstable : (prefixWord ++ tailWord_4513230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513230).length < 2 ^ (prefixWord ++ tailWord_4513230).sum := by decide
  have hdescent : baseEnd_4513230 < baseStart_4513230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513240 : List Nat := [2, 1, 2, 2, 2, 1, 5, 2, 1, 5]
def baseStart_4513240 : Nat := 118140960795 + 4513240 * 2 ^ 59
def prefixEnd_4513240 : Nat := 4983230072969 + 3 ^ 40 * 4513240 * 2
def baseEnd_4513240 : Nat := 772487143032675720481331

theorem tailTrace_4513240 : CollatzResearch.WordTrace tailWord_4513240 prefixEnd_4513240 772487143032675720481331 := by
  unfold tailWord_4513240
  simp only [CollatzResearch.WordTrace]
  refine ⟨82305693084654877435292587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109740924112873169913723449 82305693084654877435292587)
  ·
    refine ⟨123458539626982316152938881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82305693084654877435292587 123458539626982316152938881)
    ·
      refine ⟨92593904720236737114704161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123458539626982316152938881 92593904720236737114704161)
      ·
        refine ⟨69445428540177552836028121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92593904720236737114704161 69445428540177552836028121)
        ·
          refine ⟨52084071405133164627021091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69445428540177552836028121 52084071405133164627021091)
          ·
            refine ⟨78126107107699746940531637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52084071405133164627021091 78126107107699746940531637)
            ·
              refine ⟨7324322541346851275674841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78126107107699746940531637 7324322541346851275674841)
              ·
                refine ⟨5493241906010138456756131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7324322541346851275674841 5493241906010138456756131)
                ·
                  refine ⟨8239862859015207685134197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5493241906010138456756131 8239862859015207685134197)
                  ·
                    refine ⟨772487143032675720481331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8239862859015207685134197 772487143032675720481331)
                    ·
                      rfl

theorem cell23_4513240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 1, 5].length) (baseStart_4513240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513240 prefixEnd_4513240 := by exact prefixLift 4513240
  have htrace : WordTrace (prefixWord ++ tailWord_4513240) baseStart_4513240 baseEnd_4513240 := by
    simpa [prefixWord, tailWord_4513240, baseEnd_4513240] using wordTrace_append hprefix tailTrace_4513240
  have hstable : (prefixWord ++ tailWord_4513240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513240).length < 2 ^ (prefixWord ++ tailWord_4513240).sum := by decide
  have hdescent : baseEnd_4513240 < baseStart_4513240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513247 : List Nat := [1, 1, 2, 3, 3, 1, 4, 1, 2, 3, 2]
def baseStart_4513247 : Nat := 118140960795 + 4513247 * 2 ^ 59
def prefixEnd_4513247 : Nat := 4983230072969 + 3 ^ 40 * 4513247 * 2
def baseEnd_4513247 : Nat := 2317465023462608634056461

theorem tailTrace_4513247 : CollatzResearch.WordTrace tailWord_4513247 prefixEnd_4513247 2317465023462608634056461 := by
  unfold tailWord_4513247
  simp only [CollatzResearch.WordTrace]
  refine ⟨164611641480284395066089995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109741094320189596710726663 164611641480284395066089995)
  ·
    refine ⟨246917462220426592599134993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164611641480284395066089995 246917462220426592599134993)
    ·
      refine ⟨185188096665319944449351245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246917462220426592599134993 185188096665319944449351245)
      ·
        refine ⟨69445536249494979168506717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185188096665319944449351245 69445536249494979168506717)
        ·
          refine ⟨26042076093560617188190019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69445536249494979168506717 26042076093560617188190019)
          ·
            refine ⟨39063114140340925782285029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26042076093560617188190019 39063114140340925782285029)
            ·
              refine ⟨7324333901313923584178443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39063114140340925782285029 7324333901313923584178443)
              ·
                refine ⟨10986500851970885376267665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7324333901313923584178443 10986500851970885376267665)
                ·
                  refine ⟨8239875638978164032200749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10986500851970885376267665 8239875638978164032200749)
                  ·
                    refine ⟨3089953364616811512075281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8239875638978164032200749 3089953364616811512075281)
                    ·
                      refine ⟨2317465023462608634056461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3089953364616811512075281 2317465023462608634056461)
                      ·
                        rfl

theorem cell23_4513247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 3, 2].length) (baseStart_4513247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513247 prefixEnd_4513247 := by exact prefixLift 4513247
  have htrace : WordTrace (prefixWord ++ tailWord_4513247) baseStart_4513247 baseEnd_4513247 := by
    simpa [prefixWord, tailWord_4513247, baseEnd_4513247] using wordTrace_append hprefix tailTrace_4513247
  have hstable : (prefixWord ++ tailWord_4513247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513247).length < 2 ^ (prefixWord ++ tailWord_4513247).sum := by decide
  have hdescent : baseEnd_4513247 < baseStart_4513247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513273 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 5, 2, 4]
def baseStart_4513273 : Nat := 118140960795 + 4513273 * 2 ^ 59
def prefixEnd_4513273 : Nat := 4983230072969 + 3 ^ 40 * 4513273 * 2
def baseEnd_4513273 : Nat := 2317478373959625532331341

theorem tailTrace_4513273 : CollatzResearch.WordTrace tailWord_4513273 prefixEnd_4513273 2317478373959625532331341 := by
  unfold tailWord_4513273
  simp only [CollatzResearch.WordTrace]
  refine ⟨164612589778190201506536473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109741726518793467671024315 164612589778190201506536473)
  ·
    refine ⟨123459442333642651129902355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164612589778190201506536473 123459442333642651129902355)
    ·
      refine ⟨185189163500463976694853533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123459442333642651129902355 185189163500463976694853533)
      ·
        refine ⟨69445936312673991260570075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185189163500463976694853533 69445936312673991260570075)
        ·
          refine ⟨104168904469010986890855113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69445936312673991260570075 104168904469010986890855113)
          ·
            refine ⟨78126678351758240168141335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104168904469010986890855113 78126678351758240168141335)
            ·
              refine ⟨117190017527637360252212003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78126678351758240168141335 117190017527637360252212003)
              ·
                refine ⟨175785026291456040378318005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117190017527637360252212003 175785026291456040378318005)
                ·
                  refine ⟨16479846214824003785467313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 175785026291456040378318005 16479846214824003785467313)
                  ·
                    refine ⟨12359884661118002839100485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16479846214824003785467313 12359884661118002839100485)
                    ·
                      refine ⟨2317478373959625532331341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12359884661118002839100485 2317478373959625532331341)
                      ·
                        rfl

theorem cell23_4513273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_4513273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513273 prefixEnd_4513273 := by exact prefixLift 4513273
  have htrace : WordTrace (prefixWord ++ tailWord_4513273) baseStart_4513273 baseEnd_4513273 := by
    simpa [prefixWord, tailWord_4513273, baseEnd_4513273] using wordTrace_append hprefix tailTrace_4513273
  have hstable : (prefixWord ++ tailWord_4513273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513273).length < 2 ^ (prefixWord ++ tailWord_4513273).sum := by decide
  have hdescent : baseEnd_4513273 < baseStart_4513273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513287 : List Nat := [1, 1, 4, 3, 2, 1, 2, 3, 2, 4]
def baseStart_4513287 : Nat := 118140960795 + 4513287 * 2 ^ 59
def prefixEnd_4513287 : Nat := 4983230072969 + 3 ^ 40 * 4513287 * 2
def baseEnd_4513287 : Nat := 772495187562929492518759

theorem tailTrace_4513287 : CollatzResearch.WordTrace tailWord_4513287 prefixEnd_4513287 772495187562929492518759 := by
  unfold tailWord_4513287
  simp only [CollatzResearch.WordTrace]
  refine ⟨164613100400139481897546115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109742066933426321265030743 164613100400139481897546115)
  ·
    refine ⟨246919650600209222846319173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164613100400139481897546115 246919650600209222846319173)
    ·
      refine ⟨46297434487539229283684845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 246919650600209222846319173 46297434487539229283684845)
      ·
        refine ⟨17361537932827210981381817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46297434487539229283684845 17361537932827210981381817)
        ·
          refine ⟨13021153449620408236036363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17361537932827210981381817 13021153449620408236036363)
          ·
            refine ⟨19531730174430612354054545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13021153449620408236036363 19531730174430612354054545)
            ·
              refine ⟨14648797630822959265540909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19531730174430612354054545 14648797630822959265540909)
              ·
                refine ⟨5493299111558609724577841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14648797630822959265540909 5493299111558609724577841)
                ·
                  refine ⟨4119974333668957293433381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5493299111558609724577841 4119974333668957293433381)
                  ·
                    refine ⟨772495187562929492518759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4119974333668957293433381 772495187562929492518759)
                    ·
                      rfl

theorem cell23_4513287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_4513287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513287 prefixEnd_4513287 := by exact prefixLift 4513287
  have htrace : WordTrace (prefixWord ++ tailWord_4513287) baseStart_4513287 baseEnd_4513287 := by
    simpa [prefixWord, tailWord_4513287, baseEnd_4513287] using wordTrace_append hprefix tailTrace_4513287
  have hstable : (prefixWord ++ tailWord_4513287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513287).length < 2 ^ (prefixWord ++ tailWord_4513287).sum := by decide
  have hdescent : baseEnd_4513287 < baseStart_4513287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513290 : List Nat := [3, 1, 2, 2, 2, 2, 1, 3, 1, 2, 4]
def baseStart_4513290 : Nat := 118140960795 + 4513290 * 2 ^ 59
def prefixEnd_4513290 : Nat := 4983230072969 + 3 ^ 40 * 4513290 * 2
def baseEnd_4513290 : Nat := 2317487103130751965818763

theorem tailTrace_4513290 : CollatzResearch.WordTrace tailWord_4513290 prefixEnd_4513290 2317487103130751965818763 := by
  unfold tailWord_4513290
  simp only [CollatzResearch.WordTrace]
  refine ⟨41153302454782153352476331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109742139879419075606603549 41153302454782153352476331)
  ·
    refine ⟨61729953682173230028714497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41153302454782153352476331 61729953682173230028714497)
    ·
      refine ⟨46297465261629922521535873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61729953682173230028714497 46297465261629922521535873)
      ·
        refine ⟨34723098946222441891151905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46297465261629922521535873 34723098946222441891151905)
        ·
          refine ⟨26042324209666831418363929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34723098946222441891151905 26042324209666831418363929)
          ·
            refine ⟨19531743157250123563772947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26042324209666831418363929 19531743157250123563772947)
            ·
              refine ⟨29297614735875185345659421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19531743157250123563772947 29297614735875185345659421)
              ·
                refine ⟨10986605525953194504622283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29297614735875185345659421 10986605525953194504622283)
                ·
                  refine ⟨16479908288929791756933425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10986605525953194504622283 16479908288929791756933425)
                  ·
                    refine ⟨12359931216697343817700069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16479908288929791756933425 12359931216697343817700069)
                    ·
                      refine ⟨2317487103130751965818763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12359931216697343817700069 2317487103130751965818763)
                      ·
                        rfl

theorem cell23_4513290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_4513290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513290 prefixEnd_4513290 := by exact prefixLift 4513290
  have htrace : WordTrace (prefixWord ++ tailWord_4513290) baseStart_4513290 baseEnd_4513290 := by
    simpa [prefixWord, tailWord_4513290, baseEnd_4513290] using wordTrace_append hprefix tailTrace_4513290
  have hstable : (prefixWord ++ tailWord_4513290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513290).length < 2 ^ (prefixWord ++ tailWord_4513290).sum := by decide
  have hdescent : baseEnd_4513290 < baseStart_4513290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513314 : List Nat := [3, 3, 1, 1, 1, 1, 6, 1, 1, 2, 3]
def baseStart_4513314 : Nat := 118140960795 + 4513314 * 2 ^ 59
def prefixEnd_4513314 : Nat := 4983230072969 + 3 ^ 40 * 4513314 * 2
def baseEnd_4513314 : Nat := 2317499426666459871918653

theorem tailTrace_4513314 : CollatzResearch.WordTrace tailWord_4513314 prefixEnd_4513314 2317499426666459871918653 := by
  unfold tailWord_4513314
  simp only [CollatzResearch.WordTrace]
  refine ⟨41153521292760416377194749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109742723447361110339185997 41153521292760416377194749)
  ·
    refine ⟨15432570484785156141448031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41153521292760416377194749 15432570484785156141448031)
    ·
      refine ⟨23148855727177734212172047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15432570484785156141448031 23148855727177734212172047)
      ·
        refine ⟨34723283590766601318258071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23148855727177734212172047 34723283590766601318258071)
        ·
          refine ⟨52084925386149901977387107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34723283590766601318258071 52084925386149901977387107)
          ·
            refine ⟨78127388079224852966080661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52084925386149901977387107 78127388079224852966080661)
            ·
              refine ⟨3662221316213664982785031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78127388079224852966080661 3662221316213664982785031)
              ·
                refine ⟨5493331974320497474177547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3662221316213664982785031 5493331974320497474177547)
                ·
                  refine ⟨8239997961480746211266321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5493331974320497474177547 8239997961480746211266321)
                  ·
                    refine ⟨6179998471110559658449741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8239997961480746211266321 6179998471110559658449741)
                    ·
                      refine ⟨2317499426666459871918653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6179998471110559658449741 2317499426666459871918653)
                      ·
                        rfl

theorem cell23_4513314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_4513314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513314 prefixEnd_4513314 := by exact prefixLift 4513314
  have htrace : WordTrace (prefixWord ++ tailWord_4513314) baseStart_4513314 baseEnd_4513314 := by
    simpa [prefixWord, tailWord_4513314, baseEnd_4513314] using wordTrace_append hprefix tailTrace_4513314
  have hstable : (prefixWord ++ tailWord_4513314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513314).length < 2 ^ (prefixWord ++ tailWord_4513314).sum := by decide
  have hdescent : baseEnd_4513314 < baseStart_4513314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513353 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 3, 3, 5]
def baseStart_4513353 : Nat := 118140960795 + 4513353 * 2 ^ 59
def prefixEnd_4513353 : Nat := 4983230072969 + 3 ^ 40 * 4513353 * 2
def baseEnd_4513353 : Nat := 2317519452411985219330973

theorem tailTrace_4513353 : CollatzResearch.WordTrace tailWord_4513353 prefixEnd_4513353 2317519452411985219330973 := by
  unfold tailWord_4513353
  simp only [CollatzResearch.WordTrace]
  refine ⟨164615507617900375169448713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109743671745266916779632475 164615507617900375169448713)
  ·
    refine ⟨123461630713425281377086535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164615507617900375169448713 123461630713425281377086535)
    ·
      refine ⟨185192446070137922065629803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123461630713425281377086535 185192446070137922065629803)
      ·
        refine ⟨277788669105206883098444705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185192446070137922065629803 277788669105206883098444705)
        ·
          refine ⟨208341501828905162323833529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277788669105206883098444705 208341501828905162323833529)
          ·
            refine ⟨156256126371678871742875147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208341501828905162323833529 156256126371678871742875147)
            ·
              refine ⟨234384189557518307614312721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156256126371678871742875147 234384189557518307614312721)
              ·
                refine ⟨175788142168138730710734541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234384189557518307614312721 175788142168138730710734541)
                ·
                  refine ⟨65920553313052024016525453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175788142168138730710734541 65920553313052024016525453)
                  ·
                    refine ⟨24720207492394509006197045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65920553313052024016525453 24720207492394509006197045)
                    ·
                      refine ⟨2317519452411985219330973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24720207492394509006197045 2317519452411985219330973)
                      ·
                        rfl

theorem cell23_4513353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_4513353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513353 prefixEnd_4513353 := by exact prefixLift 4513353
  have htrace : WordTrace (prefixWord ++ tailWord_4513353) baseStart_4513353 baseEnd_4513353 := by
    simpa [prefixWord, tailWord_4513353, baseEnd_4513353] using wordTrace_append hprefix tailTrace_4513353
  have hstable : (prefixWord ++ tailWord_4513353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513353).length < 2 ^ (prefixWord ++ tailWord_4513353).sum := by decide
  have hdescent : baseEnd_4513353 < baseStart_4513353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513354 : List Nat := [3, 1, 2, 1, 1, 3, 4, 2, 1, 3, 2]
def baseStart_4513354 : Nat := 118140960795 + 4513354 * 2 ^ 59
def prefixEnd_4513354 : Nat := 4983230072969 + 3 ^ 40 * 4513354 * 2
def baseEnd_4513354 : Nat := 2317519965892639715418469

theorem tailTrace_4513354 : CollatzResearch.WordTrace tailWord_4513354 prefixEnd_4513354 2317519965892639715418469 := by
  unfold tailWord_4513354
  simp only [CollatzResearch.WordTrace]
  refine ⟨41153886022724188085058779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109743696060597834893490077 41153886022724188085058779)
  ·
    refine ⟨61730829034086282127588169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41153886022724188085058779 61730829034086282127588169)
    ·
      refine ⟨46298121775564711595691127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61730829034086282127588169 46298121775564711595691127)
      ·
        refine ⟨69447182663347067393536691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46298121775564711595691127 69447182663347067393536691)
        ·
          refine ⟨104170773995020601090305037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69447182663347067393536691 104170773995020601090305037)
          ·
            refine ⟨39064040248132725408864389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104170773995020601090305037 39064040248132725408864389)
            ·
              refine ⟨7324507546524886014162073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39064040248132725408864389 7324507546524886014162073)
              ·
                refine ⟨5493380659893664510621555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7324507546524886014162073 5493380659893664510621555)
                ·
                  refine ⟨8240070989840496765932333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5493380659893664510621555 8240070989840496765932333)
                  ·
                    refine ⟨3090026621190186287224625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8240070989840496765932333 3090026621190186287224625)
                    ·
                      refine ⟨2317519965892639715418469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3090026621190186287224625 2317519965892639715418469)
                      ·
                        rfl

theorem cell23_4513354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 1, 3, 2].length) (baseStart_4513354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513354 prefixEnd_4513354 := by exact prefixLift 4513354
  have htrace : WordTrace (prefixWord ++ tailWord_4513354) baseStart_4513354 baseEnd_4513354 := by
    simpa [prefixWord, tailWord_4513354, baseEnd_4513354] using wordTrace_append hprefix tailTrace_4513354
  have hstable : (prefixWord ++ tailWord_4513354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513354).length < 2 ^ (prefixWord ++ tailWord_4513354).sum := by decide
  have hdescent : baseEnd_4513354 < baseStart_4513354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513441 : List Nat := [1, 2, 3, 3, 2, 3, 2, 2, 5]
def baseStart_4513441 : Nat := 118140960795 + 4513441 * 2 ^ 59
def prefixEnd_4513441 : Nat := 4983230072969 + 3 ^ 40 * 4513441 * 2
def baseEnd_4513441 : Nat := 257507182078842319447841

theorem tailTrace_4513441 : CollatzResearch.WordTrace tailWord_4513441 prefixEnd_4513441 257507182078842319447841 := by
  unfold tailWord_4513441
  simp only [CollatzResearch.WordTrace]
  refine ⟨164618717241581566198652177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109745811494387710799101451 164618717241581566198652177)
  ·
    refine ⟨123464037931186174648989133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164618717241581566198652177 123464037931186174648989133)
    ·
      refine ⟨46299014224194815493370925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123464037931186174648989133 46299014224194815493370925)
      ·
        refine ⟨17362130334073055810014097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46299014224194815493370925 17362130334073055810014097)
        ·
          refine ⟨13021597750554791857510573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17362130334073055810014097 13021597750554791857510573)
          ·
            refine ⟨4883099156458046946566465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13021597750554791857510573 4883099156458046946566465)
            ·
              refine ⟨3662324367343535209924849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4883099156458046946566465 3662324367343535209924849)
              ·
                refine ⟨2746743275507651407443637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3662324367343535209924849 2746743275507651407443637)
                ·
                  refine ⟨257507182078842319447841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2746743275507651407443637 257507182078842319447841)
                  ·
                    rfl

theorem cell23_4513441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 5].length) (baseStart_4513441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513441 prefixEnd_4513441 := by exact prefixLift 4513441
  have htrace : WordTrace (prefixWord ++ tailWord_4513441) baseStart_4513441 baseEnd_4513441 := by
    simpa [prefixWord, tailWord_4513441, baseEnd_4513441] using wordTrace_append hprefix tailTrace_4513441
  have hstable : (prefixWord ++ tailWord_4513441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513441).length < 2 ^ (prefixWord ++ tailWord_4513441).sum := by decide
  have hdescent : baseEnd_4513441 < baseStart_4513441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513480 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 8]
def baseStart_4513480 : Nat := 118140960795 + 4513480 * 2 ^ 59
def prefixEnd_4513480 : Nat := 4983230072969 + 3 ^ 40 * 4513480 * 2
def baseEnd_4513480 : Nat := 257509407161678469160321

theorem tailTrace_4513480 : CollatzResearch.WordTrace tailWord_4513480 prefixEnd_4513480 257509407161678469160321 := by
  unfold tailWord_4513480
  simp only [CollatzResearch.WordTrace]
  refine ⟨82310069844220137929660947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109746759792293517239547929 82310069844220137929660947)
  ·
    refine ⟨123465104766330206894491421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82310069844220137929660947 123465104766330206894491421)
    ·
      refine ⟨46299414287373827585434283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123465104766330206894491421 46299414287373827585434283)
      ·
        refine ⟨69449121431060741378151425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46299414287373827585434283 69449121431060741378151425)
        ·
          refine ⟨52086841073295556033613569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69449121431060741378151425 52086841073295556033613569)
          ·
            refine ⟨39065130804971667025210177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52086841073295556033613569 39065130804971667025210177)
            ·
              refine ⟨29298848103728750268907633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39065130804971667025210177 29298848103728750268907633)
              ·
                refine ⟨21974136077796562701680725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29298848103728750268907633 21974136077796562701680725)
                ·
                  refine ⟨257509407161678469160321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21974136077796562701680725 257509407161678469160321)
                  ·
                    rfl

theorem cell23_4513480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 8].length) (baseStart_4513480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513480 prefixEnd_4513480 := by exact prefixLift 4513480
  have htrace : WordTrace (prefixWord ++ tailWord_4513480) baseStart_4513480 baseEnd_4513480 := by
    simpa [prefixWord, tailWord_4513480, baseEnd_4513480] using wordTrace_append hprefix tailTrace_4513480
  have hstable : (prefixWord ++ tailWord_4513480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513480).length < 2 ^ (prefixWord ++ tailWord_4513480).sum := by decide
  have hdescent : baseEnd_4513480 < baseStart_4513480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513497 : List Nat := [1, 2, 1, 2, 3, 3, 3, 2, 6]
def baseStart_4513497 : Nat := 118140960795 + 4513497 * 2 ^ 59
def prefixEnd_4513497 : Nat := 4983230072969 + 3 ^ 40 * 4513497 * 2
def baseEnd_4513497 : Nat := 257510377069581406214479

theorem tailTrace_4513497 : CollatzResearch.WordTrace tailWord_4513497 prefixEnd_4513497 257510377069581406214479 := by
  unfold tailWord_4513497
  simp only [CollatzResearch.WordTrace]
  refine ⟨164620759729378687762690745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109747173152919125175127163 164620759729378687762690745)
  ·
    refine ⟨123465569797034015822018059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164620759729378687762690745 123465569797034015822018059)
    ·
      refine ⟨185198354695551023733027089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123465569797034015822018059 185198354695551023733027089)
      ·
        refine ⟨138898766021663267799770317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185198354695551023733027089 138898766021663267799770317)
        ·
          refine ⟨52087037258123725424913869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138898766021663267799770317 52087037258123725424913869)
          ·
            refine ⟨19532638971796397034342701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52087037258123725424913869 19532638971796397034342701)
            ·
              refine ⟨7324739614423648887878513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19532638971796397034342701 7324739614423648887878513)
              ·
                refine ⟨5493554710817736665908885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7324739614423648887878513 5493554710817736665908885)
                ·
                  refine ⟨257510377069581406214479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5493554710817736665908885 257510377069581406214479)
                  ·
                    rfl

theorem cell23_4513497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 6].length) (baseStart_4513497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513497 prefixEnd_4513497 := by exact prefixLift 4513497
  have htrace : WordTrace (prefixWord ++ tailWord_4513497) baseStart_4513497 baseEnd_4513497 := by
    simpa [prefixWord, tailWord_4513497, baseEnd_4513497] using wordTrace_append hprefix tailTrace_4513497
  have hstable : (prefixWord ++ tailWord_4513497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513497).length < 2 ^ (prefixWord ++ tailWord_4513497).sum := by decide
  have hdescent : baseEnd_4513497 < baseStart_4513497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513527 : List Nat := [1, 1, 3, 1, 1, 1, 5, 4, 1, 5]
def baseStart_4513527 : Nat := 118140960795 + 4513527 * 2 ^ 59
def prefixEnd_4513527 : Nat := 4983230072969 + 3 ^ 40 * 4513527 * 2
def baseEnd_4513527 : Nat := 772536266015289179518391

theorem tailTrace_4513527 : CollatzResearch.WordTrace tailWord_4513527 prefixEnd_4513527 772536266015289179518391 := by
  unfold tailWord_4513527
  simp only [CollatzResearch.WordTrace]
  refine ⟨164621853919270002886282835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109747902612846668590855223 164621853919270002886282835)
  ·
    refine ⟨246932780878905004329424253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164621853919270002886282835 246932780878905004329424253)
    ·
      refine ⟨92599792829589376623534095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246932780878905004329424253 92599792829589376623534095)
      ·
        refine ⟨138899689244384064935301143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92599792829589376623534095 138899689244384064935301143)
        ·
          refine ⟨208349533866576097402951715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138899689244384064935301143 208349533866576097402951715)
          ·
            refine ⟨312524300799864146104427573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208349533866576097402951715 312524300799864146104427573)
            ·
              refine ⟨29299153199987263697290085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 312524300799864146104427573 29299153199987263697290085)
              ·
                refine ⟨5493591224997611943241891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29299153199987263697290085 5493591224997611943241891)
                ·
                  refine ⟨8240386837496417914862837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5493591224997611943241891 8240386837496417914862837)
                  ·
                    refine ⟨772536266015289179518391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8240386837496417914862837 772536266015289179518391)
                    ·
                      rfl

theorem cell23_4513527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 5].length) (baseStart_4513527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513527 prefixEnd_4513527 := by exact prefixLift 4513527
  have htrace : WordTrace (prefixWord ++ tailWord_4513527) baseStart_4513527 baseEnd_4513527 := by
    simpa [prefixWord, tailWord_4513527, baseEnd_4513527] using wordTrace_append hprefix tailTrace_4513527
  have hstable : (prefixWord ++ tailWord_4513527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513527).length < 2 ^ (prefixWord ++ tailWord_4513527).sum := by decide
  have hdescent : baseEnd_4513527 < baseStart_4513527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513542 : List Nat := [6, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_4513542 : Nat := 118140960795 + 4513542 * 2 ^ 59
def prefixEnd_4513542 : Nat := 4983230072969 + 3 ^ 40 * 4513542 * 2
def baseEnd_4513542 : Nat := 2317616500255684979867605

theorem tailTrace_4513542 : CollatzResearch.WordTrace tailWord_4513542 prefixEnd_4513542 2317616500255684979867605 := by
  unfold tailWord_4513542
  simp only [CollatzResearch.WordTrace]
  refine ⟨5144450031694239389002465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 109748267342810440298719253 5144450031694239389002465)
  ·
    refine ⟨3858337523770679541751849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5144450031694239389002465 3858337523770679541751849)
    ·
      refine ⟨2893753142828009656313887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3858337523770679541751849 2893753142828009656313887)
      ·
        refine ⟨4340629714242014484470831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2893753142828009656313887 4340629714242014484470831)
        ·
          refine ⟨6510944571363021726706247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4340629714242014484470831 6510944571363021726706247)
          ·
            refine ⟨9766416857044532590059371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6510944571363021726706247 9766416857044532590059371)
            ·
              refine ⟨14649625285566798885089057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9766416857044532590059371 14649625285566798885089057)
              ·
                refine ⟨10987218964175099163816793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14649625285566798885089057 10987218964175099163816793)
                ·
                  refine ⟨8240414223131324372862595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10987218964175099163816793 8240414223131324372862595)
                  ·
                    refine ⟨12360621334696986559293893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8240414223131324372862595 12360621334696986559293893)
                    ·
                      refine ⟨2317616500255684979867605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12360621334696986559293893 2317616500255684979867605)
                      ·
                        rfl

theorem cell23_4513542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_4513542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513542 prefixEnd_4513542 := by exact prefixLift 4513542
  have htrace : WordTrace (prefixWord ++ tailWord_4513542) baseStart_4513542 baseEnd_4513542 := by
    simpa [prefixWord, tailWord_4513542, baseEnd_4513542] using wordTrace_append hprefix tailTrace_4513542
  have hstable : (prefixWord ++ tailWord_4513542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513542).length < 2 ^ (prefixWord ++ tailWord_4513542).sum := by decide
  have hdescent : baseEnd_4513542 < baseStart_4513542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513567 : List Nat := [1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 5]
def baseStart_4513567 : Nat := 118140960795 + 4513567 * 2 ^ 59
def prefixEnd_4513567 : Nat := 4983230072969 + 3 ^ 40 * 4513567 * 2
def baseEnd_4513567 : Nat := 2317629337272047382054989

theorem tailTrace_4513567 : CollatzResearch.WordTrace tailWord_4513567 prefixEnd_4513567 2317629337272047382054989 := by
  unfold tailWord_4513567
  simp only [CollatzResearch.WordTrace]
  refine ⟨164623312839125089717738955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109748875226083393145159303 164623312839125089717738955)
  ·
    refine ⟨246934969258687634576608433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164623312839125089717738955 246934969258687634576608433)
    ·
      refine ⟨185201226944015725932456325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246934969258687634576608433 185201226944015725932456325)
      ·
        refine ⟨34725230052002948612335561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185201226944015725932456325 34725230052002948612335561)
        ·
          refine ⟨26043922539002211459251671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34725230052002948612335561 26043922539002211459251671)
          ·
            refine ⟨39065883808503317188877507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26043922539002211459251671 39065883808503317188877507)
            ·
              refine ⟨58598825712754975783316261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39065883808503317188877507 58598825712754975783316261)
              ·
                refine ⟨10987279821141557959371799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58598825712754975783316261 10987279821141557959371799)
                ·
                  refine ⟨16480919731712336939057699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10987279821141557959371799 16480919731712336939057699)
                  ·
                    refine ⟨24721379597568505408586549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16480919731712336939057699 24721379597568505408586549)
                    ·
                      refine ⟨2317629337272047382054989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24721379597568505408586549 2317629337272047382054989)
                      ·
                        rfl

theorem cell23_4513567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_4513567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513567 prefixEnd_4513567 := by exact prefixLift 4513567
  have htrace : WordTrace (prefixWord ++ tailWord_4513567) baseStart_4513567 baseEnd_4513567 := by
    simpa [prefixWord, tailWord_4513567, baseEnd_4513567] using wordTrace_append hprefix tailTrace_4513567
  have hstable : (prefixWord ++ tailWord_4513567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513567).length < 2 ^ (prefixWord ++ tailWord_4513567).sum := by decide
  have hdescent : baseEnd_4513567 < baseStart_4513567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513594 : List Nat := [3, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4]
def baseStart_4513594 : Nat := 118140960795 + 4513594 * 2 ^ 59
def prefixEnd_4513594 : Nat := 4983230072969 + 3 ^ 40 * 4513594 * 2
def baseEnd_4513594 : Nat := 2317643201249718776417365

theorem tailTrace_4513594 : CollatzResearch.WordTrace tailWord_4513594 prefixEnd_4513594 2317643201249718776417365 := by
  unfold tailWord_4513594
  simp only [CollatzResearch.WordTrace]
  refine ⟨41156074402506818332242959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109749531740018182219314557 41156074402506818332242959)
  ·
    refine ⟨61734111603760227498364439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41156074402506818332242959 61734111603760227498364439)
    ·
      refine ⟨92601167405640341247546659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61734111603760227498364439 92601167405640341247546659)
      ·
        refine ⟨138901751108460511871319989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92601167405640341247546659 138901751108460511871319989)
        ·
          refine ⟨13022039166418172987936249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 138901751108460511871319989 13022039166418172987936249)
          ·
            refine ⟨9766529374813629740952187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13022039166418172987936249 9766529374813629740952187)
            ·
              refine ⟨14649794062220444611428281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9766529374813629740952187 14649794062220444611428281)
              ·
                refine ⟨10987345546665333458571211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14649794062220444611428281 10987345546665333458571211)
                ·
                  refine ⟨16481018319998000187856817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10987345546665333458571211 16481018319998000187856817)
                  ·
                    refine ⟨12360763739998500140892613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16481018319998000187856817 12360763739998500140892613)
                    ·
                      refine ⟨2317643201249718776417365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12360763739998500140892613 2317643201249718776417365)
                      ·
                        rfl

theorem cell23_4513594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_4513594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513594 prefixEnd_4513594 := by exact prefixLift 4513594
  have htrace : WordTrace (prefixWord ++ tailWord_4513594) baseStart_4513594 baseEnd_4513594 := by
    simpa [prefixWord, tailWord_4513594, baseEnd_4513594] using wordTrace_append hprefix tailTrace_4513594
  have hstable : (prefixWord ++ tailWord_4513594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513594).length < 2 ^ (prefixWord ++ tailWord_4513594).sum := by decide
  have hdescent : baseEnd_4513594 < baseStart_4513594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513598 : List Nat := [4, 2, 1, 2, 2, 2, 3, 1, 1, 1, 4]
def baseStart_4513598 : Nat := 118140960795 + 4513598 * 2 ^ 59
def prefixEnd_4513598 : Nat := 4983230072969 + 3 ^ 40 * 4513598 * 2
def baseEnd_4513598 : Nat := 2317645255172336760767347

theorem tailTrace_4513598 : CollatzResearch.WordTrace tailWord_4513598 prefixEnd_4513598 2317645255172336760767347 := by
  unfold tailWord_4513598
  simp only [CollatzResearch.WordTrace]
  refine ⟨20578055437751597751514681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109749629001341854674744965 20578055437751597751514681)
  ·
    refine ⟨15433541578313698313636011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20578055437751597751514681 15433541578313698313636011)
    ·
      refine ⟨23150312367470547470454017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15433541578313698313636011 23150312367470547470454017)
      ·
        refine ⟨17362734275602910602840513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23150312367470547470454017 17362734275602910602840513)
        ·
          refine ⟨13022050706702182952130385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17362734275602910602840513 13022050706702182952130385)
          ·
            refine ⟨9766538030026637214097789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13022050706702182952130385 9766538030026637214097789)
            ·
              refine ⟨3662451761259988955286671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9766538030026637214097789 3662451761259988955286671)
              ·
                refine ⟨5493677641889983432930007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3662451761259988955286671 5493677641889983432930007)
                ·
                  refine ⟨8240516462834975149395011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5493677641889983432930007 8240516462834975149395011)
                  ·
                    refine ⟨12360774694252462724092517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8240516462834975149395011 12360774694252462724092517)
                    ·
                      refine ⟨2317645255172336760767347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12360774694252462724092517 2317645255172336760767347)
                      ·
                        rfl

theorem cell23_4513598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_4513598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513598 prefixEnd_4513598 := by exact prefixLift 4513598
  have htrace : WordTrace (prefixWord ++ tailWord_4513598) baseStart_4513598 baseEnd_4513598 := by
    simpa [prefixWord, tailWord_4513598, baseEnd_4513598] using wordTrace_append hprefix tailTrace_4513598
  have hstable : (prefixWord ++ tailWord_4513598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513598).length < 2 ^ (prefixWord ++ tailWord_4513598).sum := by decide
  have hdescent : baseEnd_4513598 < baseStart_4513598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513617 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 2, 7]
def baseStart_4513617 : Nat := 118140960795 + 4513617 * 2 ^ 59
def prefixEnd_4513617 : Nat := 4983230072969 + 3 ^ 40 * 4513617 * 2
def baseEnd_4513617 : Nat := 772551670434924062143253

theorem tailTrace_4513617 : CollatzResearch.WordTrace tailWord_4513617 prefixEnd_4513617 772551670434924062143253 := by
  unfold tailWord_4513617
  simp only [CollatzResearch.WordTrace]
  refine ⟨164625136488943948257059105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109750090992629298838039403 164625136488943948257059105)
  ·
    refine ⟨123468852366707961192794329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164625136488943948257059105 123468852366707961192794329)
    ·
      refine ⟨92601639275030970894595747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123468852366707961192794329 92601639275030970894595747)
      ·
        refine ⟨138902458912546456341893621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92601639275030970894595747 138902458912546456341893621)
        ·
          refine ⟨13022105523051230282052527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 138902458912546456341893621 13022105523051230282052527)
          ·
            refine ⟨19533158284576845423078791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13022105523051230282052527 19533158284576845423078791)
            ·
              refine ⟨29299737426865268134618187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19533158284576845423078791 29299737426865268134618187)
              ·
                refine ⟨43949606140297902201927281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29299737426865268134618187 43949606140297902201927281)
                ·
                  refine ⟨32962204605223426651445461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43949606140297902201927281 32962204605223426651445461)
                  ·
                    refine ⟨772551670434924062143253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32962204605223426651445461 772551670434924062143253)
                    ·
                      rfl

theorem cell23_4513617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_4513617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513617 prefixEnd_4513617 := by exact prefixLift 4513617
  have htrace : WordTrace (prefixWord ++ tailWord_4513617) baseStart_4513617 baseEnd_4513617 := by
    simpa [prefixWord, tailWord_4513617, baseEnd_4513617] using wordTrace_append hprefix tailTrace_4513617
  have hstable : (prefixWord ++ tailWord_4513617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513617).length < 2 ^ (prefixWord ++ tailWord_4513617).sum := by decide
  have hdescent : baseEnd_4513617 < baseStart_4513617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513631 : List Nat := [1, 1, 2, 3, 1, 4, 2, 3, 2, 1, 3]
def baseStart_4513631 : Nat := 118140960795 + 4513631 * 2 ^ 59
def prefixEnd_4513631 : Nat := 4983230072969 + 3 ^ 40 * 4513631 * 2
def baseEnd_4513631 : Nat := 2317662200033935131654695

theorem tailTrace_4513631 : CollatzResearch.WordTrace tailWord_4513631 prefixEnd_4513631 2317662200033935131654695 := by
  unfold tailWord_4513631
  simp only [CollatzResearch.WordTrace]
  refine ⟨164625647110893228648068747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109750431407262152432045831 164625647110893228648068747)
  ·
    refine ⟨246938470666339842972103121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164625647110893228648068747 246938470666339842972103121)
    ·
      refine ⟨185203852999754882229077341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246938470666339842972103121 185203852999754882229077341)
      ·
        refine ⟨69451444874908080835904003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185203852999754882229077341 69451444874908080835904003)
        ·
          refine ⟨104177167312362121253856005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69451444874908080835904003 104177167312362121253856005)
          ·
            refine ⟨19533218871067897735098001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104177167312362121253856005 19533218871067897735098001)
            ·
              refine ⟨14649914153300923301323501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19533218871067897735098001 14649914153300923301323501)
              ·
                refine ⟨5493717807487846237996313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14649914153300923301323501 5493717807487846237996313)
                ·
                  refine ⟨4120288355615884678497235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5493717807487846237996313 4120288355615884678497235)
                  ·
                    refine ⟨6180432533423827017745853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4120288355615884678497235 6180432533423827017745853)
                    ·
                      refine ⟨2317662200033935131654695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6180432533423827017745853 2317662200033935131654695)
                      ·
                        rfl

theorem cell23_4513631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_4513631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513631 prefixEnd_4513631 := by exact prefixLift 4513631
  have htrace : WordTrace (prefixWord ++ tailWord_4513631) baseStart_4513631 baseEnd_4513631 := by
    simpa [prefixWord, tailWord_4513631, baseEnd_4513631] using wordTrace_append hprefix tailTrace_4513631
  have hstable : (prefixWord ++ tailWord_4513631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513631).length < 2 ^ (prefixWord ++ tailWord_4513631).sum := by decide
  have hdescent : baseEnd_4513631 < baseStart_4513631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513637 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 4, 3, 4]
def baseStart_4513637 : Nat := 118140960795 + 4513637 * 2 ^ 59
def prefixEnd_4513637 : Nat := 4983230072969 + 3 ^ 40 * 4513637 * 2
def baseEnd_4513637 : Nat := 2317665280917862108179667

theorem tailTrace_4513637 : CollatzResearch.WordTrace tailWord_4513637 prefixEnd_4513637 2317665280917862108179667 := by
  unfold tailWord_4513637
  simp only [CollatzResearch.WordTrace]
  refine ⟨164625865948871491672787165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109750577299247661115191443 164625865948871491672787165)
  ·
    refine ⟨61734699730826809377295187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164625865948871491672787165 61734699730826809377295187)
    ·
      refine ⟨92602049596240214065942781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61734699730826809377295187 92602049596240214065942781)
      ·
        refine ⟨34725768598590080274728543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92602049596240214065942781 34725768598590080274728543)
        ·
          refine ⟨52088652897885120412092815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34725768598590080274728543 52088652897885120412092815)
          ·
            refine ⟨78132979346827680618139223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52088652897885120412092815 78132979346827680618139223)
            ·
              refine ⟨117199469020241520927208835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78132979346827680618139223 117199469020241520927208835)
              ·
                refine ⟨175799203530362281390813253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117199469020241520927208835 175799203530362281390813253)
                ·
                  refine ⟨32962350661942927760777485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175799203530362281390813253 32962350661942927760777485)
                  ·
                    refine ⟨12360881498228597910291557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32962350661942927760777485 12360881498228597910291557)
                    ·
                      refine ⟨2317665280917862108179667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12360881498228597910291557 2317665280917862108179667)
                      ·
                        rfl

theorem cell23_4513637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_4513637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513637 prefixEnd_4513637 := by exact prefixLift 4513637
  have htrace : WordTrace (prefixWord ++ tailWord_4513637) baseStart_4513637 baseEnd_4513637 := by
    simpa [prefixWord, tailWord_4513637, baseEnd_4513637] using wordTrace_append hprefix tailTrace_4513637
  have hstable : (prefixWord ++ tailWord_4513637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513637).length < 2 ^ (prefixWord ++ tailWord_4513637).sum := by decide
  have hdescent : baseEnd_4513637 < baseStart_4513637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513657 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 1, 3, 5]
def baseStart_4513657 : Nat := 118140960795 + 4513657 * 2 ^ 59
def prefixEnd_4513657 : Nat := 4983230072969 + 3 ^ 40 * 4513657 * 2
def baseEnd_4513657 : Nat := 2317675550530952029929575

theorem tailTrace_4513657 : CollatzResearch.WordTrace tailWord_4513657 prefixEnd_4513657 2317675550530952029929575 := by
  unfold tailWord_4513657
  simp only [CollatzResearch.WordTrace]
  refine ⟨164626595408799035088515225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109751063605866023392343483 164626595408799035088515225)
  ·
    refine ⟨123469946556599276316386419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164626595408799035088515225 123469946556599276316386419)
    ·
      refine ⟨185204919834898914474579629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123469946556599276316386419 185204919834898914474579629)
      ·
        refine ⟨69451844938087092927967361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185204919834898914474579629 69451844938087092927967361)
        ·
          refine ⟨52088883703565319695975521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69451844938087092927967361 52088883703565319695975521)
          ·
            refine ⟨39066662777673989771981641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52088883703565319695975521 39066662777673989771981641)
            ·
              refine ⟨29299997083255492328986231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39066662777673989771981641 29299997083255492328986231)
              ·
                refine ⟨43949995624883238493479347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29299997083255492328986231 43949995624883238493479347)
                ·
                  refine ⟨65924993437324857740219021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43949995624883238493479347 65924993437324857740219021)
                  ·
                    refine ⟨24721872538996821652582133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65924993437324857740219021 24721872538996821652582133)
                    ·
                      refine ⟨2317675550530952029929575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24721872538996821652582133 2317675550530952029929575)
                      ·
                        rfl

theorem cell23_4513657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_4513657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513657 prefixEnd_4513657 := by exact prefixLift 4513657
  have htrace : WordTrace (prefixWord ++ tailWord_4513657) baseStart_4513657 baseEnd_4513657 := by
    simpa [prefixWord, tailWord_4513657, baseEnd_4513657] using wordTrace_append hprefix tailTrace_4513657
  have hstable : (prefixWord ++ tailWord_4513657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513657).length < 2 ^ (prefixWord ++ tailWord_4513657).sum := by decide
  have hdescent : baseEnd_4513657 < baseStart_4513657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513658 : List Nat := [3, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2]
def baseStart_4513658 : Nat := 118140960795 + 4513658 * 2 ^ 59
def prefixEnd_4513658 : Nat := 4983230072969 + 3 ^ 40 * 4513658 * 2
def baseEnd_4513658 : Nat := 2317676064011606526017071

theorem tailTrace_4513658 : CollatzResearch.WordTrace tailWord_4513658 prefixEnd_4513658 2317676064011606526017071 := by
  unfold tailWord_4513658
  simp only [CollatzResearch.WordTrace]
  refine ⟨41156657970448853064825407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109751087921196941506201085 41156657970448853064825407)
  ·
    refine ⟨61734986955673279597238111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41156657970448853064825407 61734986955673279597238111)
    ·
      refine ⟨92602480433509919395857167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61734986955673279597238111 92602480433509919395857167)
      ·
        refine ⟨138903720650264879093785751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92602480433509919395857167 138903720650264879093785751)
        ·
          refine ⟨208355580975397318640678627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138903720650264879093785751 208355580975397318640678627)
          ·
            refine ⟨312533371463095977961017941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208355580975397318640678627 312533371463095977961017941)
            ·
              refine ⟨3662500446833155991730679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 312533371463095977961017941 3662500446833155991730679)
              ·
                refine ⟨5493750670249733987596019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3662500446833155991730679 5493750670249733987596019)
                ·
                  refine ⟨8240626005374600981394029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5493750670249733987596019 8240626005374600981394029)
                  ·
                    refine ⟨3090234752015475368022761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8240626005374600981394029 3090234752015475368022761)
                    ·
                      refine ⟨2317676064011606526017071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3090234752015475368022761 2317676064011606526017071)
                      ·
                        rfl

theorem cell23_4513658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2].length) (baseStart_4513658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513658 prefixEnd_4513658 := by exact prefixLift 4513658
  have htrace : WordTrace (prefixWord ++ tailWord_4513658) baseStart_4513658 baseEnd_4513658 := by
    simpa [prefixWord, tailWord_4513658, baseEnd_4513658] using wordTrace_append hprefix tailTrace_4513658
  have hstable : (prefixWord ++ tailWord_4513658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513658).length < 2 ^ (prefixWord ++ tailWord_4513658).sum := by decide
  have hdescent : baseEnd_4513658 < baseStart_4513658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513784 : List Nat := [2, 1, 2, 1, 1, 3, 3, 4, 6]
def baseStart_4513784 : Nat := 118140960795 + 4513784 * 2 ^ 59
def prefixEnd_4513784 : Nat := 4983230072969 + 3 ^ 40 * 4513784 * 2
def baseEnd_4513784 : Nat := 257526751397119225893499

theorem tailTrace_4513784 : CollatzResearch.WordTrace tailWord_4513784 prefixEnd_4513784 257526751397119225893499 := by
  unfold tailWord_4513784
  simp only [CollatzResearch.WordTrace]
  refine ⟨82315613739669467889194203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109754151652892623852258937 82315613739669467889194203)
  ·
    refine ⟨123473420609504201833791305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82315613739669467889194203 123473420609504201833791305)
    ·
      refine ⟨92605065457128151375343479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123473420609504201833791305 92605065457128151375343479)
      ·
        refine ⟨138907598185692227063015219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92605065457128151375343479 138907598185692227063015219)
        ·
          refine ⟨208361397278538340594522829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138907598185692227063015219 208361397278538340594522829)
          ·
            refine ⟨78135523979451877722946061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208361397278538340594522829 78135523979451877722946061)
            ·
              refine ⟨29300821492294454146104773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78135523979451877722946061 29300821492294454146104773)
              ·
                refine ⟨5493904029805210152394645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29300821492294454146104773 5493904029805210152394645)
                ·
                  refine ⟨257526751397119225893499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5493904029805210152394645 257526751397119225893499)
                  ·
                    rfl

theorem cell23_4513784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 6].length) (baseStart_4513784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513784 prefixEnd_4513784 := by exact prefixLift 4513784
  have htrace : WordTrace (prefixWord ++ tailWord_4513784) baseStart_4513784 baseEnd_4513784 := by
    simpa [prefixWord, tailWord_4513784, baseEnd_4513784] using wordTrace_append hprefix tailTrace_4513784
  have hstable : (prefixWord ++ tailWord_4513784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513784).length < 2 ^ (prefixWord ++ tailWord_4513784).sum := by decide
  have hdescent : baseEnd_4513784 < baseStart_4513784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513788 : List Nat := [2, 2, 2, 1, 2, 2, 3, 4, 1, 4]
def baseStart_4513788 : Nat := 118140960795 + 4513788 * 2 ^ 59
def prefixEnd_4513788 : Nat := 4983230072969 + 3 ^ 40 * 4513788 * 2
def baseEnd_4513788 : Nat := 772580938832230339130491

theorem tailTrace_4513788 : CollatzResearch.WordTrace tailWord_4513788 prefixEnd_4513788 772580938832230339130491 := by
  unfold tailWord_4513788
  simp only [CollatzResearch.WordTrace]
  refine ⟨82315686685662222230767009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109754248914216296307689345 82315686685662222230767009)
  ·
    refine ⟨61736765014246666673075257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82315686685662222230767009 61736765014246666673075257)
    ·
      refine ⟨46302573760685000004806443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61736765014246666673075257 46302573760685000004806443)
      ·
        refine ⟨69453860641027500007209665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46302573760685000004806443 69453860641027500007209665)
        ·
          refine ⟨52090395480770625005407249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69453860641027500007209665 52090395480770625005407249)
          ·
            refine ⟨39067796610577968754055437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52090395480770625005407249 39067796610577968754055437)
            ·
              refine ⟨14650423728966738282770789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39067796610577968754055437 14650423728966738282770789)
              ·
                refine ⟨2746954449181263428019523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14650423728966738282770789 2746954449181263428019523)
                ·
                  refine ⟨4120431673771895142029285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2746954449181263428019523 4120431673771895142029285)
                  ·
                    refine ⟨772580938832230339130491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4120431673771895142029285 772580938832230339130491)
                    ·
                      rfl

theorem cell23_4513788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_4513788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513788 prefixEnd_4513788 := by exact prefixLift 4513788
  have htrace : WordTrace (prefixWord ++ tailWord_4513788) baseStart_4513788 baseEnd_4513788 := by
    simpa [prefixWord, tailWord_4513788, baseEnd_4513788] using wordTrace_append hprefix tailTrace_4513788
  have hstable : (prefixWord ++ tailWord_4513788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513788).length < 2 ^ (prefixWord ++ tailWord_4513788).sum := by decide
  have hdescent : baseEnd_4513788 < baseStart_4513788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513811 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 5, 1, 3]
def baseStart_4513811 : Nat := 118140960795 + 4513811 * 2 ^ 59
def prefixEnd_4513811 : Nat := 4983230072969 + 3 ^ 40 * 4513811 * 2
def baseEnd_4513811 : Nat := 2317754626551744427403867

theorem tailTrace_4513811 : CollatzResearch.WordTrace tailWord_4513811 prefixEnd_4513811 2317754626551744427403867 := by
  unfold tailWord_4513811
  simp only [CollatzResearch.WordTrace]
  refine ⟨164632212250241119389621287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109754808166827412926414191 164632212250241119389621287)
  ·
    refine ⟨246948318375361679084431931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164632212250241119389621287 246948318375361679084431931)
    ·
      refine ⟨370422477563042518626647897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246948318375361679084431931 370422477563042518626647897)
      ·
        refine ⟨277816858172281888969985923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 370422477563042518626647897 277816858172281888969985923)
        ·
          refine ⟨416725287258422833454978885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277816858172281888969985923 416725287258422833454978885)
          ·
            refine ⟨78135991360954281272808541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 416725287258422833454978885 78135991360954281272808541)
            ·
              refine ⟨29300996760357855477303203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78135991360954281272808541 29300996760357855477303203)
              ·
                refine ⟨43951495140536783215954805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29300996760357855477303203 43951495140536783215954805)
                ·
                  refine ⟨4120452669425323426495763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43951495140536783215954805 4120452669425323426495763)
                  ·
                    refine ⟨6180679004137985139743645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4120452669425323426495763 6180679004137985139743645)
                    ·
                      refine ⟨2317754626551744427403867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6180679004137985139743645 2317754626551744427403867)
                      ·
                        rfl

theorem cell23_4513811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 1, 3].length) (baseStart_4513811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513811 prefixEnd_4513811 := by exact prefixLift 4513811
  have htrace : WordTrace (prefixWord ++ tailWord_4513811) baseStart_4513811 baseEnd_4513811 := by
    simpa [prefixWord, tailWord_4513811, baseEnd_4513811] using wordTrace_append hprefix tailTrace_4513811
  have hstable : (prefixWord ++ tailWord_4513811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513811).length < 2 ^ (prefixWord ++ tailWord_4513811).sum := by decide
  have hdescent : baseEnd_4513811 < baseStart_4513811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513812 : List Nat := [2, 4, 3, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_4513812 : Nat := 118140960795 + 4513812 * 2 ^ 59
def prefixEnd_4513812 : Nat := 4983230072969 + 3 ^ 40 * 4513812 * 2
def baseEnd_4513812 : Nat := 2317755140032398923491363

theorem tailTrace_4513812 : CollatzResearch.WordTrace tailWord_4513812 prefixEnd_4513812 2317755140032398923491363 := by
  unfold tailWord_4513812
  simp only [CollatzResearch.WordTrace]
  refine ⟨82316124361618748280203845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109754832482158331040271793 82316124361618748280203845)
  ·
    refine ⟨15434273317803515302538221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82316124361618748280203845 15434273317803515302538221)
    ·
      refine ⟨5787852494176318238451833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15434273317803515302538221 5787852494176318238451833)
      ·
        refine ⟨4340889370632238678838875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5787852494176318238451833 4340889370632238678838875)
        ·
          refine ⟨6511334055948358018258313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4340889370632238678838875 6511334055948358018258313)
          ·
            refine ⟨4883500541961268513693735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6511334055948358018258313 4883500541961268513693735)
            ·
              refine ⟨7325250812941902770540603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4883500541961268513693735 7325250812941902770540603)
              ·
                refine ⟨10987876219412854155810905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7325250812941902770540603 10987876219412854155810905)
                ·
                  refine ⟨8240907164559640616858179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10987876219412854155810905 8240907164559640616858179)
                  ·
                    refine ⟨12361360746839460925287269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8240907164559640616858179 12361360746839460925287269)
                    ·
                      refine ⟨2317755140032398923491363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12361360746839460925287269 2317755140032398923491363)
                      ·
                        rfl

theorem cell23_4513812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_4513812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513812 prefixEnd_4513812 := by exact prefixLift 4513812
  have htrace : WordTrace (prefixWord ++ tailWord_4513812) baseStart_4513812 baseEnd_4513812 := by
    simpa [prefixWord, tailWord_4513812, baseEnd_4513812] using wordTrace_append hprefix tailTrace_4513812
  have hstable : (prefixWord ++ tailWord_4513812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513812).length < 2 ^ (prefixWord ++ tailWord_4513812).sum := by decide
  have hdescent : baseEnd_4513812 < baseStart_4513812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513815 : List Nat := [1, 1, 3, 5, 2, 2, 1, 1, 2, 2, 3]
def baseStart_4513815 : Nat := 118140960795 + 4513815 * 2 ^ 59
def prefixEnd_4513815 : Nat := 4983230072969 + 3 ^ 40 * 4513815 * 2
def baseEnd_4513815 : Nat := 2317756680474362411753849

theorem tailTrace_4513815 : CollatzResearch.WordTrace tailWord_4513815 prefixEnd_4513815 2317756680474362411753849 := by
  unfold tailWord_4513815
  simp only [CollatzResearch.WordTrace]
  refine ⟨164632358142226628072766899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109754905428151085381844599 164632358142226628072766899)
  ·
    refine ⟨246948537213339942109150349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164632358142226628072766899 246948537213339942109150349)
    ·
      refine ⟨92605701455002478290931381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246948537213339942109150349 92605701455002478290931381)
      ·
        refine ⟨8681784511406482339774817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92605701455002478290931381 8681784511406482339774817)
        ·
          refine ⟨6511338383554861754831113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8681784511406482339774817 6511338383554861754831113)
          ·
            refine ⟨4883503787666146316123335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6511338383554861754831113 4883503787666146316123335)
            ·
              refine ⟨7325255681499219474185003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4883503787666146316123335 7325255681499219474185003)
              ·
                refine ⟨10987883522248829211277505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7325255681499219474185003 10987883522248829211277505)
                ·
                  refine ⟨8240912641686621908458129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10987883522248829211277505 8240912641686621908458129)
                  ·
                    refine ⟨6180684481264966431343597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8240912641686621908458129 6180684481264966431343597)
                    ·
                      refine ⟨2317756680474362411753849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6180684481264966431343597 2317756680474362411753849)
                      ·
                        rfl

theorem cell23_4513815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_4513815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513815 prefixEnd_4513815 := by exact prefixLift 4513815
  have htrace : WordTrace (prefixWord ++ tailWord_4513815) baseStart_4513815 baseEnd_4513815 := by
    simpa [prefixWord, tailWord_4513815, baseEnd_4513815] using wordTrace_append hprefix tailTrace_4513815
  have hstable : (prefixWord ++ tailWord_4513815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513815).length < 2 ^ (prefixWord ++ tailWord_4513815).sum := by decide
  have hdescent : baseEnd_4513815 < baseStart_4513815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513845 : List Nat := [1, 3, 3, 1, 1, 1, 4, 4, 1, 1, 3]
def baseStart_4513845 : Nat := 118140960795 + 4513845 * 2 ^ 59
def prefixEnd_4513845 : Nat := 4983230072969 + 3 ^ 40 * 4513845 * 2
def baseEnd_4513845 : Nat := 2317772084893997294378711

theorem tailTrace_4513845 : CollatzResearch.WordTrace tailWord_4513845 prefixEnd_4513845 2317772084893997294378711 := by
  unfold tailWord_4513845
  simp only [CollatzResearch.WordTrace]
  refine ⟨164633452332117943196358989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109755634888078628797572659 164633452332117943196358989)
  ·
    refine ⟨61737544624544228698634621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164633452332117943196358989 61737544624544228698634621)
    ·
      refine ⟨23151579234204085761987983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61737544624544228698634621 23151579234204085761987983)
      ·
        refine ⟨34727368851306128642981975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23151579234204085761987983 34727368851306128642981975)
        ·
          refine ⟨52091053276959192964472963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34727368851306128642981975 52091053276959192964472963)
          ·
            refine ⟨78136579915438789446709445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52091053276959192964472963 78136579915438789446709445)
            ·
              refine ⟨14650608734144773021258021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78136579915438789446709445 14650608734144773021258021)
              ·
                refine ⟨2746989137652144941485879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14650608734144773021258021 2746989137652144941485879)
                ·
                  refine ⟨4120483706478217412228819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2746989137652144941485879 4120483706478217412228819)
                  ·
                    refine ⟨6180725559717326118343229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4120483706478217412228819 6180725559717326118343229)
                    ·
                      refine ⟨2317772084893997294378711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6180725559717326118343229 2317772084893997294378711)
                      ·
                        rfl

theorem cell23_4513845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_4513845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513845 prefixEnd_4513845 := by exact prefixLift 4513845
  have htrace : WordTrace (prefixWord ++ tailWord_4513845) baseStart_4513845 baseEnd_4513845 := by
    simpa [prefixWord, tailWord_4513845, baseEnd_4513845] using wordTrace_append hprefix tailTrace_4513845
  have hstable : (prefixWord ++ tailWord_4513845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513845).length < 2 ^ (prefixWord ++ tailWord_4513845).sum := by decide
  have hdescent : baseEnd_4513845 < baseStart_4513845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513885 : List Nat := [1, 4, 4, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_4513885 : Nat := 118140960795 + 4513885 * 2 ^ 59
def prefixEnd_4513885 : Nat := 4983230072969 + 3 ^ 40 * 4513885 * 2
def baseEnd_4513885 : Nat := 2317792624120177137878527

theorem tailTrace_4513885 : CollatzResearch.WordTrace tailWord_4513885 prefixEnd_4513885 2317792624120177137878527 := by
  unfold tailWord_4513885
  simp only [CollatzResearch.WordTrace]
  refine ⟨164634911251973030027815109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109756607501315353351876739 164634911251973030027815109)
  ·
    refine ⟨30869045859744943130215333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164634911251973030027815109 30869045859744943130215333)
    ·
      refine ⟨5787946098702176836915375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30869045859744943130215333 5787946098702176836915375)
      ·
        refine ⟨8681919148053265255373063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5787946098702176836915375 8681919148053265255373063)
        ·
          refine ⟨13022878722079897883059595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8681919148053265255373063 13022878722079897883059595)
          ·
            refine ⟨19534318083119846824589393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13022878722079897883059595 19534318083119846824589393)
            ·
              refine ⟨14650738562339885118442045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19534318083119846824589393 14650738562339885118442045)
              ·
                refine ⟨5494026960877456919415767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14650738562339885118442045 5494026960877456919415767)
                ·
                  refine ⟨8241040441316185379123651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5494026960877456919415767 8241040441316185379123651)
                  ·
                    refine ⟨12361560661974278068685477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8241040441316185379123651 12361560661974278068685477)
                    ·
                      refine ⟨2317792624120177137878527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12361560661974278068685477 2317792624120177137878527)
                      ·
                        rfl

theorem cell23_4513885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_4513885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513885 prefixEnd_4513885 := by exact prefixLift 4513885
  have htrace : WordTrace (prefixWord ++ tailWord_4513885) baseStart_4513885 baseEnd_4513885 := by
    simpa [prefixWord, tailWord_4513885, baseEnd_4513885] using wordTrace_append hprefix tailTrace_4513885
  have hstable : (prefixWord ++ tailWord_4513885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513885).length < 2 ^ (prefixWord ++ tailWord_4513885).sum := by decide
  have hdescent : baseEnd_4513885 < baseStart_4513885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513888 : List Nat := [2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 3]
def baseStart_4513888 : Nat := 118140960795 + 4513888 * 2 ^ 59
def prefixEnd_4513888 : Nat := 4983230072969 + 3 ^ 40 * 4513888 * 2
def baseEnd_4513888 : Nat := 2317794164562140626141013

theorem tailTrace_4513888 : CollatzResearch.WordTrace tailWord_4513888 prefixEnd_4513888 2317794164562140626141013 := by
  unfold tailWord_4513888
  simp only [CollatzResearch.WordTrace]
  refine ⟨82317510335481080770087159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109756680447308107693449545 82317510335481080770087159)
  ·
    refine ⟨123476265503221621155130739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82317510335481080770087159 123476265503221621155130739)
    ·
      refine ⟨185214398254832431732696109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123476265503221621155130739 185214398254832431732696109)
      ·
        refine ⟨69455399345562161899761041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185214398254832431732696109 69455399345562161899761041)
        ·
          refine ⟨52091549509171621424820781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69455399345562161899761041 52091549509171621424820781)
          ·
            refine ⟨19534331065939358034307793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52091549509171621424820781 19534331065939358034307793)
            ·
              refine ⟨14650748299454518525730845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19534331065939358034307793 14650748299454518525730845)
              ·
                refine ⟨5494030612295444447149067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14650748299454518525730845 5494030612295444447149067)
                ·
                  refine ⟨8241045918443166670723601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5494030612295444447149067 8241045918443166670723601)
                  ·
                    refine ⟨6180784438832375003042701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8241045918443166670723601 6180784438832375003042701)
                    ·
                      refine ⟨2317794164562140626141013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6180784438832375003042701 2317794164562140626141013)
                      ·
                        rfl

theorem cell23_4513888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_4513888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513888 prefixEnd_4513888 := by exact prefixLift 4513888
  have htrace : WordTrace (prefixWord ++ tailWord_4513888) baseStart_4513888 baseEnd_4513888 := by
    simpa [prefixWord, tailWord_4513888, baseEnd_4513888] using wordTrace_append hprefix tailTrace_4513888
  have hstable : (prefixWord ++ tailWord_4513888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513888).length < 2 ^ (prefixWord ++ tailWord_4513888).sum := by decide
  have hdescent : baseEnd_4513888 < baseStart_4513888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513942 : List Nat := [5, 3, 2, 1, 1, 11]
def baseStart_4513942 : Nat := 118140960795 + 4513942 * 2 ^ 59
def prefixEnd_4513942 : Nat := 4983230072969 + 3 ^ 40 * 4513942 * 2
def baseEnd_4513942 : Nat := 9538361697602812406855

theorem tailTrace_4513942 : CollatzResearch.WordTrace tailWord_4513942 prefixEnd_4513942 9538361697602812406855 := by
  unfold tailWord_4513942
  simp only [CollatzResearch.WordTrace]
  refine ⟨10289811888297908047665005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109757993475177685841760053 10289811888297908047665005)
  ·
    refine ⟨3858679458111715517874377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10289811888297908047665005 3858679458111715517874377)
    ·
      refine ⟨2894009593583786638405783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3858679458111715517874377 2894009593583786638405783)
      ·
        refine ⟨4341014390375679957608675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2894009593583786638405783 4341014390375679957608675)
        ·
          refine ⟨6511521585563519936413013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4341014390375679957608675 6511521585563519936413013)
          ·
            refine ⟨9538361697602812406855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6511521585563519936413013 9538361697602812406855)
            ·
              rfl

theorem cell23_4513942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 11].length) (baseStart_4513942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513942 prefixEnd_4513942 := by exact prefixLift 4513942
  have htrace : WordTrace (prefixWord ++ tailWord_4513942) baseStart_4513942 baseEnd_4513942 := by
    simpa [prefixWord, tailWord_4513942, baseEnd_4513942] using wordTrace_append hprefix tailTrace_4513942
  have hstable : (prefixWord ++ tailWord_4513942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513942).length < 2 ^ (prefixWord ++ tailWord_4513942).sum := by decide
  have hdescent : baseEnd_4513942 < baseStart_4513942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513975 : List Nat := [1, 1, 3, 1, 4, 3, 2, 1, 1, 4, 2]
def baseStart_4513975 : Nat := 118140960795 + 4513975 * 2 ^ 59
def prefixEnd_4513975 : Nat := 4983230072969 + 3 ^ 40 * 4513975 * 2
def baseEnd_4513975 : Nat := 2317838837379081785753113

theorem tailTrace_4513975 : CollatzResearch.WordTrace tailWord_4513975 prefixEnd_4513975 2317838837379081785753113 := by
  unfold tailWord_4513975
  simp only [CollatzResearch.WordTrace]
  refine ⟨164638193821646975398591379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109758795881097983599060919 164638193821646975398591379)
  ·
    refine ⟨246957290732470463097887069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164638193821646975398591379 246957290732470463097887069)
    ·
      refine ⟨92608984024676423661707651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246957290732470463097887069 92608984024676423661707651)
      ·
        refine ⟨138913476037014635492561477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92608984024676423661707651 138913476037014635492561477)
        ·
          refine ⟨26046276756940244154855277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138913476037014635492561477 26046276756940244154855277)
          ·
            refine ⟨9767353783852591558070729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26046276756940244154855277 9767353783852591558070729)
            ·
              refine ⟨7325515337889443668553047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9767353783852591558070729 7325515337889443668553047)
              ·
                refine ⟨10988273006834165502829571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7325515337889443668553047 10988273006834165502829571)
                ·
                  refine ⟨16482409510251248254244357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10988273006834165502829571 16482409510251248254244357)
                  ·
                    refine ⟨3090451783172109047670817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16482409510251248254244357 3090451783172109047670817)
                    ·
                      refine ⟨2317838837379081785753113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3090451783172109047670817 2317838837379081785753113)
                      ·
                        rfl

theorem cell23_4513975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 4, 2].length) (baseStart_4513975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513975 prefixEnd_4513975 := by exact prefixLift 4513975
  have htrace : WordTrace (prefixWord ++ tailWord_4513975) baseStart_4513975 baseEnd_4513975 := by
    simpa [prefixWord, tailWord_4513975, baseEnd_4513975] using wordTrace_append hprefix tailTrace_4513975
  have hstable : (prefixWord ++ tailWord_4513975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513975).length < 2 ^ (prefixWord ++ tailWord_4513975).sum := by decide
  have hdescent : baseEnd_4513975 < baseStart_4513975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4513996 : List Nat := [2, 2, 1, 6, 1, 2, 2, 1, 1, 3, 2]
def baseStart_4513996 : Nat := 118140960795 + 4513996 * 2 ^ 59
def prefixEnd_4513996 : Nat := 4983230072969 + 3 ^ 40 * 4513996 * 2
def baseEnd_4513996 : Nat := 2317849620472826203590517

theorem tailTrace_4513996 : CollatzResearch.WordTrace tailWord_4513996 prefixEnd_4513996 2317849620472826203590517 := by
  unfold tailWord_4513996
  simp only [CollatzResearch.WordTrace]
  refine ⟨82319479877285447992552921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109759306503047263990070561 82319479877285447992552921)
  ·
    refine ⟨61739609907964085994414691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82319479877285447992552921 61739609907964085994414691)
    ·
      refine ⟨92609414861946128991622037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61739609907964085994414691 92609414861946128991622037)
      ·
        refine ⟨4341066321653724796482283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 92609414861946128991622037 4341066321653724796482283)
        ·
          refine ⟨6511599482480587194723425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4341066321653724796482283 6511599482480587194723425)
          ·
            refine ⟨4883699611860440396042569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6511599482480587194723425 4883699611860440396042569)
            ·
              refine ⟨3662774708895330297031927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4883699611860440396042569 3662774708895330297031927)
              ·
                refine ⟨5494162063342995445547891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3662774708895330297031927 5494162063342995445547891)
                ·
                  refine ⟨8241243095014493168321837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5494162063342995445547891 8241243095014493168321837)
                  ·
                    refine ⟨3090466160630434938120689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8241243095014493168321837 3090466160630434938120689)
                    ·
                      refine ⟨2317849620472826203590517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3090466160630434938120689 2317849620472826203590517)
                      ·
                        rfl

theorem cell23_4513996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_4513996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4513996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4513996 prefixEnd_4513996 := by exact prefixLift 4513996
  have htrace : WordTrace (prefixWord ++ tailWord_4513996) baseStart_4513996 baseEnd_4513996 := by
    simpa [prefixWord, tailWord_4513996, baseEnd_4513996] using wordTrace_append hprefix tailTrace_4513996
  have hstable : (prefixWord ++ tailWord_4513996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4513996).length < 2 ^ (prefixWord ++ tailWord_4513996).sum := by decide
  have hdescent : baseEnd_4513996 < baseStart_4513996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4513996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514008 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 2, 3, 3]
def baseStart_4514008 : Nat := 118140960795 + 4514008 * 2 ^ 59
def prefixEnd_4514008 : Nat := 4983230072969 + 3 ^ 40 * 4514008 * 2
def baseEnd_4514008 : Nat := 2317855782240680156640461

theorem tailTrace_4514008 : CollatzResearch.WordTrace tailWord_4514008 prefixEnd_4514008 2317855782240680156640461 := by
  unfold tailWord_4514008
  simp only [CollatzResearch.WordTrace]
  refine ⟨82319698715263711017271339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109759598287018281356361785 82319698715263711017271339)
  ·
    refine ⟨123479548072895566525907009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82319698715263711017271339 123479548072895566525907009)
    ·
      refine ⟨92609661054671674894430257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123479548072895566525907009 92609661054671674894430257)
      ·
        refine ⟨69457245791003756170822693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92609661054671674894430257 69457245791003756170822693)
        ·
          refine ⟨13023233585813204282029255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69457245791003756170822693 13023233585813204282029255)
          ·
            refine ⟨19534850378719806423043883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13023233585813204282029255 19534850378719806423043883)
            ·
              refine ⟨29302275568079709634565825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19534850378719806423043883 29302275568079709634565825)
              ·
                refine ⟨21976706676059782225924369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29302275568079709634565825 21976706676059782225924369)
                ·
                  refine ⟨16482530007044836669443277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21976706676059782225924369 16482530007044836669443277)
                  ·
                    refine ⟨6180948752641813751041229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16482530007044836669443277 6180948752641813751041229)
                    ·
                      refine ⟨2317855782240680156640461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6180948752641813751041229 2317855782240680156640461)
                      ·
                        rfl

theorem cell23_4514008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_4514008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514008 prefixEnd_4514008 := by exact prefixLift 4514008
  have htrace : WordTrace (prefixWord ++ tailWord_4514008) baseStart_4514008 baseEnd_4514008 := by
    simpa [prefixWord, tailWord_4514008, baseEnd_4514008] using wordTrace_append hprefix tailTrace_4514008
  have hstable : (prefixWord ++ tailWord_4514008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514008).length < 2 ^ (prefixWord ++ tailWord_4514008).sum := by decide
  have hdescent : baseEnd_4514008 < baseStart_4514008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514048 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 1, 6, 2]
def baseStart_4514048 : Nat := 118140960795 + 4514048 * 2 ^ 59
def prefixEnd_4514048 : Nat := 4983230072969 + 3 ^ 40 * 4514048 * 2
def baseEnd_4514048 : Nat := 2317876321466860000140277

theorem tailTrace_4514048 : CollatzResearch.WordTrace tailWord_4514048 prefixEnd_4514048 2317876321466860000140277 := by
  unfold tailWord_4514048
  simp only [CollatzResearch.WordTrace]
  refine ⟨82320428175191254432999399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109760570900255005910665865 82320428175191254432999399)
  ·
    refine ⟨123480642262786881649499099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82320428175191254432999399 123480642262786881649499099)
    ·
      refine ⟨185220963394180322474248649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123480642262786881649499099 185220963394180322474248649)
      ·
        refine ⟨138915722545635241855686487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185220963394180322474248649 138915722545635241855686487)
        ·
          refine ⟨208373583818452862783529731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138915722545635241855686487 208373583818452862783529731)
          ·
            refine ⟨312560375727679294175294597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208373583818452862783529731 312560375727679294175294597)
            ·
              refine ⟨58605070448939867657867737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 312560375727679294175294597 58605070448939867657867737)
              ·
                refine ⟨43953802836704900743400803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58605070448939867657867737 43953802836704900743400803)
                ·
                  refine ⟨65930704255057351115101205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43953802836704900743400803 65930704255057351115101205)
                  ·
                    refine ⟨3090501761955813333520369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65930704255057351115101205 3090501761955813333520369)
                    ·
                      refine ⟨2317876321466860000140277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3090501761955813333520369 2317876321466860000140277)
                      ·
                        rfl

theorem cell23_4514048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 1, 6, 2].length) (baseStart_4514048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514048 prefixEnd_4514048 := by exact prefixLift 4514048
  have htrace : WordTrace (prefixWord ++ tailWord_4514048) baseStart_4514048 baseEnd_4514048 := by
    simpa [prefixWord, tailWord_4514048, baseEnd_4514048] using wordTrace_append hprefix tailTrace_4514048
  have hstable : (prefixWord ++ tailWord_4514048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514048).length < 2 ^ (prefixWord ++ tailWord_4514048).sum := by decide
  have hdescent : baseEnd_4514048 < baseStart_4514048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514058 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 5, 4]
def baseStart_4514058 : Nat := 118140960795 + 4514058 * 2 ^ 59
def prefixEnd_4514058 : Nat := 4983230072969 + 3 ^ 40 * 4514058 * 2
def baseEnd_4514058 : Nat := 772627152091134987005077

theorem tailTrace_4514058 : CollatzResearch.WordTrace tailWord_4514058 prefixEnd_4514058 772627152091134987005077 := by
  unfold tailWord_4514058
  simp only [CollatzResearch.WordTrace]
  refine ⟨41160305270086570143465707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109760814053564187049241885 41160305270086570143465707)
  ·
    refine ⟨61740457905129855215198561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41160305270086570143465707 61740457905129855215198561)
    ·
      refine ⟨46305343428847391411398921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61740457905129855215198561 46305343428847391411398921)
      ·
        refine ⟨34729007571635543558549191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46305343428847391411398921 34729007571635543558549191)
        ·
          refine ⟨52093511357453315337823787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34729007571635543558549191 52093511357453315337823787)
          ·
            refine ⟨78140267036179973006735681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52093511357453315337823787 78140267036179973006735681)
            ·
              refine ⟨58605200277134979755051761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78140267036179973006735681 58605200277134979755051761)
              ·
                refine ⟨43953900207851234816288821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58605200277134979755051761 43953900207851234816288821)
                ·
                  refine ⟨4120678144486053264027077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43953900207851234816288821 4120678144486053264027077)
                  ·
                    refine ⟨772627152091134987005077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4120678144486053264027077 772627152091134987005077)
                    ·
                      rfl

theorem cell23_4514058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_4514058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514058 prefixEnd_4514058 := by exact prefixLift 4514058
  have htrace : WordTrace (prefixWord ++ tailWord_4514058) baseStart_4514058 baseEnd_4514058 := by
    simpa [prefixWord, tailWord_4514058, baseEnd_4514058] using wordTrace_append hprefix tailTrace_4514058
  have hstable : (prefixWord ++ tailWord_4514058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514058).length < 2 ^ (prefixWord ++ tailWord_4514058).sum := by decide
  have hdescent : baseEnd_4514058 < baseStart_4514058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514075 : List Nat := [1, 1, 1, 1, 1, 1, 6, 6, 1, 4]
def baseStart_4514075 : Nat := 118140960795 + 4514075 * 2 ^ 59
def prefixEnd_4514075 : Nat := 4983230072969 + 3 ^ 40 * 4514075 * 2
def baseEnd_4514075 : Nat := 772630061814843798167551

theorem tailTrace_4514075 : CollatzResearch.WordTrace tailWord_4514075 prefixEnd_4514075 772630061814843798167551 := by
  unfold tailWord_4514075
  simp only [CollatzResearch.WordTrace]
  refine ⟨164641841121284692477231679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109761227414189794984821119 164641841121284692477231679)
  ·
    refine ⟨246962761681927038715847519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164641841121284692477231679 246962761681927038715847519)
    ·
      refine ⟨370444142522890558073771279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246962761681927038715847519 370444142522890558073771279)
      ·
        refine ⟨555666213784335837110656919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370444142522890558073771279 555666213784335837110656919)
        ·
          refine ⟨833499320676503755665985379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 555666213784335837110656919 833499320676503755665985379)
          ·
            refine ⟨1250248981014755633498978069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 833499320676503755665985379 1250248981014755633498978069)
            ·
              refine ⟨58605420985066670320264597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1250248981014755633498978069 58605420985066670320264597)
              ·
                refine ⟨2747129108675000171262403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58605420985066670320264597 2747129108675000171262403)
                ·
                  refine ⟨4120693663012500256893605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2747129108675000171262403 4120693663012500256893605)
                  ·
                    refine ⟨772630061814843798167551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4120693663012500256893605 772630061814843798167551)
                    ·
                      rfl

theorem cell23_4514075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 1, 4].length) (baseStart_4514075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514075 prefixEnd_4514075 := by exact prefixLift 4514075
  have htrace : WordTrace (prefixWord ++ tailWord_4514075) baseStart_4514075 baseEnd_4514075 := by
    simpa [prefixWord, tailWord_4514075, baseEnd_4514075] using wordTrace_append hprefix tailTrace_4514075
  have hstable : (prefixWord ++ tailWord_4514075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514075).length < 2 ^ (prefixWord ++ tailWord_4514075).sum := by decide
  have hdescent : baseEnd_4514075 < baseStart_4514075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514165 : List Nat := [1, 3, 4, 1, 2, 1, 2, 2, 1, 6]
def baseStart_4514165 : Nat := 118140960795 + 4514165 * 2 ^ 59
def prefixEnd_4514165 : Nat := 4983230072969 + 3 ^ 40 * 4514165 * 2
def baseEnd_4514165 : Nat := 772645466234478680792413

theorem tailTrace_4514165 : CollatzResearch.WordTrace tailWord_4514165 prefixEnd_4514165 772645466234478680792413 := by
  unfold tailWord_4514165
  simp only [CollatzResearch.WordTrace]
  refine ⟨164645123690958637848007949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109763415793972425232005299 164645123690958637848007949)
  ·
    refine ⟨61741921384109489193002981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164645123690958637848007949 61741921384109489193002981)
    ·
      refine ⟨11576610259520529223688059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61741921384109489193002981 11576610259520529223688059)
      ·
        refine ⟨17364915389280793835532089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11576610259520529223688059 17364915389280793835532089)
        ·
          refine ⟨13023686541960595376649067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17364915389280793835532089 13023686541960595376649067)
          ·
            refine ⟨19535529812940893064973601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13023686541960595376649067 19535529812940893064973601)
            ·
              refine ⟨14651647359705669798730201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19535529812940893064973601 14651647359705669798730201)
              ·
                refine ⟨10988735519779252349047651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14651647359705669798730201 10988735519779252349047651)
                ·
                  refine ⟨16483103279668878523571477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10988735519779252349047651 16483103279668878523571477)
                  ·
                    refine ⟨772645466234478680792413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16483103279668878523571477 772645466234478680792413)
                    ·
                      rfl

theorem cell23_4514165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_4514165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514165 prefixEnd_4514165 := by exact prefixLift 4514165
  have htrace : WordTrace (prefixWord ++ tailWord_4514165) baseStart_4514165 baseEnd_4514165 := by
    simpa [prefixWord, tailWord_4514165, baseEnd_4514165] using wordTrace_append hprefix tailTrace_4514165
  have hstable : (prefixWord ++ tailWord_4514165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514165).length < 2 ^ (prefixWord ++ tailWord_4514165).sum := by decide
  have hdescent : baseEnd_4514165 < baseStart_4514165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514175 : List Nat := [1, 1, 2, 2, 1, 1, 2, 7, 1, 2, 3]
def baseStart_4514175 : Nat := 118140960795 + 4514175 * 2 ^ 59
def prefixEnd_4514175 : Nat := 4983230072969 + 3 ^ 40 * 4514175 * 2
def baseEnd_4514175 : Nat := 2317941533509981003252193

theorem tailTrace_4514175 : CollatzResearch.WordTrace tailWord_4514175 prefixEnd_4514175 2317941533509981003252193 := by
  unfold tailWord_4514175
  simp only [CollatzResearch.WordTrace]
  refine ⟨164645488420922409555871979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109763658947281606370581319 164645488420922409555871979)
  ·
    refine ⟨246968232631383614333807969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164645488420922409555871979 246968232631383614333807969)
    ·
      refine ⟨185226174473537710750355977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246968232631383614333807969 185226174473537710750355977)
      ·
        refine ⟨138919630855153283062766983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185226174473537710750355977 138919630855153283062766983)
        ·
          refine ⟨208379446282729924594150475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138919630855153283062766983 208379446282729924594150475)
          ·
            refine ⟨312569169424094886891225713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208379446282729924594150475 312569169424094886891225713)
            ·
              refine ⟨234426877068071165168419285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 312569169424094886891225713 234426877068071165168419285)
              ·
                refine ⟨5494379931282917933634827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 234426877068071165168419285 5494379931282917933634827)
                ·
                  refine ⟨8241569896924376900452241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5494379931282917933634827 8241569896924376900452241)
                  ·
                    refine ⟨6181177422693282675339181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8241569896924376900452241 6181177422693282675339181)
                    ·
                      refine ⟨2317941533509981003252193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6181177422693282675339181 2317941533509981003252193)
                      ·
                        rfl

theorem cell23_4514175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 2, 3].length) (baseStart_4514175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514175 prefixEnd_4514175 := by exact prefixLift 4514175
  have htrace : WordTrace (prefixWord ++ tailWord_4514175) baseStart_4514175 baseEnd_4514175 := by
    simpa [prefixWord, tailWord_4514175, baseEnd_4514175] using wordTrace_append hprefix tailTrace_4514175
  have hstable : (prefixWord ++ tailWord_4514175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514175).length < 2 ^ (prefixWord ++ tailWord_4514175).sum := by decide
  have hdescent : baseEnd_4514175 < baseStart_4514175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514202 : List Nat := [3, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4]
def baseStart_4514202 : Nat := 118140960795 + 4514202 * 2 ^ 59
def prefixEnd_4514202 : Nat := 4983230072969 + 3 ^ 40 * 4514202 * 2
def baseEnd_4514202 : Nat := 2317955397487652397614569

theorem tailTrace_4514202 : CollatzResearch.WordTrace tailWord_4514202 prefixEnd_4514202 2317955397487652397614569 := by
  unfold tailWord_4514202
  simp only [CollatzResearch.WordTrace]
  refine ⟨41161618297956148291776215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109764315461216395444736573 41161618297956148291776215)
  ·
    refine ⟨61742427446934222437664323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41161618297956148291776215 61742427446934222437664323)
    ·
      refine ⟨92613641170401333656496485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61742427446934222437664323 92613641170401333656496485)
      ·
        refine ⟨17365057719450250060593091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92613641170401333656496485 17365057719450250060593091)
        ·
          refine ⟨26047586579175375090889637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17365057719450250060593091 26047586579175375090889637)
          ·
            refine ⟨4883922483595382829541807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26047586579175375090889637 4883922483595382829541807)
            ·
              refine ⟨7325883725393074244312711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4883922483595382829541807 7325883725393074244312711)
              ·
                refine ⟨10988825588089611366469067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7325883725393074244312711 10988825588089611366469067)
                ·
                  refine ⟨16483238382134417049703601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10988825588089611366469067 16483238382134417049703601)
                  ·
                    refine ⟨12362428786600812787277701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16483238382134417049703601 12362428786600812787277701)
                    ·
                      refine ⟨2317955397487652397614569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12362428786600812787277701 2317955397487652397614569)
                      ·
                        rfl

theorem cell23_4514202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_4514202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514202 prefixEnd_4514202 := by exact prefixLift 4514202
  have htrace : WordTrace (prefixWord ++ tailWord_4514202) baseStart_4514202 baseEnd_4514202 := by
    simpa [prefixWord, tailWord_4514202, baseEnd_4514202] using wordTrace_append hprefix tailTrace_4514202
  have hstable : (prefixWord ++ tailWord_4514202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514202).length < 2 ^ (prefixWord ++ tailWord_4514202).sum := by decide
  have hdescent : baseEnd_4514202 < baseStart_4514202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514206 : List Nat := [4, 3, 1, 2, 1, 1, 2, 2, 3, 2, 2]
def baseStart_4514206 : Nat := 118140960795 + 4514206 * 2 ^ 59
def prefixEnd_4514206 : Nat := 4983230072969 + 3 ^ 40 * 4514206 * 2
def baseEnd_4514206 : Nat := 2317957451410270381964551

theorem tailTrace_4514206 : CollatzResearch.WordTrace tailWord_4514206 prefixEnd_4514206 2317957451410270381964551 := by
  unfold tailWord_4514206
  simp only [CollatzResearch.WordTrace]
  refine ⟨20580827385476262731281309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109764412722540067900166981 20580827385476262731281309)
  ·
    refine ⟨7717810269553598524230491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20580827385476262731281309 7717810269553598524230491)
    ·
      refine ⟨11576715404330397786345737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7717810269553598524230491 11576715404330397786345737)
      ·
        refine ⟨8682536553247798339759303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11576715404330397786345737 8682536553247798339759303)
        ·
          refine ⟨13023804829871697509638955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8682536553247798339759303 13023804829871697509638955)
          ·
            refine ⟨19535707244807546264458433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13023804829871697509638955 19535707244807546264458433)
            ·
              refine ⟨14651780433605659698343825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19535707244807546264458433 14651780433605659698343825)
              ·
                refine ⟨10988835325204244773757869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14651780433605659698343825 10988835325204244773757869)
                ·
                  refine ⟨4120813246951591790159201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10988835325204244773757869 4120813246951591790159201)
                  ·
                    refine ⟨3090609935213693842619401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4120813246951591790159201 3090609935213693842619401)
                    ·
                      refine ⟨2317957451410270381964551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3090609935213693842619401 2317957451410270381964551)
                      ·
                        rfl

theorem cell23_4514206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_4514206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514206 prefixEnd_4514206 := by exact prefixLift 4514206
  have htrace : WordTrace (prefixWord ++ tailWord_4514206) baseStart_4514206 baseEnd_4514206 := by
    simpa [prefixWord, tailWord_4514206, baseEnd_4514206] using wordTrace_append hprefix tailTrace_4514206
  have hstable : (prefixWord ++ tailWord_4514206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514206).length < 2 ^ (prefixWord ++ tailWord_4514206).sum := by decide
  have hdescent : baseEnd_4514206 < baseStart_4514206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514332 : List Nat := [2, 2, 3, 1, 2, 2, 3, 1, 2, 5]
def baseStart_4514332 : Nat := 118140960795 + 4514332 * 2 ^ 59
def prefixEnd_4514332 : Nat := 4983230072969 + 3 ^ 40 * 4514332 * 2
def baseEnd_4514332 : Nat := 772674049990912296329657

theorem tailTrace_4514332 : CollatzResearch.WordTrace tailWord_4514332 prefixEnd_4514332 772674049990912296329657 := by
  unfold tailWord_4514332
  simp only [CollatzResearch.WordTrace]
  refine ⟨82325607340676812684668625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109767476454235750246224833 82325607340676812684668625)
  ·
    refine ⟨61744205505507609513501469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82325607340676812684668625 61744205505507609513501469)
    ·
      refine ⟨23154077064565353567563051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61744205505507609513501469 23154077064565353567563051)
      ·
        refine ⟨34731115596848030351344577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23154077064565353567563051 34731115596848030351344577)
        ·
          refine ⟨26048336697636022763508433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34731115596848030351344577 26048336697636022763508433)
          ·
            refine ⟨19536252523227017072631325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26048336697636022763508433 19536252523227017072631325)
            ·
              refine ⟨7326094696210131402236747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19536252523227017072631325 7326094696210131402236747)
              ·
                refine ⟨10989142044315197103355121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7326094696210131402236747 10989142044315197103355121)
                ·
                  refine ⟨8241856533236397827516341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10989142044315197103355121 8241856533236397827516341)
                  ·
                    refine ⟨772674049990912296329657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8241856533236397827516341 772674049990912296329657)
                    ·
                      rfl

theorem cell23_4514332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_4514332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514332 prefixEnd_4514332 := by exact prefixLift 4514332
  have htrace : WordTrace (prefixWord ++ tailWord_4514332) baseStart_4514332 baseEnd_4514332 := by
    simpa [prefixWord, tailWord_4514332, baseEnd_4514332] using wordTrace_append hprefix tailTrace_4514332
  have hstable : (prefixWord ++ tailWord_4514332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514332).length < 2 ^ (prefixWord ++ tailWord_4514332).sum := by decide
  have hdescent : baseEnd_4514332 < baseStart_4514332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514352 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 2, 4, 2]
def baseStart_4514352 : Nat := 118140960795 + 4514352 * 2 ^ 59
def prefixEnd_4514352 : Nat := 4983230072969 + 3 ^ 40 * 4514352 * 2
def baseEnd_4514352 : Nat := 2318032419585826810738879

theorem tailTrace_4514352 : CollatzResearch.WordTrace tailWord_4514352 prefixEnd_4514352 2318032419585826810738879 := by
  unfold tailWord_4514352
  simp only [CollatzResearch.WordTrace]
  refine ⟨82325972070640584392532655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109767962760854112523376873 82325972070640584392532655)
  ·
    refine ⟨123488958105960876588798983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82325972070640584392532655 123488958105960876588798983)
    ·
      refine ⟨185233437158941314883198475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123488958105960876588798983 185233437158941314883198475)
      ·
        refine ⟨277850155738411972324797713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185233437158941314883198475 277850155738411972324797713)
        ·
          refine ⟨208387616803808979243598285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277850155738411972324797713 208387616803808979243598285)
          ·
            refine ⟨78145356301428367216349357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208387616803808979243598285 78145356301428367216349357)
            ·
              refine ⟨29304508613035637706131009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78145356301428367216349357 29304508613035637706131009)
              ·
                refine ⟨21978381459776728279598257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29304508613035637706131009 21978381459776728279598257)
                ·
                  refine ⟨16483786094832546209698693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21978381459776728279598257 16483786094832546209698693)
                  ·
                    refine ⟨3090709892781102414318505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16483786094832546209698693 3090709892781102414318505)
                    ·
                      refine ⟨2318032419585826810738879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3090709892781102414318505 2318032419585826810738879)
                      ·
                        rfl

theorem cell23_4514352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 2, 4, 2].length) (baseStart_4514352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514352 prefixEnd_4514352 := by exact prefixLift 4514352
  have htrace : WordTrace (prefixWord ++ tailWord_4514352) baseStart_4514352 baseEnd_4514352 := by
    simpa [prefixWord, tailWord_4514352, baseEnd_4514352] using wordTrace_append hprefix tailTrace_4514352
  have hstable : (prefixWord ++ tailWord_4514352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514352).length < 2 ^ (prefixWord ++ tailWord_4514352).sum := by decide
  have hdescent : baseEnd_4514352 < baseStart_4514352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514362 : List Nat := [3, 1, 1, 1, 3, 3, 1, 3, 3, 4]
def baseStart_4514362 : Nat := 118140960795 + 4514362 * 2 ^ 59
def prefixEnd_4514362 : Nat := 4983230072969 + 3 ^ 40 * 4514362 * 2
def baseEnd_4514362 : Nat := 772679184797457257204611

theorem tailTrace_4514362 : CollatzResearch.WordTrace tailWord_4514362 prefixEnd_4514362 772679184797457257204611 := by
  unfold tailWord_4514362
  simp only [CollatzResearch.WordTrace]
  refine ⟨41163077217811235123232335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109768205914163293661952893 41163077217811235123232335)
  ·
    refine ⟨61744615826716852684848503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41163077217811235123232335 61744615826716852684848503)
    ·
      refine ⟨92616923740075279027272755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61744615826716852684848503 92616923740075279027272755)
      ·
        refine ⟨138925385610112918540909133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92616923740075279027272755 138925385610112918540909133)
        ·
          refine ⟨52097019603792344452840925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138925385610112918540909133 52097019603792344452840925)
          ·
            refine ⟨19536382351422129169815347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52097019603792344452840925 19536382351422129169815347)
            ·
              refine ⟨29304573527133193754723021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19536382351422129169815347 29304573527133193754723021)
              ·
                refine ⟨10989215072674947658021133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29304573527133193754723021 10989215072674947658021133)
                ·
                  refine ⟨4120955652253105371757925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10989215072674947658021133 4120955652253105371757925)
                  ·
                    refine ⟨772679184797457257204611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4120955652253105371757925 772679184797457257204611)
                    ·
                      rfl

theorem cell23_4514362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 3, 4].length) (baseStart_4514362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514362 prefixEnd_4514362 := by exact prefixLift 4514362
  have htrace : WordTrace (prefixWord ++ tailWord_4514362) baseStart_4514362 baseEnd_4514362 := by
    simpa [prefixWord, tailWord_4514362, baseEnd_4514362] using wordTrace_append hprefix tailTrace_4514362
  have hstable : (prefixWord ++ tailWord_4514362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514362).length < 2 ^ (prefixWord ++ tailWord_4514362).sum := by decide
  have hdescent : baseEnd_4514362 < baseStart_4514362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514369 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 2, 4, 2]
def baseStart_4514369 : Nat := 118140960795 + 4514369 * 2 ^ 59
def prefixEnd_4514369 : Nat := 4983230072969 + 3 ^ 40 * 4514369 * 2
def baseEnd_4514369 : Nat := 2318041148756953244226301

theorem tailTrace_4514369 : CollatzResearch.WordTrace tailWord_4514369 prefixEnd_4514369 2318041148756953244226301 := by
  unfold tailWord_4514369
  simp only [CollatzResearch.WordTrace]
  refine ⟨164652564182219580688434161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109768376121479720458956107 164652564182219580688434161)
  ·
    refine ⟨123489423136664685516325621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164652564182219580688434161 123489423136664685516325621)
    ·
      refine ⟨11577133419062314267155527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123489423136664685516325621 11577133419062314267155527)
      ·
        refine ⟨17365700128593471400733291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11577133419062314267155527 17365700128593471400733291)
        ·
          refine ⟨26048550192890207101099937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17365700128593471400733291 26048550192890207101099937)
          ·
            refine ⟨19536412644667655325824953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26048550192890207101099937 19536412644667655325824953)
            ·
              refine ⟨14652309483500741494368715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19536412644667655325824953 14652309483500741494368715)
              ·
                refine ⟨21978464225251112241553073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14652309483500741494368715 21978464225251112241553073)
                ·
                  refine ⟨16483848168938334181164805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21978464225251112241553073 16483848168938334181164805)
                  ·
                    refine ⟨3090721531675937658968401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16483848168938334181164805 3090721531675937658968401)
                    ·
                      refine ⟨2318041148756953244226301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3090721531675937658968401 2318041148756953244226301)
                      ·
                        rfl

theorem cell23_4514369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_4514369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514369 prefixEnd_4514369 := by exact prefixLift 4514369
  have htrace : WordTrace (prefixWord ++ tailWord_4514369) baseStart_4514369 baseEnd_4514369 := by
    simpa [prefixWord, tailWord_4514369, baseEnd_4514369] using wordTrace_append hprefix tailTrace_4514369
  have hstable : (prefixWord ++ tailWord_4514369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514369).length < 2 ^ (prefixWord ++ tailWord_4514369).sum := by decide
  have hdescent : baseEnd_4514369 < baseStart_4514369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514413 : List Nat := [1, 5, 1, 1, 3, 2, 3, 2, 1, 4]
def baseStart_4514413 : Nat := 118140960795 + 4514413 * 2 ^ 59
def prefixEnd_4514413 : Nat := 4983230072969 + 3 ^ 40 * 4514413 * 2
def baseEnd_4514413 : Nat := 772687913968583690692033

theorem tailTrace_4514413 : CollatzResearch.WordTrace tailWord_4514413 prefixEnd_4514413 772687913968583690692033 := by
  unfold tailWord_4514413
  simp only [CollatzResearch.WordTrace]
  refine ⟨164654168994060176203035893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109769445996040117468690595 164654168994060176203035893)
  ·
    refine ⟨15436328343193141519034615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 164654168994060176203035893 15436328343193141519034615)
    ·
      refine ⟨23154492514789712278551923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15436328343193141519034615 23154492514789712278551923)
      ·
        refine ⟨34731738772184568417827885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23154492514789712278551923 34731738772184568417827885)
        ·
          refine ⟨13024402039569213156685457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34731738772184568417827885 13024402039569213156685457)
          ·
            refine ⟨9768301529676909867514093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13024402039569213156685457 9768301529676909867514093)
            ·
              refine ⟨3663113073628841200317785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9768301529676909867514093 3663113073628841200317785)
              ·
                refine ⟨2747334805221630900238339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3663113073628841200317785 2747334805221630900238339)
                ·
                  refine ⟨4121002207832446350357509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2747334805221630900238339 4121002207832446350357509)
                  ·
                    refine ⟨772687913968583690692033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4121002207832446350357509 772687913968583690692033)
                    ·
                      rfl

theorem cell23_4514413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_4514413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514413 prefixEnd_4514413 := by exact prefixLift 4514413
  have htrace : WordTrace (prefixWord ++ tailWord_4514413) baseStart_4514413 baseEnd_4514413 := by
    simpa [prefixWord, tailWord_4514413, baseEnd_4514413] using wordTrace_append hprefix tailTrace_4514413
  have hstable : (prefixWord ++ tailWord_4514413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514413).length < 2 ^ (prefixWord ++ tailWord_4514413).sum := by decide
  have hdescent : baseEnd_4514413 < baseStart_4514413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514446 : List Nat := [4, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2]
def baseStart_4514446 : Nat := 118140960795 + 4514446 * 2 ^ 59
def prefixEnd_4514446 : Nat := 4983230072969 + 3 ^ 40 * 4514446 * 2
def baseEnd_4514446 : Nat := 2318080686767349442963447

theorem tailTrace_4514446 : CollatzResearch.WordTrace tailWord_4514446 prefixEnd_4514446 2318080686767349442963447 := by
  unfold tailWord_4514446
  simp only [CollatzResearch.WordTrace]
  refine ⟨20581921575367577854873399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109770248401960415225991461 20581921575367577854873399)
  ·
    refine ⟨30872882363051366782310099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20581921575367577854873399 30872882363051366782310099)
    ·
      refine ⟨46309323544577050173465149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30872882363051366782310099 46309323544577050173465149)
      ·
        refine ⟨17365996329216393815049431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46309323544577050173465149 17365996329216393815049431)
        ·
          refine ⟨26048994493824590722574147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17365996329216393815049431 26048994493824590722574147)
          ·
            refine ⟨39073491740736886083861221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26048994493824590722574147 39073491740736886083861221)
            ·
              refine ⟨7326279701388166140723979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39073491740736886083861221 7326279701388166140723979)
              ·
                refine ⟨10989419552082249211085969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7326279701388166140723979 10989419552082249211085969)
                ·
                  refine ⟨8242064664061686908314477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10989419552082249211085969 8242064664061686908314477)
                  ·
                    refine ⟨3090774249023132590617929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8242064664061686908314477 3090774249023132590617929)
                    ·
                      refine ⟨2318080686767349442963447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3090774249023132590617929 2318080686767349442963447)
                      ·
                        rfl

theorem cell23_4514446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_4514446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514446 prefixEnd_4514446 := by exact prefixLift 4514446
  have htrace : WordTrace (prefixWord ++ tailWord_4514446) baseStart_4514446 baseEnd_4514446 := by
    simpa [prefixWord, tailWord_4514446, baseEnd_4514446] using wordTrace_append hprefix tailTrace_4514446
  have hstable : (prefixWord ++ tailWord_4514446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514446).length < 2 ^ (prefixWord ++ tailWord_4514446).sum := by decide
  have hdescent : baseEnd_4514446 < baseStart_4514446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514465 : List Nat := [1, 2, 3, 3, 14]
def baseStart_4514465 : Nat := 118140960795 + 4514465 * 2 ^ 59
def prefixEnd_4514465 : Nat := 4983230072969 + 3 ^ 40 * 4514465 * 2
def baseEnd_4514465 : Nat := 3179822281069663742971

theorem tailTrace_4514465 : CollatzResearch.WordTrace tailWord_4514465 prefixEnd_4514465 3179822281069663742971 := by
  unfold tailWord_4514465
  simp only [CollatzResearch.WordTrace]
  refine ⟨164656065589871789083928849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109770710393247859389285899 164656065589871789083928849)
  ·
    refine ⟨123492049192403841812946637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164656065589871789083928849 123492049192403841812946637)
    ·
      refine ⟨46309518447151440679854989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123492049192403841812946637 46309518447151440679854989)
      ·
        refine ⟨17366069417681790254945621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46309518447151440679854989 17366069417681790254945621)
        ·
          refine ⟨3179822281069663742971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 17366069417681790254945621 3179822281069663742971)
          ·
            rfl

theorem cell23_4514465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 14].length) (baseStart_4514465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514465 prefixEnd_4514465 := by exact prefixLift 4514465
  have htrace : WordTrace (prefixWord ++ tailWord_4514465) baseStart_4514465 baseEnd_4514465 := by
    simpa [prefixWord, tailWord_4514465, baseEnd_4514465] using wordTrace_append hprefix tailTrace_4514465
  have hstable : (prefixWord ++ tailWord_4514465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514465).length < 2 ^ (prefixWord ++ tailWord_4514465).sum := by decide
  have hdescent : baseEnd_4514465 < baseStart_4514465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514497 : List Nat := [1, 2, 6, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_4514497 : Nat := 118140960795 + 4514497 * 2 ^ 59
def prefixEnd_4514497 : Nat := 4983230072969 + 3 ^ 40 * 4514497 * 2
def baseEnd_4514497 : Nat := 2318106874280728743425713

theorem tailTrace_4514497 : CollatzResearch.WordTrace tailWord_4514497 prefixEnd_4514497 2318106874280728743425713 := by
  unfold tailWord_4514497
  simp only [CollatzResearch.WordTrace]
  refine ⟨164657232725755858549093745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109771488483837239032729163 164657232725755858549093745)
  ·
    refine ⟨123492924544316893911820309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164657232725755858549093745 123492924544316893911820309)
    ·
      refine ⟨5788730838014854402116577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 123492924544316893911820309 5788730838014854402116577)
      ·
        refine ⟨4341548128511140801587433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5788730838014854402116577 4341548128511140801587433)
        ·
          refine ⟨3256161096383355601190575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4341548128511140801587433 3256161096383355601190575)
          ·
            refine ⟨4884241644575033401785863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3256161096383355601190575 4884241644575033401785863)
            ·
              refine ⟨7326362466862550102678795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4884241644575033401785863 7326362466862550102678795)
              ·
                refine ⟨10989543700293825154018193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7326362466862550102678795 10989543700293825154018193)
                ·
                  refine ⟨8242157775220368865513645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10989543700293825154018193 8242157775220368865513645)
                  ·
                    refine ⟨3090809165707638324567617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8242157775220368865513645 3090809165707638324567617)
                    ·
                      refine ⟨2318106874280728743425713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3090809165707638324567617 2318106874280728743425713)
                      ·
                        rfl

theorem cell23_4514497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_4514497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514497 prefixEnd_4514497 := by exact prefixLift 4514497
  have htrace : WordTrace (prefixWord ++ tailWord_4514497) baseStart_4514497 baseEnd_4514497 := by
    simpa [prefixWord, tailWord_4514497, baseEnd_4514497] using wordTrace_append hprefix tailTrace_4514497
  have hstable : (prefixWord ++ tailWord_4514497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514497).length < 2 ^ (prefixWord ++ tailWord_4514497).sum := by decide
  have hdescent : baseEnd_4514497 < baseStart_4514497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514510 : List Nat := [4, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2]
def baseStart_4514510 : Nat := 118140960795 + 4514510 * 2 ^ 59
def prefixEnd_4514510 : Nat := 4983230072969 + 3 ^ 40 * 4514510 * 2
def baseEnd_4514510 : Nat := 2318113549529237192563153

theorem tailTrace_4514510 : CollatzResearch.WordTrace tailWord_4514510 prefixEnd_4514510 2318113549529237192563153 := by
  unfold tailWord_4514510
  simp only [CollatzResearch.WordTrace]
  refine ⟨20582213359338595221164623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109771804583139174512877989 20582213359338595221164623)
  ·
    refine ⟨30873320039007892831746935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20582213359338595221164623 30873320039007892831746935)
    ·
      refine ⟨46309980058511839247620403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30873320039007892831746935 46309980058511839247620403)
      ·
        refine ⟨69464970087767758871430605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46309980058511839247620403 69464970087767758871430605)
        ·
          refine ⟨26049363782912909576786477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69464970087767758871430605 26049363782912909576786477)
          ·
            refine ⟨9768511418592341091294929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26049363782912909576786477 9768511418592341091294929)
            ·
              refine ⟨7326383563944255818471197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9768511418592341091294929 7326383563944255818471197)
              ·
                refine ⟨2747393836479095931926699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7326383563944255818471197 2747393836479095931926699)
                ·
                  refine ⟨4121090754718643897890049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2747393836479095931926699 4121090754718643897890049)
                  ·
                    refine ⟨3090818066038982923417537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4121090754718643897890049 3090818066038982923417537)
                    ·
                      refine ⟨2318113549529237192563153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3090818066038982923417537 2318113549529237192563153)
                      ·
                        rfl

theorem cell23_4514510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2].length) (baseStart_4514510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514510 prefixEnd_4514510 := by exact prefixLift 4514510
  have htrace : WordTrace (prefixWord ++ tailWord_4514510) baseStart_4514510 baseEnd_4514510 := by
    simpa [prefixWord, tailWord_4514510, baseEnd_4514510] using wordTrace_append hprefix tailTrace_4514510
  have hstable : (prefixWord ++ tailWord_4514510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514510).length < 2 ^ (prefixWord ++ tailWord_4514510).sum := by decide
  have hdescent : baseEnd_4514510 < baseStart_4514510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514543 : List Nat := [1, 1, 2, 1, 5, 3, 3, 1, 2, 1, 3]
def baseStart_4514543 : Nat := 118140960795 + 4514543 * 2 ^ 59
def prefixEnd_4514543 : Nat := 4983230072969 + 3 ^ 40 * 4514543 * 2
def baseEnd_4514543 : Nat := 2318130494390835563450501

theorem tailTrace_4514543 : CollatzResearch.WordTrace tailWord_4514543 prefixEnd_4514543 2318130494390835563450501 := by
  unfold tailWord_4514543
  simp only [CollatzResearch.WordTrace]
  refine ⟨164658910483589208405268283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109772606989059472270178855 164658910483589208405268283)
  ·
    refine ⟨246988365725383812607902425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164658910483589208405268283 246988365725383812607902425)
    ·
      refine ⟨185241274294037859455926819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246988365725383812607902425 185241274294037859455926819)
      ·
        refine ⟨277861911441056789183890229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185241274294037859455926819 277861911441056789183890229)
        ·
          refine ⟨26049554197599073985989709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 277861911441056789183890229 26049554197599073985989709)
          ·
            refine ⟨9768582824099652744746141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26049554197599073985989709 9768582824099652744746141)
            ·
              refine ⟨3663218559037369779279803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9768582824099652744746141 3663218559037369779279803)
              ·
                refine ⟨5494827838556054668919705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3663218559037369779279803 5494827838556054668919705)
                ·
                  refine ⟨4121120878917041001689779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5494827838556054668919705 4121120878917041001689779)
                  ·
                    refine ⟨6181681318375561502534669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4121120878917041001689779 6181681318375561502534669)
                    ·
                      refine ⟨2318130494390835563450501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6181681318375561502534669 2318130494390835563450501)
                      ·
                        rfl

theorem cell23_4514543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 2, 1, 3].length) (baseStart_4514543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514543 prefixEnd_4514543 := by exact prefixLift 4514543
  have htrace : WordTrace (prefixWord ++ tailWord_4514543) baseStart_4514543 baseEnd_4514543 := by
    simpa [prefixWord, tailWord_4514543, baseEnd_4514543] using wordTrace_append hprefix tailTrace_4514543
  have hstable : (prefixWord ++ tailWord_4514543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514543).length < 2 ^ (prefixWord ++ tailWord_4514543).sum := by decide
  have hdescent : baseEnd_4514543 < baseStart_4514543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514552 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 2, 1, 5]
def baseStart_4514552 : Nat := 118140960795 + 4514552 * 2 ^ 59
def prefixEnd_4514552 : Nat := 4983230072969 + 3 ^ 40 * 4514552 * 2
def baseEnd_4514552 : Nat := 2318135115716726028237959

theorem tailTrace_4514552 : CollatzResearch.WordTrace tailWord_4514552 prefixEnd_4514552 2318135115716726028237959 := by
  unfold tailWord_4514552
  simp only [CollatzResearch.WordTrace]
  refine ⟨82329619370278301471172955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109772825827037735294897273 82329619370278301471172955)
  ·
    refine ⟨123494429055417452206759433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82329619370278301471172955 123494429055417452206759433)
    ·
      refine ⟨92620821791563089155069575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123494429055417452206759433 92620821791563089155069575)
      ·
        refine ⟨138931232687344633732604363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92620821791563089155069575 138931232687344633732604363)
        ·
          refine ⟨208396849031016950598906545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138931232687344633732604363 208396849031016950598906545)
          ·
            refine ⟨156297636773262712949179909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208396849031016950598906545 156297636773262712949179909)
            ·
              refine ⟨29305806894986758677971233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 156297636773262712949179909 29305806894986758677971233)
              ·
                refine ⟨21979355171240069008478425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29305806894986758677971233 21979355171240069008478425)
                ·
                  refine ⟨16484516378430051756358819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21979355171240069008478425 16484516378430051756358819)
                  ·
                    refine ⟨24726774567645077634538229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16484516378430051756358819 24726774567645077634538229)
                    ·
                      refine ⟨2318135115716726028237959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24726774567645077634538229 2318135115716726028237959)
                      ·
                        rfl

theorem cell23_4514552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_4514552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514552 prefixEnd_4514552 := by exact prefixLift 4514552
  have htrace : WordTrace (prefixWord ++ tailWord_4514552) baseStart_4514552 baseEnd_4514552 := by
    simpa [prefixWord, tailWord_4514552, baseEnd_4514552] using wordTrace_append hprefix tailTrace_4514552
  have hstable : (prefixWord ++ tailWord_4514552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514552).length < 2 ^ (prefixWord ++ tailWord_4514552).sum := by decide
  have hdescent : baseEnd_4514552 < baseStart_4514552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514639 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 5, 6, 2]
def baseStart_4514639 : Nat := 118140960795 + 4514639 * 2 ^ 59
def prefixEnd_4514639 : Nat := 4983230072969 + 3 ^ 40 * 4514639 * 2
def baseEnd_4514639 : Nat := 2318179788533667187850059

theorem tailTrace_4514639 : CollatzResearch.WordTrace tailWord_4514639 prefixEnd_4514639 2318179788533667187850059 := by
  unfold tailWord_4514639
  simp only [CollatzResearch.WordTrace]
  refine ⟨164662411891241416800762971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109774941260827611200508647 164662411891241416800762971)
  ·
    refine ⟨246993617836862125201144457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164662411891241416800762971 246993617836862125201144457)
    ·
      refine ⟨185245213377646593900858343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246993617836862125201144457 185245213377646593900858343)
      ·
        refine ⟨277867820066469890851287515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185245213377646593900858343 277867820066469890851287515)
        ·
          refine ⟨416801730099704836276931273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277867820066469890851287515 416801730099704836276931273)
          ·
            refine ⟨312601297574778627207698455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 416801730099704836276931273 312601297574778627207698455)
            ·
              refine ⟨468901946362167940811547683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312601297574778627207698455 468901946362167940811547683)
              ·
                refine ⟨703352919543251911217321525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468901946362167940811547683 703352919543251911217321525)
                ·
                  refine ⟨65939336207179866676623893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 703352919543251911217321525 65939336207179866676623893)
                  ·
                    refine ⟨3090906384711556250466745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65939336207179866676623893 3090906384711556250466745)
                    ·
                      refine ⟨2318179788533667187850059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3090906384711556250466745 2318179788533667187850059)
                      ·
                        rfl

theorem cell23_4514639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 6, 2].length) (baseStart_4514639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514639 prefixEnd_4514639 := by exact prefixLift 4514639
  have htrace : WordTrace (prefixWord ++ tailWord_4514639) baseStart_4514639 baseEnd_4514639 := by
    simpa [prefixWord, tailWord_4514639, baseEnd_4514639] using wordTrace_append hprefix tailTrace_4514639
  have hstable : (prefixWord ++ tailWord_4514639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514639).length < 2 ^ (prefixWord ++ tailWord_4514639).sum := by decide
  have hdescent : baseEnd_4514639 < baseStart_4514639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514656 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 2, 4, 2]
def baseStart_4514656 : Nat := 118140960795 + 4514656 * 2 ^ 59
def prefixEnd_4514656 : Nat := 4983230072969 + 3 ^ 40 * 4514656 * 2
def baseEnd_4514656 : Nat := 2318188517704793621337481

theorem tailTrace_4514656 : CollatzResearch.WordTrace tailWord_4514656 prefixEnd_4514656 2318188517704793621337481 := by
  unfold tailWord_4514656
  simp only [CollatzResearch.WordTrace]
  refine ⟨82331515966089914352065911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109775354621453219136087881 82331515966089914352065911)
  ·
    refine ⟨123497273949134871528098867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82331515966089914352065911 123497273949134871528098867)
    ·
      refine ⟨185245910923702307292148301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123497273949134871528098867 185245910923702307292148301)
      ·
        refine ⟨69467216596388365234555613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185245910923702307292148301 69467216596388365234555613)
        ·
          refine ⟨26050206223645636962958355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69467216596388365234555613 26050206223645636962958355)
          ·
            refine ⟨39075309335468455444437533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26050206223645636962958355 39075309335468455444437533)
            ·
              refine ⟨14653241000800670791664075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39075309335468455444437533 14653241000800670791664075)
              ·
                refine ⟨21979861501201006187496113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14653241000800670791664075 21979861501201006187496113)
                ·
                  refine ⟨16484896125900754640622085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21979861501201006187496113 16484896125900754640622085)
                  ·
                    refine ⟨3090918023606391495116641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16484896125900754640622085 3090918023606391495116641)
                    ·
                      refine ⟨2318188517704793621337481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3090918023606391495116641 2318188517704793621337481)
                      ·
                        rfl

theorem cell23_4514656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 2, 4, 2].length) (baseStart_4514656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514656 prefixEnd_4514656 := by exact prefixLift 4514656
  have htrace : WordTrace (prefixWord ++ tailWord_4514656) baseStart_4514656 baseEnd_4514656 := by
    simpa [prefixWord, tailWord_4514656, baseEnd_4514656] using wordTrace_append hprefix tailTrace_4514656
  have hstable : (prefixWord ++ tailWord_4514656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514656).length < 2 ^ (prefixWord ++ tailWord_4514656).sum := by decide
  have hdescent : baseEnd_4514656 < baseStart_4514656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514670 : List Nat := [4, 1, 2, 3, 3, 1, 1, 1, 2, 5]
def baseStart_4514670 : Nat := 118140960795 + 4514670 * 2 ^ 59
def prefixEnd_4514670 : Nat := 4983230072969 + 3 ^ 40 * 4514670 * 2
def baseEnd_4514670 : Nat := 772731902144652188854139

theorem tailTrace_4514670 : CollatzResearch.WordTrace tailWord_4514670 prefixEnd_4514670 772731902144652188854139 := by
  unfold tailWord_4514670
  simp only [CollatzResearch.WordTrace]
  refine ⟨20582942819266138636892683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109775695036086072730094309 20582942819266138636892683)
  ·
    refine ⟨30874414228899207955339025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20582942819266138636892683 30874414228899207955339025)
    ·
      refine ⟨23155810671674405966504269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30874414228899207955339025 23155810671674405966504269)
      ·
        refine ⟨8683429001877902237439101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23155810671674405966504269 8683429001877902237439101)
        ·
          refine ⟨3256285875704213339039663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8683429001877902237439101 3256285875704213339039663)
          ·
            refine ⟨4884428813556320008559495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3256285875704213339039663 4884428813556320008559495)
            ·
              refine ⟨7326643220334480012839243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4884428813556320008559495 7326643220334480012839243)
              ·
                refine ⟨10989964830501720019258865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7326643220334480012839243 10989964830501720019258865)
                ·
                  refine ⟨8242473622876290014444149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10989964830501720019258865 8242473622876290014444149)
                  ·
                    refine ⟨772731902144652188854139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8242473622876290014444149 772731902144652188854139)
                    ·
                      rfl

theorem cell23_4514670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_4514670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514670 prefixEnd_4514670 := by exact prefixLift 4514670
  have htrace : WordTrace (prefixWord ++ tailWord_4514670) baseStart_4514670 baseEnd_4514670 := by
    simpa [prefixWord, tailWord_4514670, baseEnd_4514670] using wordTrace_append hprefix tailTrace_4514670
  have hstable : (prefixWord ++ tailWord_4514670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514670).length < 2 ^ (prefixWord ++ tailWord_4514670).sum := by decide
  have hdescent : baseEnd_4514670 < baseStart_4514670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514696 : List Nat := [2, 1, 3, 3, 2, 1, 3, 2, 6]
def baseStart_4514696 : Nat := 118140960795 + 4514696 * 2 ^ 59
def prefixEnd_4514696 : Nat := 4983230072969 + 3 ^ 40 * 4514696 * 2
def baseEnd_4514696 : Nat := 257578784103441496093033

theorem tailTrace_4514696 : CollatzResearch.WordTrace tailWord_4514696 prefixEnd_4514696 257578784103441496093033 := by
  unfold tailWord_4514696
  simp only [CollatzResearch.WordTrace]
  refine ⟨82332245426017457767793971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109776327234689943690391961 82332245426017457767793971)
  ·
    refine ⟨123498368139026186651690957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82332245426017457767793971 123498368139026186651690957)
    ·
      refine ⟨46311888052134819994384109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123498368139026186651690957 46311888052134819994384109)
      ·
        refine ⟨17366958019550557497894041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46311888052134819994384109 17366958019550557497894041)
        ·
          refine ⟨13025218514662918123420531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17366958019550557497894041 13025218514662918123420531)
          ·
            refine ⟨19537827771994377185130797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13025218514662918123420531 19537827771994377185130797)
            ·
              refine ⟨7326685414497891444424049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19537827771994377185130797 7326685414497891444424049)
              ·
                refine ⟨5495014060873418583318037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7326685414497891444424049 5495014060873418583318037)
                ·
                  refine ⟨257578784103441496093033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5495014060873418583318037 257578784103441496093033)
                  ·
                    rfl

theorem cell23_4514696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 6].length) (baseStart_4514696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514696 prefixEnd_4514696 := by exact prefixLift 4514696
  have htrace : WordTrace (prefixWord ++ tailWord_4514696) baseStart_4514696 baseEnd_4514696 := by
    simpa [prefixWord, tailWord_4514696, baseEnd_4514696] using wordTrace_append hprefix tailTrace_4514696
  have hstable : (prefixWord ++ tailWord_4514696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514696).length < 2 ^ (prefixWord ++ tailWord_4514696).sum := by decide
  have hdescent : baseEnd_4514696 < baseStart_4514696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514710 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_4514710 : Nat := 118140960795 + 4514710 * 2 ^ 59
def prefixEnd_4514710 : Nat := 4983230072969 + 3 ^ 40 * 4514710 * 2
def baseEnd_4514710 : Nat := 2318216245660136410062233

theorem tailTrace_4514710 : CollatzResearch.WordTrace tailWord_4514710 prefixEnd_4514710 2318216245660136410062233 := by
  unfold tailWord_4514710
  simp only [CollatzResearch.WordTrace]
  refine ⟨10291562592124012245412349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109776667649322797284398389 10291562592124012245412349)
  ·
    refine ⟨3859335972046504592029631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10291562592124012245412349 3859335972046504592029631)
    ·
      refine ⟨5789003958069756888044447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3859335972046504592029631 5789003958069756888044447)
      ·
        refine ⟨8683505937104635332066671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5789003958069756888044447 8683505937104635332066671)
        ·
          refine ⟨13025258905656952998100007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8683505937104635332066671 13025258905656952998100007)
          ·
            refine ⟨19537888358485429497150011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13025258905656952998100007 19537888358485429497150011)
            ·
              refine ⟨29306832537728144245725017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19537888358485429497150011 29306832537728144245725017)
              ·
                refine ⟨21980124403296108184293763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29306832537728144245725017 21980124403296108184293763)
                ·
                  refine ⟨32970186604944162276440645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21980124403296108184293763 32970186604944162276440645)
                  ·
                    refine ⟨6181909988427030426832621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32970186604944162276440645 6181909988427030426832621)
                    ·
                      refine ⟨2318216245660136410062233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6181909988427030426832621 2318216245660136410062233)
                      ·
                        rfl

theorem cell23_4514710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_4514710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514710 prefixEnd_4514710 := by exact prefixLift 4514710
  have htrace : WordTrace (prefixWord ++ tailWord_4514710) baseStart_4514710 baseEnd_4514710 := by
    simpa [prefixWord, tailWord_4514710, baseEnd_4514710] using wordTrace_append hprefix tailTrace_4514710
  have hstable : (prefixWord ++ tailWord_4514710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514710).length < 2 ^ (prefixWord ++ tailWord_4514710).sum := by decide
  have hdescent : baseEnd_4514710 < baseStart_4514710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514746 : List Nat := [3, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4]
def baseStart_4514746 : Nat := 118140960795 + 4514746 * 2 ^ 59
def prefixEnd_4514746 : Nat := 4983230072969 + 3 ^ 40 * 4514746 * 2
def baseEnd_4514746 : Nat := 2318234730963698269212067

theorem tailTrace_4514746 : CollatzResearch.WordTrace tailWord_4514746 prefixEnd_4514746 2318234730963698269212067 := by
  unfold tailWord_4514746
  simp only [CollatzResearch.WordTrace]
  refine ⟨41166578625463443518727023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109777543001235849383272061 41166578625463443518727023)
  ·
    refine ⟨61749867938195165278090535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41166578625463443518727023 61749867938195165278090535)
    ·
      refine ⟨92624801907292747917135803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61749867938195165278090535 92624801907292747917135803)
      ·
        refine ⟨138937202860939121875703705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92624801907292747917135803 138937202860939121875703705)
        ·
          refine ⟨104202902145704341406777779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138937202860939121875703705 104202902145704341406777779)
          ·
            refine ⟨156304353218556512110166669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104202902145704341406777779 156304353218556512110166669)
            ·
              refine ⟨58614132456958692041312501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156304353218556512110166669 58614132456958692041312501)
              ·
                refine ⟨5495074917839877378873047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58614132456958692041312501 5495074917839877378873047)
                ·
                  refine ⟨8242612376759816068309571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5495074917839877378873047 8242612376759816068309571)
                  ·
                    refine ⟨12363918565139724102464357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8242612376759816068309571 12363918565139724102464357)
                    ·
                      refine ⟨2318234730963698269212067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12363918565139724102464357 2318234730963698269212067)
                      ·
                        rfl

theorem cell23_4514746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4].length) (baseStart_4514746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514746 prefixEnd_4514746 := by exact prefixLift 4514746
  have htrace : WordTrace (prefixWord ++ tailWord_4514746) baseStart_4514746 baseEnd_4514746 := by
    simpa [prefixWord, tailWord_4514746, baseEnd_4514746] using wordTrace_append hprefix tailTrace_4514746
  have hstable : (prefixWord ++ tailWord_4514746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514746).length < 2 ^ (prefixWord ++ tailWord_4514746).sum := by decide
  have hdescent : baseEnd_4514746 < baseStart_4514746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514759 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 6]
def baseStart_4514759 : Nat := 118140960795 + 4514759 * 2 ^ 59
def prefixEnd_4514759 : Nat := 4983230072969 + 3 ^ 40 * 4514759 * 2
def baseEnd_4514759 : Nat := 2318241406212206718349507

theorem tailTrace_4514759 : CollatzResearch.WordTrace tailWord_4514759 prefixEnd_4514759 2318241406212206718349507 := by
  unfold tailWord_4514759
  simp only [CollatzResearch.WordTrace]
  refine ⟨164666788650806677295131331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109777859100537784863420887 164666788650806677295131331)
  ·
    refine ⟨247000182976210015942696997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164666788650806677295131331 247000182976210015942696997)
    ·
      refine ⟨46312534308039377989255687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 247000182976210015942696997 46312534308039377989255687)
      ·
        refine ⟨69468801462059066983883531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46312534308039377989255687 69468801462059066983883531)
        ·
          refine ⟨104203202193088600475825297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69468801462059066983883531 104203202193088600475825297)
          ·
            refine ⟨78152401644816450356868973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104203202193088600475825297 78152401644816450356868973)
            ·
              refine ⟨29307150616806168883825865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78152401644816450356868973 29307150616806168883825865)
              ·
                refine ⟨21980362962604626662869399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29307150616806168883825865 21980362962604626662869399)
                ·
                  refine ⟨32970544443906939994304099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21980362962604626662869399 32970544443906939994304099)
                  ·
                    refine ⟨49455816665860409991456149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32970544443906939994304099 49455816665860409991456149)
                    ·
                      refine ⟨2318241406212206718349507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49455816665860409991456149 2318241406212206718349507)
                      ·
                        rfl

theorem cell23_4514759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_4514759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514759 prefixEnd_4514759 := by exact prefixLift 4514759
  have htrace : WordTrace (prefixWord ++ tailWord_4514759) baseStart_4514759 baseEnd_4514759 := by
    simpa [prefixWord, tailWord_4514759, baseEnd_4514759] using wordTrace_append hprefix tailTrace_4514759
  have hstable : (prefixWord ++ tailWord_4514759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514759).length < 2 ^ (prefixWord ++ tailWord_4514759).sum := by decide
  have hdescent : baseEnd_4514759 < baseStart_4514759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514766 : List Nat := [4, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5]
def baseStart_4514766 : Nat := 118140960795 + 4514766 * 2 ^ 59
def prefixEnd_4514766 : Nat := 4983230072969 + 3 ^ 40 * 4514766 * 2
def baseEnd_4514766 : Nat := 2318245000576788190961975

theorem tailTrace_4514766 : CollatzResearch.WordTrace tailWord_4514766 prefixEnd_4514766 2318245000576788190961975 := by
  unfold tailWord_4514766
  simp only [CollatzResearch.WordTrace]
  refine ⟨20583380495222664686329519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109778029307854211660424101 20583380495222664686329519)
  ·
    refine ⟨30875070742833997029494279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20583380495222664686329519 30875070742833997029494279)
    ·
      refine ⟨46312606114250995544241419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30875070742833997029494279 46312606114250995544241419)
      ·
        refine ⟨69468909171376493316362129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46312606114250995544241419 69468909171376493316362129)
        ·
          refine ⟨52101681878532369987271597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69468909171376493316362129 52101681878532369987271597)
          ·
            refine ⟨19538130704449638745226849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52101681878532369987271597 19538130704449638745226849)
            ·
              refine ⟨14653598028337229058920137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19538130704449638745226849 14653598028337229058920137)
              ·
                refine ⟨10990198521252921794190103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14653598028337229058920137 10990198521252921794190103)
                ·
                  refine ⟨16485297781879382691285155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10990198521252921794190103 16485297781879382691285155)
                  ·
                    refine ⟨24727946672819074036927733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16485297781879382691285155 24727946672819074036927733)
                    ·
                      refine ⟨2318245000576788190961975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24727946672819074036927733 2318245000576788190961975)
                      ·
                        rfl

theorem cell23_4514766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_4514766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514766 prefixEnd_4514766 := by exact prefixLift 4514766
  have htrace : WordTrace (prefixWord ++ tailWord_4514766) baseStart_4514766 baseEnd_4514766 := by
    simpa [prefixWord, tailWord_4514766, baseEnd_4514766] using wordTrace_append hprefix tailTrace_4514766
  have hstable : (prefixWord ++ tailWord_4514766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514766).length < 2 ^ (prefixWord ++ tailWord_4514766).sum := by decide
  have hdescent : baseEnd_4514766 < baseStart_4514766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514769 : List Nat := [1, 2, 2, 1, 2, 1, 6, 8]
def baseStart_4514769 : Nat := 118140960795 + 4514769 * 2 ^ 59
def prefixEnd_4514769 : Nat := 4983230072969 + 3 ^ 40 * 4514769 * 2
def baseEnd_4514769 : Nat := 85860983000694506637943

theorem tailTrace_4514769 : CollatzResearch.WordTrace tailWord_4514769 prefixEnd_4514769 85860983000694506637943 := by
  unfold tailWord_4514769
  simp only [CollatzResearch.WordTrace]
  refine ⟨164667153380770449002995361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109778102253846966001996907 164667153380770449002995361)
  ·
    refine ⟨123500365035577836752246521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164667153380770449002995361 123500365035577836752246521)
    ·
      refine ⟨92625273776683377564184891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123500365035577836752246521 92625273776683377564184891)
      ·
        refine ⟨138937910665025066346277337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92625273776683377564184891 138937910665025066346277337)
        ·
          refine ⟨104203432998768799759708003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138937910665025066346277337 104203432998768799759708003)
          ·
            refine ⟨156305149498153199639562005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104203432998768799759708003 156305149498153199639562005)
            ·
              refine ⟨7326803882725931233104469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 156305149498153199639562005 7326803882725931233104469)
              ·
                refine ⟨85860983000694506637943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7326803882725931233104469 85860983000694506637943)
                ·
                  rfl

theorem cell23_4514769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 8].length) (baseStart_4514769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514769 prefixEnd_4514769 := by exact prefixLift 4514769
  have htrace : WordTrace (prefixWord ++ tailWord_4514769) baseStart_4514769 baseEnd_4514769 := by
    simpa [prefixWord, tailWord_4514769, baseEnd_4514769] using wordTrace_append hprefix tailTrace_4514769
  have hstable : (prefixWord ++ tailWord_4514769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514769).length < 2 ^ (prefixWord ++ tailWord_4514769).sum := by decide
  have hdescent : baseEnd_4514769 < baseStart_4514769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514783 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 3]
def baseStart_4514783 : Nat := 118140960795 + 4514783 * 2 ^ 59
def prefixEnd_4514783 : Nat := 4983230072969 + 3 ^ 40 * 4514783 * 2
def baseEnd_4514783 : Nat := 2318253729747914624449397

theorem tailTrace_4514783 : CollatzResearch.WordTrace tailWord_4514783 prefixEnd_4514783 2318253729747914624449397 := by
  unfold tailWord_4514783
  simp only [CollatzResearch.WordTrace]
  refine ⟨164667664002719729394005003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109778442668479819596003335 164667664002719729394005003)
  ·
    refine ⟨247001496004079594091007505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164667664002719729394005003 247001496004079594091007505)
    ·
      refine ⟨185251122003059695568255629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247001496004079594091007505 185251122003059695568255629)
      ·
        refine ⟨69469170751147385838095861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185251122003059695568255629 69469170751147385838095861)
        ·
          refine ⟨6512734757920067422321487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69469170751147385838095861 6512734757920067422321487)
          ·
            refine ⟨9769102136880101133482231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6512734757920067422321487 9769102136880101133482231)
            ·
              refine ⟨14653653205320151700223347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9769102136880101133482231 14653653205320151700223347)
              ·
                refine ⟨21980479807980227550335021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14653653205320151700223347 21980479807980227550335021)
                ·
                  refine ⟨8242679927992585331375633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21980479807980227550335021 8242679927992585331375633)
                  ·
                    refine ⟨6182009945994438998531725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8242679927992585331375633 6182009945994438998531725)
                    ·
                      refine ⟨2318253729747914624449397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6182009945994438998531725 2318253729747914624449397)
                      ·
                        rfl

theorem cell23_4514783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_4514783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514783 prefixEnd_4514783 := by exact prefixLift 4514783
  have htrace : WordTrace (prefixWord ++ tailWord_4514783) baseStart_4514783 baseEnd_4514783 := by
    simpa [prefixWord, tailWord_4514783, baseEnd_4514783] using wordTrace_append hprefix tailTrace_4514783
  have hstable : (prefixWord ++ tailWord_4514783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514783).length < 2 ^ (prefixWord ++ tailWord_4514783).sum := by decide
  have hdescent : baseEnd_4514783 < baseStart_4514783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514823 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 5, 3, 2]
def baseStart_4514823 : Nat := 118140960795 + 4514823 * 2 ^ 59
def prefixEnd_4514823 : Nat := 4983230072969 + 3 ^ 40 * 4514823 * 2
def baseEnd_4514823 : Nat := 2318274268974094467949213

theorem tailTrace_4514823 : CollatzResearch.WordTrace tailWord_4514823 prefixEnd_4514823 2318274268974094467949213 := by
  unfold tailWord_4514823
  simp only [CollatzResearch.WordTrace]
  refine ⟨164669122922574816225461123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109779415281716544150307415 164669122922574816225461123)
  ·
    refine ⟨247003684383862224338191685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164669122922574816225461123 247003684383862224338191685)
    ·
      refine ⟨46313190821974167063410941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 247003684383862224338191685 46313190821974167063410941)
      ·
        refine ⟨17367446558240312648779103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46313190821974167063410941 17367446558240312648779103)
        ·
          refine ⟨26051169837360468973168655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17367446558240312648779103 26051169837360468973168655)
          ·
            refine ⟨39076754756040703459752983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26051169837360468973168655 39076754756040703459752983)
            ·
              refine ⟨58615132134061055189629475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39076754756040703459752983 58615132134061055189629475)
              ·
                refine ⟨87922698201091582784444213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58615132134061055189629475 87922698201091582784444213)
                ·
                  refine ⟨8242752956352335886041645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87922698201091582784444213 8242752956352335886041645)
                  ·
                    refine ⟨3091032358632125957265617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8242752956352335886041645 3091032358632125957265617)
                    ·
                      refine ⟨2318274268974094467949213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3091032358632125957265617 2318274268974094467949213)
                      ·
                        rfl

theorem cell23_4514823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_4514823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514823 prefixEnd_4514823 := by exact prefixLift 4514823
  have htrace : WordTrace (prefixWord ++ tailWord_4514823) baseStart_4514823 baseEnd_4514823 := by
    simpa [prefixWord, tailWord_4514823, baseEnd_4514823] using wordTrace_append hprefix tailTrace_4514823
  have hstable : (prefixWord ++ tailWord_4514823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514823).length < 2 ^ (prefixWord ++ tailWord_4514823).sum := by decide
  have hdescent : baseEnd_4514823 < baseStart_4514823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514830 : List Nat := [4, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3]
def baseStart_4514830 : Nat := 118140960795 + 4514830 * 2 ^ 59
def prefixEnd_4514830 : Nat := 4983230072969 + 3 ^ 40 * 4514830 * 2
def baseEnd_4514830 : Nat := 2318277863338675940561681

theorem tailTrace_4514830 : CollatzResearch.WordTrace tailWord_4514830 prefixEnd_4514830 2318277863338675940561681 := by
  unfold tailWord_4514830
  simp only [CollatzResearch.WordTrace]
  refine ⟨20583672279193682052620743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109779585489032970947310629 20583672279193682052620743)
  ·
    refine ⟨30875508418790523078931115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20583672279193682052620743 30875508418790523078931115)
    ·
      refine ⟨46313262628185784618396673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30875508418790523078931115 46313262628185784618396673)
      ·
        refine ⟨34734946971139338463797505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46313262628185784618396673 34734946971139338463797505)
        ·
          refine ⟨26051210228354503847848129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34734946971139338463797505 26051210228354503847848129)
          ·
            refine ⟨19538407671265877885886097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26051210228354503847848129 19538407671265877885886097)
            ·
              refine ⟨14653805753449408414414573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19538407671265877885886097 14653805753449408414414573)
              ·
                refine ⟨5495177157543528155405465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14653805753449408414414573 5495177157543528155405465)
                ·
                  refine ⟨4121382868157646116554099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5495177157543528155405465 4121382868157646116554099)
                  ·
                    refine ⟨6182074302236469174831149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4121382868157646116554099 6182074302236469174831149)
                    ·
                      refine ⟨2318277863338675940561681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6182074302236469174831149 2318277863338675940561681)
                      ·
                        rfl

theorem cell23_4514830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_4514830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514830 prefixEnd_4514830 := by exact prefixLift 4514830
  have htrace : WordTrace (prefixWord ++ tailWord_4514830) baseStart_4514830 baseEnd_4514830 := by
    simpa [prefixWord, tailWord_4514830, baseEnd_4514830] using wordTrace_append hprefix tailTrace_4514830
  have hstable : (prefixWord ++ tailWord_4514830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514830).length < 2 ^ (prefixWord ++ tailWord_4514830).sum := by decide
  have hdescent : baseEnd_4514830 < baseStart_4514830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514853 : List Nat := [1, 3, 1, 2, 2, 2, 1, 4, 1, 4, 2]
def baseStart_4514853 : Nat := 118140960795 + 4514853 * 2 ^ 59
def prefixEnd_4514853 : Nat := 4983230072969 + 3 ^ 40 * 4514853 * 2
def baseEnd_4514853 : Nat := 2318289673393729350574075

theorem tailTrace_4514853 : CollatzResearch.WordTrace tailWord_4514853 prefixEnd_4514853 2318289673393729350574075 := by
  unfold tailWord_4514853
  simp only [CollatzResearch.WordTrace]
  refine ⟨164670217112466131349053213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109780144741644087566035475 164670217112466131349053213)
  ·
    refine ⟨61751331417174799255894955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164670217112466131349053213 61751331417174799255894955)
    ·
      refine ⟨92626997125762198883842433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61751331417174799255894955 92626997125762198883842433)
      ·
        refine ⟨69470247844321649162881825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92626997125762198883842433 69470247844321649162881825)
        ·
          refine ⟨52102685883241236872161369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69470247844321649162881825 52102685883241236872161369)
          ·
            refine ⟨39077014412430927654121027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52102685883241236872161369 39077014412430927654121027)
            ·
              refine ⟨58615521618646391481181541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39077014412430927654121027 58615521618646391481181541)
              ·
                refine ⟨10990410303496198402721539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58615521618646391481181541 10990410303496198402721539)
                ·
                  refine ⟨16485615455244297604082309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10990410303496198402721539 16485615455244297604082309)
                  ·
                    refine ⟨3091052897858305800765433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16485615455244297604082309 3091052897858305800765433)
                    ·
                      refine ⟨2318289673393729350574075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3091052897858305800765433 2318289673393729350574075)
                      ·
                        rfl

theorem cell23_4514853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 4, 2].length) (baseStart_4514853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514853 prefixEnd_4514853 := by exact prefixLift 4514853
  have htrace : WordTrace (prefixWord ++ tailWord_4514853) baseStart_4514853 baseEnd_4514853 := by
    simpa [prefixWord, tailWord_4514853, baseEnd_4514853] using wordTrace_append hprefix tailTrace_4514853
  have hstable : (prefixWord ++ tailWord_4514853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514853).length < 2 ^ (prefixWord ++ tailWord_4514853).sum := by decide
  have hdescent : baseEnd_4514853 < baseStart_4514853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514859 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 9]
def baseStart_4514859 : Nat := 118140960795 + 4514859 * 2 ^ 59
def prefixEnd_4514859 : Nat := 4983230072969 + 3 ^ 40 * 4514859 * 2
def baseEnd_4514859 : Nat := 257588083808628480788783

theorem tailTrace_4514859 : CollatzResearch.WordTrace tailWord_4514859 prefixEnd_4514859 257588083808628480788783 := by
  unfold tailWord_4514859
  simp only [CollatzResearch.WordTrace]
  refine ⟨164670435950444394373771631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109780290633629596249181087 164670435950444394373771631)
  ·
    refine ⟨247005653925666591560657447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164670435950444394373771631 247005653925666591560657447)
    ·
      refine ⟨370508480888499887340986171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247005653925666591560657447 370508480888499887340986171)
      ·
        refine ⟨555762721332749831011479257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370508480888499887340986171 555762721332749831011479257)
        ·
          refine ⟨416822040999562373258609443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 555762721332749831011479257 416822040999562373258609443)
          ·
            refine ⟨625233061499343559887914165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416822040999562373258609443 625233061499343559887914165)
            ·
              refine ⟨58615599515563458739491953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 625233061499343559887914165 58615599515563458739491953)
              ·
                refine ⟨43961699636672594054618965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58615599515563458739491953 43961699636672594054618965)
                ·
                  refine ⟨257588083808628480788783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43961699636672594054618965 257588083808628480788783)
                  ·
                    rfl

theorem cell23_4514859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 9].length) (baseStart_4514859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514859 prefixEnd_4514859 := by exact prefixLift 4514859
  have htrace : WordTrace (prefixWord ++ tailWord_4514859) baseStart_4514859 baseEnd_4514859 := by
    simpa [prefixWord, tailWord_4514859, baseEnd_4514859] using wordTrace_append hprefix tailTrace_4514859
  have hstable : (prefixWord ++ tailWord_4514859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514859).length < 2 ^ (prefixWord ++ tailWord_4514859).sum := by decide
  have hdescent : baseEnd_4514859 < baseStart_4514859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514866 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4]
def baseStart_4514866 : Nat := 118140960795 + 4514866 * 2 ^ 59
def prefixEnd_4514866 : Nat := 4983230072969 + 3 ^ 40 * 4514866 * 2
def baseEnd_4514866 : Nat := 2318296348642237799711515

theorem tailTrace_4514866 : CollatzResearch.WordTrace tailWord_4514866 prefixEnd_4514866 2318296348642237799711515 := by
  unfold tailWord_4514866
  simp only [CollatzResearch.WordTrace]
  refine ⟨41167672815354758642319113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109780460840946023046184301 41167672815354758642319113)
  ·
    refine ⟨30875754611516068981739335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41167672815354758642319113 30875754611516068981739335)
    ·
      refine ⟨46313631917274103472609003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30875754611516068981739335 46313631917274103472609003)
      ·
        refine ⟨69470447875911155208913505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46313631917274103472609003 69470447875911155208913505)
        ·
          refine ⟨52102835906933366406685129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69470447875911155208913505 52102835906933366406685129)
          ·
            refine ⟨39077126930200024805013847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52102835906933366406685129 39077126930200024805013847)
            ·
              refine ⟨58615690395300037207520771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39077126930200024805013847 58615690395300037207520771)
              ·
                refine ⟨87923535592950055811281157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58615690395300037207520771 87923535592950055811281157)
                ·
                  refine ⟨16485662923678135464615217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87923535592950055811281157 16485662923678135464615217)
                  ·
                    refine ⟨12364247192758601598461413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16485662923678135464615217 12364247192758601598461413)
                    ·
                      refine ⟨2318296348642237799711515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12364247192758601598461413 2318296348642237799711515)
                      ·
                        rfl

theorem cell23_4514866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_4514866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514866 prefixEnd_4514866 := by exact prefixLift 4514866
  have htrace : WordTrace (prefixWord ++ tailWord_4514866) baseStart_4514866 baseEnd_4514866 := by
    simpa [prefixWord, tailWord_4514866, baseEnd_4514866] using wordTrace_append hprefix tailTrace_4514866
  have hstable : (prefixWord ++ tailWord_4514866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514866).length < 2 ^ (prefixWord ++ tailWord_4514866).sum := by decide
  have hdescent : baseEnd_4514866 < baseStart_4514866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514876 : List Nat := [2, 2, 2, 2, 2, 2, 1, 3, 7]
def baseStart_4514876 : Nat := 118140960795 + 4514876 * 2 ^ 59
def prefixEnd_4514876 : Nat := 4983230072969 + 3 ^ 40 * 4514876 * 2
def baseEnd_4514876 : Nat := 257589053716531417842941

theorem tailTrace_4514876 : CollatzResearch.WordTrace tailWord_4514876 prefixEnd_4514876 257589053716531417842941 := by
  unfold tailWord_4514876
  simp only [CollatzResearch.WordTrace]
  refine ⟨82335527995691403138570241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109780703994255204184760321 82335527995691403138570241)
  ·
    refine ⟨61751645996768552353927681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82335527995691403138570241 61751645996768552353927681)
    ·
      refine ⟨46313734497576414265445761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61751645996768552353927681 46313734497576414265445761)
      ·
        refine ⟨34735300873182310699084321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46313734497576414265445761 34735300873182310699084321)
        ·
          refine ⟨26051475654886733024313241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34735300873182310699084321 26051475654886733024313241)
          ·
            refine ⟨19538606741165049768234931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26051475654886733024313241 19538606741165049768234931)
            ·
              refine ⟨29307910111747574652352397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19538606741165049768234931 29307910111747574652352397)
              ·
                refine ⟨10990466291905340494632149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29307910111747574652352397 10990466291905340494632149)
                ·
                  refine ⟨257589053716531417842941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10990466291905340494632149 257589053716531417842941)
                  ·
                    rfl

theorem cell23_4514876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 7].length) (baseStart_4514876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514876 prefixEnd_4514876 := by exact prefixLift 4514876
  have htrace : WordTrace (prefixWord ++ tailWord_4514876) baseStart_4514876 baseEnd_4514876 := by
    simpa [prefixWord, tailWord_4514876, baseEnd_4514876] using wordTrace_append hprefix tailTrace_4514876
  have hstable : (prefixWord ++ tailWord_4514876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514876).length < 2 ^ (prefixWord ++ tailWord_4514876).sum := by decide
  have hdescent : baseEnd_4514876 < baseStart_4514876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514893 : List Nat := [1, 6, 1, 1, 1, 2, 2, 2, 7]
def baseStart_4514893 : Nat := 118140960795 + 4514893 * 2 ^ 59
def prefixEnd_4514893 : Nat := 4983230072969 + 3 ^ 40 * 4514893 * 2
def baseEnd_4514893 : Nat := 257590023624434354897099

theorem tailTrace_4514893 : CollatzResearch.WordTrace tailWord_4514893 prefixEnd_4514893 257590023624434354897099 := by
  unfold tailWord_4514893
  simp only [CollatzResearch.WordTrace]
  refine ⟨164671676032321218180509333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109781117354880812120339555 164671676032321218180509333)
  ·
    refine ⟨7718984814015057102211375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 164671676032321218180509333 7718984814015057102211375)
    ·
      refine ⟨11578477221022585653317063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7718984814015057102211375 11578477221022585653317063)
      ·
        refine ⟨17367715831533878479975595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11578477221022585653317063 17367715831533878479975595)
        ·
          refine ⟨26051573747300817719963393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17367715831533878479975595 26051573747300817719963393)
          ·
            refine ⟨19538680310475613289972545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26051573747300817719963393 19538680310475613289972545)
            ·
              refine ⟨14654010232856709967479409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19538680310475613289972545 14654010232856709967479409)
              ·
                refine ⟨10990507674642532475609557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14654010232856709967479409 10990507674642532475609557)
                ·
                  refine ⟨257590023624434354897099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10990507674642532475609557 257590023624434354897099)
                  ·
                    rfl

theorem cell23_4514893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_4514893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514893 prefixEnd_4514893 := by exact prefixLift 4514893
  have htrace : WordTrace (prefixWord ++ tailWord_4514893) baseStart_4514893 baseEnd_4514893 := by
    simpa [prefixWord, tailWord_4514893, baseEnd_4514893] using wordTrace_append hprefix tailTrace_4514893
  have hstable : (prefixWord ++ tailWord_4514893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514893).length < 2 ^ (prefixWord ++ tailWord_4514893).sum := by decide
  have hdescent : baseEnd_4514893 < baseStart_4514893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514916 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 1, 2, 5]
def baseStart_4514916 : Nat := 118140960795 + 4514916 * 2 ^ 59
def prefixEnd_4514916 : Nat := 4983230072969 + 3 ^ 40 * 4514916 * 2
def baseEnd_4514916 : Nat := 2318322022674962604086285

theorem tailTrace_4514916 : CollatzResearch.WordTrace tailWord_4514916 prefixEnd_4514916 2318322022674962604086285 := by
  unfold tailWord_4514916
  simp only [CollatzResearch.WordTrace]
  refine ⟨82336257455618946554298301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109781676607491928739064401 82336257455618946554298301)
  ·
    refine ⟨30876096545857104957861863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82336257455618946554298301 30876096545857104957861863)
    ·
      refine ⟨46314144818785657436792795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30876096545857104957861863 46314144818785657436792795)
      ·
        refine ⟨69471217228178486155189193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46314144818785657436792795 69471217228178486155189193)
        ·
          refine ⟨52103412921133864616391895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69471217228178486155189193 52103412921133864616391895)
          ·
            refine ⟨78155119381700796924587843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52103412921133864616391895 78155119381700796924587843)
            ·
              refine ⟨117232679072551195386881765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78155119381700796924587843 117232679072551195386881765)
              ·
                refine ⟨21981127326103349135040331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117232679072551195386881765 21981127326103349135040331)
                ·
                  refine ⟨32971690989155023702560497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21981127326103349135040331 32971690989155023702560497)
                  ·
                    refine ⟨24728768241866267776920373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32971690989155023702560497 24728768241866267776920373)
                    ·
                      refine ⟨2318322022674962604086285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24728768241866267776920373 2318322022674962604086285)
                      ·
                        rfl

theorem cell23_4514916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_4514916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514916 prefixEnd_4514916 := by exact prefixLift 4514916
  have htrace : WordTrace (prefixWord ++ tailWord_4514916) baseStart_4514916 baseEnd_4514916 := by
    simpa [prefixWord, tailWord_4514916, baseEnd_4514916] using wordTrace_append hprefix tailTrace_4514916
  have hstable : (prefixWord ++ tailWord_4514916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514916).length < 2 ^ (prefixWord ++ tailWord_4514916).sum := by decide
  have hdescent : baseEnd_4514916 < baseStart_4514916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514956 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 2, 4, 4]
def baseStart_4514956 : Nat := 118140960795 + 4514956 * 2 ^ 59
def prefixEnd_4514956 : Nat := 4983230072969 + 3 ^ 40 * 4514956 * 2
def baseEnd_4514956 : Nat := 2318342561901142447586101

theorem tailTrace_4514956 : CollatzResearch.WordTrace tailWord_4514956 prefixEnd_4514956 2318342561901142447586101 := by
  unfold tailWord_4514956
  simp only [CollatzResearch.WordTrace]
  refine ⟨82336986915546489970026361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109782649220728653293368481 82336986915546489970026361)
  ·
    refine ⟨61752740186659867477519771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82336986915546489970026361 61752740186659867477519771)
    ·
      refine ⟨92629110279989801216279657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61752740186659867477519771 92629110279989801216279657)
      ·
        refine ⟨69471832709992350912209743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92629110279989801216279657 69471832709992350912209743)
        ·
          refine ⟨104207749064988526368314615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69471832709992350912209743 104207749064988526368314615)
          ·
            refine ⟨156311623597482789552471923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104207749064988526368314615 156311623597482789552471923)
            ·
              refine ⟨234467435396224184328707885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156311623597482789552471923 234467435396224184328707885)
              ·
                refine ⟨87925288273584069123265457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234467435396224184328707885 87925288273584069123265457)
                ·
                  refine ⟨65943966205188051842449093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87925288273584069123265457 65943966205188051842449093)
                  ·
                    refine ⟨12364493663472759720459205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65943966205188051842449093 12364493663472759720459205)
                    ·
                      refine ⟨2318342561901142447586101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12364493663472759720459205 2318342561901142447586101)
                      ·
                        rfl

theorem cell23_4514956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_4514956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514956 prefixEnd_4514956 := by exact prefixLift 4514956
  have htrace : WordTrace (prefixWord ++ tailWord_4514956) baseStart_4514956 baseEnd_4514956 := by
    simpa [prefixWord, tailWord_4514956, baseEnd_4514956] using wordTrace_append hprefix tailTrace_4514956
  have hstable : (prefixWord ++ tailWord_4514956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514956).length < 2 ^ (prefixWord ++ tailWord_4514956).sum := by decide
  have hdescent : baseEnd_4514956 < baseStart_4514956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514963 : List Nat := [1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 3]
def baseStart_4514963 : Nat := 118140960795 + 4514963 * 2 ^ 59
def prefixEnd_4514963 : Nat := 4983230072969 + 3 ^ 40 * 4514963 * 2
def baseEnd_4514963 : Nat := 2318346156265723920198569

theorem tailTrace_4514963 : CollatzResearch.WordTrace tailWord_4514963 prefixEnd_4514963 2318346156265723920198569 := by
  unfold tailWord_4514963
  simp only [CollatzResearch.WordTrace]
  refine ⟨164674229142067620135557543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109782819428045080090371695 164674229142067620135557543)
  ·
    refine ⟨247011343713101430203336315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164674229142067620135557543 247011343713101430203336315)
    ·
      refine ⟨370517015569652145305004473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247011343713101430203336315 370517015569652145305004473)
      ·
        refine ⟨277887761677239108978753355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 370517015569652145305004473 277887761677239108978753355)
        ·
          refine ⟨416831642515858663468130033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277887761677239108978753355 416831642515858663468130033)
          ·
            refine ⟨312623731886893997601097525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 416831642515858663468130033 312623731886893997601097525)
            ·
              refine ⟨29308474864396312275102893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 312623731886893997601097525 29308474864396312275102893)
              ·
                refine ⟨10990678074148617103163585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29308474864396312275102893 10990678074148617103163585)
                ·
                  refine ⟨8243008555611462827372689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10990678074148617103163585 8243008555611462827372689)
                  ·
                    refine ⟨6182256416708597120529517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8243008555611462827372689 6182256416708597120529517)
                    ·
                      refine ⟨2318346156265723920198569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6182256416708597120529517 2318346156265723920198569)
                      ·
                        rfl

theorem cell23_4514963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 3].length) (baseStart_4514963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514963 prefixEnd_4514963 := by exact prefixLift 4514963
  have htrace : WordTrace (prefixWord ++ tailWord_4514963) baseStart_4514963 baseEnd_4514963 := by
    simpa [prefixWord, tailWord_4514963, baseEnd_4514963] using wordTrace_append hprefix tailTrace_4514963
  have hstable : (prefixWord ++ tailWord_4514963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514963).length < 2 ^ (prefixWord ++ tailWord_4514963).sum := by decide
  have hdescent : baseEnd_4514963 < baseStart_4514963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514980 : List Nat := [2, 3, 1, 2, 3, 1, 2, 2, 2, 2, 3]
def baseStart_4514980 : Nat := 118140960795 + 4514980 * 2 ^ 59
def prefixEnd_4514980 : Nat := 4983230072969 + 3 ^ 40 * 4514980 * 2
def baseEnd_4514980 : Nat := 2318354885436850353685991

theorem tailTrace_4514980 : CollatzResearch.WordTrace tailWord_4514980 prefixEnd_4514980 2318354885436850353685991 := by
  unfold tailWord_4514980
  simp only [CollatzResearch.WordTrace]
  refine ⟨82337424591503016019463197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109783232788670688025950929 82337424591503016019463197)
  ·
    refine ⟨30876534221813631007298699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82337424591503016019463197 30876534221813631007298699)
    ·
      refine ⟨46314801332720446510948049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30876534221813631007298699 46314801332720446510948049)
      ·
        refine ⟨34736100999540334883211037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46314801332720446510948049 34736100999540334883211037)
        ·
          refine ⟨13026037874827625581204139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34736100999540334883211037 13026037874827625581204139)
          ·
            refine ⟨19539056812241438371806209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13026037874827625581204139 19539056812241438371806209)
            ·
              refine ⟨14654292609181078778854657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19539056812241438371806209 14654292609181078778854657)
              ·
                refine ⟨10990719456885809084140993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14654292609181078778854657 10990719456885809084140993)
                ·
                  refine ⟨8243039592664356813105745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10990719456885809084140993 8243039592664356813105745)
                  ·
                    refine ⟨6182279694498267609829309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8243039592664356813105745 6182279694498267609829309)
                    ·
                      refine ⟨2318354885436850353685991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6182279694498267609829309 2318354885436850353685991)
                      ·
                        rfl

theorem cell23_4514980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_4514980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514980 prefixEnd_4514980 := by exact prefixLift 4514980
  have htrace : WordTrace (prefixWord ++ tailWord_4514980) baseStart_4514980 baseEnd_4514980 := by
    simpa [prefixWord, tailWord_4514980, baseEnd_4514980] using wordTrace_append hprefix tailTrace_4514980
  have hstable : (prefixWord ++ tailWord_4514980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514980).length < 2 ^ (prefixWord ++ tailWord_4514980).sum := by decide
  have hdescent : baseEnd_4514980 < baseStart_4514980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515013 : List Nat := [1, 3, 1, 1, 1, 1, 3, 6, 1, 5]
def baseStart_4515013 : Nat := 118140960795 + 4515013 * 2 ^ 59
def prefixEnd_4515013 : Nat := 4983230072969 + 3 ^ 40 * 4515013 * 2
def baseEnd_4515013 : Nat := 772790610099482908191113

theorem tailTrace_4515013 : CollatzResearch.WordTrace tailWord_4515013 prefixEnd_4515013 772790610099482908191113 := by
  unfold tailWord_4515013
  simp only [CollatzResearch.WordTrace]
  refine ⟨164676052791886478674877693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109784035194590985783251795 164676052791886478674877693)
  ·
    refine ⟨61753519796957429503079135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164676052791886478674877693 61753519796957429503079135)
    ·
      refine ⟨92630279695436144254618703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61753519796957429503079135 92630279695436144254618703)
      ·
        refine ⟨138945419543154216381928055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92630279695436144254618703 138945419543154216381928055)
        ·
          refine ⟨208418129314731324572892083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138945419543154216381928055 208418129314731324572892083)
          ·
            refine ⟨312627193972096986859338125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208418129314731324572892083 312627193972096986859338125)
            ·
              refine ⟨117235197739536370072251797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 312627193972096986859338125 117235197739536370072251797)
              ·
                refine ⟨5495399894040767347136803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 117235197739536370072251797 5495399894040767347136803)
                ·
                  refine ⟨8243099841061151020705205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5495399894040767347136803 8243099841061151020705205)
                  ·
                    refine ⟨772790610099482908191113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8243099841061151020705205 772790610099482908191113)
                    ·
                      rfl

theorem cell23_4515013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 5].length) (baseStart_4515013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515013 prefixEnd_4515013 := by exact prefixLift 4515013
  have htrace : WordTrace (prefixWord ++ tailWord_4515013) baseStart_4515013 baseEnd_4515013 := by
    simpa [prefixWord, tailWord_4515013, baseEnd_4515013] using wordTrace_append hprefix tailTrace_4515013
  have hstable : (prefixWord ++ tailWord_4515013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515013).length < 2 ^ (prefixWord ++ tailWord_4515013).sum := by decide
  have hdescent : baseEnd_4515013 < baseStart_4515013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515073 : List Nat := [1, 2, 4, 1, 1, 4, 1, 9]
def baseStart_4515073 : Nat := 118140960795 + 4515073 * 2 ^ 59
def prefixEnd_4515073 : Nat := 4983230072969 + 3 ^ 40 * 4515073 * 2
def baseEnd_4515073 : Nat := 85866764412508092215669

theorem tailTrace_4515073 : CollatzResearch.WordTrace tailWord_4515073 prefixEnd_4515073 85866764412508092215669 := by
  unfold tailWord_4515073
  simp only [CollatzResearch.WordTrace]
  refine ⟨164678241171669108922061873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109785494114446072614707915 164678241171669108922061873)
  ·
    refine ⟨123508680878751831691546405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164678241171669108922061873 123508680878751831691546405)
    ·
      refine ⟨23157877664765968442164951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123508680878751831691546405 23157877664765968442164951)
      ·
        refine ⟨34736816497148952663247427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23157877664765968442164951 34736816497148952663247427)
        ·
          refine ⟨52105224745723428994871141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34736816497148952663247427 52105224745723428994871141)
          ·
            refine ⟨9769729639823142936538339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52105224745723428994871141 9769729639823142936538339)
            ·
              refine ⟨14654594459734714404807509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9769729639823142936538339 14654594459734714404807509)
              ·
                refine ⟨85866764412508092215669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14654594459734714404807509 85866764412508092215669)
                ·
                  rfl

theorem cell23_4515073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 9].length) (baseStart_4515073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515073 prefixEnd_4515073 := by exact prefixLift 4515073
  have htrace : WordTrace (prefixWord ++ tailWord_4515073) baseStart_4515073 baseEnd_4515073 := by
    simpa [prefixWord, tailWord_4515073, baseEnd_4515073] using wordTrace_append hprefix tailTrace_4515073
  have hstable : (prefixWord ++ tailWord_4515073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515073).length < 2 ^ (prefixWord ++ tailWord_4515073).sum := by decide
  have hdescent : baseEnd_4515073 < baseStart_4515073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515101 : List Nat := [1, 4, 2, 3, 1, 3, 1, 1, 3, 2, 2]
def baseStart_4515101 : Nat := 118140960795 + 4515101 * 2 ^ 59
def prefixEnd_4515101 : Nat := 4983230072969 + 3 ^ 40 * 4515101 * 2
def baseEnd_4515101 : Nat := 2318417016596044380272935

theorem tailTrace_4515101 : CollatzResearch.WordTrace tailWord_4515101 prefixEnd_4515101 2318417016596044380272935 := by
  unfold tailWord_4515101
  simp only [CollatzResearch.WordTrace]
  refine ⟨164679262415567669704081157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109786174943711779802720771 164679262415567669704081157)
  ·
    refine ⟨30877361702918938069515217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164679262415567669704081157 30877361702918938069515217)
    ·
      refine ⟨23158021277189203552136413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30877361702918938069515217 23158021277189203552136413)
      ·
        refine ⟨8684257978945951332051155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23158021277189203552136413 8684257978945951332051155)
        ·
          refine ⟨13026386968418926998076733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8684257978945951332051155 13026386968418926998076733)
          ·
            refine ⟨4884895113157097624278775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13026386968418926998076733 4884895113157097624278775)
            ·
              refine ⟨7327342669735646436418163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4884895113157097624278775 7327342669735646436418163)
              ·
                refine ⟨10991014004603469654627245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7327342669735646436418163 10991014004603469654627245)
                ·
                  refine ⟨4121630251726301120485217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10991014004603469654627245 4121630251726301120485217)
                  ·
                    refine ⟨3091222688794725840363913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4121630251726301120485217 3091222688794725840363913)
                    ·
                      refine ⟨2318417016596044380272935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3091222688794725840363913 2318417016596044380272935)
                      ·
                        rfl

theorem cell23_4515101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_4515101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515101 prefixEnd_4515101 := by exact prefixLift 4515101
  have htrace : WordTrace (prefixWord ++ tailWord_4515101) baseStart_4515101 baseEnd_4515101 := by
    simpa [prefixWord, tailWord_4515101, baseEnd_4515101] using wordTrace_append hprefix tailTrace_4515101
  have hstable : (prefixWord ++ tailWord_4515101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515101).length < 2 ^ (prefixWord ++ tailWord_4515101).sum := by decide
  have hdescent : baseEnd_4515101 < baseStart_4515101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515158 : List Nat := [5, 2, 3, 1, 2, 1, 1, 8]
def baseStart_4515158 : Nat := 118140960795 + 4515158 * 2 ^ 59
def prefixEnd_4515158 : Nat := 4983230072969 + 3 ^ 40 * 4515158 * 2
def baseEnd_4515158 : Nat := 85868380925679653972599

theorem tailTrace_4515158 : CollatzResearch.WordTrace tailWord_4515158 prefixEnd_4515158 85868380925679653972599 := by
  unfold tailWord_4515158
  simp only [CollatzResearch.WordTrace]
  refine ⟨10292583836022573027431633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109787560917574112292604085 10292583836022573027431633)
  ·
    refine ⟨7719437877016929770573725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10292583836022573027431633 7719437877016929770573725)
    ·
      refine ⟨2894789203881348663965147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7719437877016929770573725 2894789203881348663965147)
      ·
        refine ⟨4342183805822022995947721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2894789203881348663965147 4342183805822022995947721)
        ·
          refine ⟨3256637854366517246960791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4342183805822022995947721 3256637854366517246960791)
          ·
            refine ⟨4884956781549775870441187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3256637854366517246960791 4884956781549775870441187)
            ·
              refine ⟨7327435172324663805661781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4884956781549775870441187 7327435172324663805661781)
              ·
                refine ⟨85868380925679653972599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7327435172324663805661781 85868380925679653972599)
                ·
                  rfl

theorem cell23_4515158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_4515158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515158 prefixEnd_4515158 := by exact prefixLift 4515158
  have htrace : WordTrace (prefixWord ++ tailWord_4515158) baseStart_4515158 baseEnd_4515158 := by
    simpa [prefixWord, tailWord_4515158, baseEnd_4515158] using wordTrace_append hprefix tailTrace_4515158
  have hstable : (prefixWord ++ tailWord_4515158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515158).length < 2 ^ (prefixWord ++ tailWord_4515158).sum := by decide
  have hdescent : baseEnd_4515158 < baseStart_4515158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515180 : List Nat := [2, 2, 1, 1, 5, 2, 1, 2, 7]
def baseStart_4515180 : Nat := 118140960795 + 4515180 * 2 ^ 59
def prefixEnd_4515180 : Nat := 4983230072969 + 3 ^ 40 * 4515180 * 2
def baseEnd_4515180 : Nat := 257606397951972174576119

theorem tailTrace_4515180 : CollatzResearch.WordTrace tailWord_4515180 prefixEnd_4515180 257606397951972174576119 := by
  unfold tailWord_4515180
  simp only [CollatzResearch.WordTrace]
  refine ⟨82341071891140733098103497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109788095854854310797471329 82341071891140733098103497)
  ·
    refine ⟨61755803918355549823577623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82341071891140733098103497 61755803918355549823577623)
    ·
      refine ⟨92633705877533324735366435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61755803918355549823577623 92633705877533324735366435)
      ·
        refine ⟨138950558816299987103049653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92633705877533324735366435 138950558816299987103049653)
        ·
          refine ⟨13026614889028123790910905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 138950558816299987103049653 13026614889028123790910905)
          ·
            refine ⟨9769961166771092843183179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13026614889028123790910905 9769961166771092843183179)
            ·
              refine ⟨14654941750156639264774769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9769961166771092843183179 14654941750156639264774769)
              ·
                refine ⟨10991206312617479448581077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14654941750156639264774769 10991206312617479448581077)
                ·
                  refine ⟨257606397951972174576119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10991206312617479448581077 257606397951972174576119)
                  ·
                    rfl

theorem cell23_4515180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 7].length) (baseStart_4515180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515180 prefixEnd_4515180 := by exact prefixLift 4515180
  have htrace : WordTrace (prefixWord ++ tailWord_4515180) baseStart_4515180 baseEnd_4515180 := by
    simpa [prefixWord, tailWord_4515180, baseEnd_4515180] using wordTrace_append hprefix tailTrace_4515180
  have hstable : (prefixWord ++ tailWord_4515180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515180).length < 2 ^ (prefixWord ++ tailWord_4515180).sum := by decide
  have hdescent : baseEnd_4515180 < baseStart_4515180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515197 : List Nat := [1, 4, 1, 1, 2, 2, 4, 3, 5]
def baseStart_4515197 : Nat := 118140960795 + 4515197 * 2 ^ 59
def prefixEnd_4515197 : Nat := 4983230072969 + 3 ^ 40 * 4515197 * 2
def baseEnd_4515197 : Nat := 257607367859875111630277

theorem tailTrace_4515197 : CollatzResearch.WordTrace tailWord_4515197 prefixEnd_4515197 257607367859875111630277 := by
  unfold tailWord_4515197
  simp only [CollatzResearch.WordTrace]
  refine ⟨164682763823219878099575845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109788509215479918733050563 164682763823219878099575845)
  ·
    refine ⟨30878018216853727143670471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164682763823219878099575845 30878018216853727143670471)
    ·
      refine ⟨46317027325280590715505707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30878018216853727143670471 46317027325280590715505707)
      ·
        refine ⟨69475540987920886073258561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46317027325280590715505707 69475540987920886073258561)
        ·
          refine ⟨52106655740940664554943921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69475540987920886073258561 52106655740940664554943921)
          ·
            refine ⟨39079991805705498416207941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52106655740940664554943921 39079991805705498416207941)
            ·
              refine ⟨7327498463569780953038989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39079991805705498416207941 7327498463569780953038989)
              ·
                refine ⟨2747811923838667857389621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7327498463569780953038989 2747811923838667857389621)
                ·
                  refine ⟨257607367859875111630277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2747811923838667857389621 257607367859875111630277)
                  ·
                    rfl

theorem cell23_4515197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_4515197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515197 prefixEnd_4515197 := by exact prefixLift 4515197
  have htrace : WordTrace (prefixWord ++ tailWord_4515197) baseStart_4515197 baseEnd_4515197 := by
    simpa [prefixWord, tailWord_4515197, baseEnd_4515197] using wordTrace_append hprefix tailTrace_4515197
  have hstable : (prefixWord ++ tailWord_4515197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515197).length < 2 ^ (prefixWord ++ tailWord_4515197).sum := by decide
  have hdescent : baseEnd_4515197 < baseStart_4515197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515274 : List Nat := [3, 1, 2, 1, 2, 5, 1, 1, 3, 4]
def baseStart_4515274 : Nat := 118140960795 + 4515274 * 2 ^ 59
def prefixEnd_4515274 : Nat := 4983230072969 + 3 ^ 40 * 4515274 * 2
def baseEnd_4515274 : Nat := 772835282916424067803213

theorem tailTrace_4515274 : CollatzResearch.WordTrace tailWord_4515274 prefixEnd_4515274 772835282916424067803213 := by
  unfold tailWord_4515274
  simp only [CollatzResearch.WordTrace]
  refine ⟨41171393060985230062532219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109790381495960613500085917 41171393060985230062532219)
  ·
    refine ⟨61757089591477845093798329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41171393060985230062532219 61757089591477845093798329)
    ·
      refine ⟨46317817193608383820348747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61757089591477845093798329 46317817193608383820348747)
      ·
        refine ⟨69476725790412575730523121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46317817193608383820348747 69476725790412575730523121)
        ·
          refine ⟨52107544342809431797892341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69476725790412575730523121 52107544342809431797892341)
          ·
            refine ⟨4885082282138384231052407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52107544342809431797892341 4885082282138384231052407)
            ·
              refine ⟨7327623423207576346578611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4885082282138384231052407 7327623423207576346578611)
              ·
                refine ⟨10991435134811364519867917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7327623423207576346578611 10991435134811364519867917)
                ·
                  refine ⟨4121788175554261694950469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10991435134811364519867917 4121788175554261694950469)
                  ·
                    refine ⟨772835282916424067803213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4121788175554261694950469 772835282916424067803213)
                    ·
                      rfl

theorem cell23_4515274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_4515274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515274 prefixEnd_4515274 := by exact prefixLift 4515274
  have htrace : WordTrace (prefixWord ++ tailWord_4515274) baseStart_4515274 baseEnd_4515274 := by
    simpa [prefixWord, tailWord_4515274, baseEnd_4515274] using wordTrace_append hprefix tailTrace_4515274
  have hstable : (prefixWord ++ tailWord_4515274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515274).length < 2 ^ (prefixWord ++ tailWord_4515274).sum := by decide
  have hdescent : baseEnd_4515274 < baseStart_4515274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515324 : List Nat := [2, 2, 2, 1, 2, 1, 4, 2, 2, 3, 2]
def baseStart_4515324 : Nat := 118140960795 + 4515324 * 2 ^ 59
def prefixEnd_4515324 : Nat := 4983230072969 + 3 ^ 40 * 4515324 * 2
def baseEnd_4515324 : Nat := 2318531522781997007784409

theorem tailTrace_4515324 : CollatzResearch.WordTrace tailWord_4515324 prefixEnd_4515324 2318531522781997007784409 := by
  unfold tailWord_4515324
  simp only [CollatzResearch.WordTrace]
  refine ⟨82343697946879889394724513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109791597262506519192966017 82343697946879889394724513)
  ·
    refine ⟨61757773460159917046043385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82343697946879889394724513 61757773460159917046043385)
    ·
      refine ⟨46318330095119937784532539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61757773460159917046043385 46318330095119937784532539)
      ·
        refine ⟨69477495142679906676798809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46318330095119937784532539 69477495142679906676798809)
        ·
          refine ⟨52108121357009930007599107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69477495142679906676798809 52108121357009930007599107)
          ·
            refine ⟨78162182035514895011398661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52108121357009930007599107 78162182035514895011398661)
            ·
              refine ⟨14655409131659042814637249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78162182035514895011398661 14655409131659042814637249)
              ·
                refine ⟨10991556848744282110977937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14655409131659042814637249 10991556848744282110977937)
                ·
                  refine ⟨8243667636558211583233453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10991556848744282110977937 8243667636558211583233453)
                  ·
                    refine ⟨3091375363709329343712545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8243667636558211583233453 3091375363709329343712545)
                    ·
                      refine ⟨2318531522781997007784409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3091375363709329343712545 2318531522781997007784409)
                      ·
                        rfl

theorem cell23_4515324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 2, 3, 2].length) (baseStart_4515324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515324 prefixEnd_4515324 := by exact prefixLift 4515324
  have htrace : WordTrace (prefixWord ++ tailWord_4515324) baseStart_4515324 baseEnd_4515324 := by
    simpa [prefixWord, tailWord_4515324, baseEnd_4515324] using wordTrace_append hprefix tailTrace_4515324
  have hstable : (prefixWord ++ tailWord_4515324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515324).length < 2 ^ (prefixWord ++ tailWord_4515324).sum := by decide
  have hdescent : baseEnd_4515324 < baseStart_4515324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515347 : List Nat := [1, 1, 1, 2, 1, 7, 2, 1, 1, 6]
def baseStart_4515347 : Nat := 118140960795 + 4515347 * 2 ^ 59
def prefixEnd_4515347 : Nat := 4983230072969 + 3 ^ 40 * 4515347 * 2
def baseEnd_4515347 : Nat := 772847777612350139265601

theorem tailTrace_4515347 : CollatzResearch.WordTrace tailWord_4515347 prefixEnd_4515347 772847777612350139265601 := by
  unfold tailWord_4515347
  simp only [CollatzResearch.WordTrace]
  refine ⟨164688234772676453717536295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109792156515117635811690863 164688234772676453717536295)
  ·
    refine ⟨247032352159014680576304443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164688234772676453717536295 247032352159014680576304443)
    ·
      refine ⟨370548528238522020864456665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247032352159014680576304443 370548528238522020864456665)
      ·
        refine ⟨277911396178891515648342499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 370548528238522020864456665 277911396178891515648342499)
        ·
          refine ⟨416867094268337273472513749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277911396178891515648342499 416867094268337273472513749)
          ·
            refine ⟨9770322521914154847012041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 416867094268337273472513749 9770322521914154847012041)
            ·
              refine ⟨7327741891435616135259031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9770322521914154847012041 7327741891435616135259031)
              ·
                refine ⟨10991612837153424202888547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7327741891435616135259031 10991612837153424202888547)
                ·
                  refine ⟨16487419255730136304332821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10991612837153424202888547 16487419255730136304332821)
                  ·
                    refine ⟨772847777612350139265601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16487419255730136304332821 772847777612350139265601)
                    ·
                      rfl

theorem cell23_4515347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 6].length) (baseStart_4515347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515347 prefixEnd_4515347 := by exact prefixLift 4515347
  have htrace : WordTrace (prefixWord ++ tailWord_4515347) baseStart_4515347 baseEnd_4515347 := by
    simpa [prefixWord, tailWord_4515347, baseEnd_4515347] using wordTrace_append hprefix tailTrace_4515347
  have hstable : (prefixWord ++ tailWord_4515347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515347).length < 2 ^ (prefixWord ++ tailWord_4515347).sum := by decide
  have hdescent : baseEnd_4515347 < baseStart_4515347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515348 : List Nat := [2, 4, 3, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_4515348 : Nat := 118140960795 + 4515348 * 2 ^ 59
def prefixEnd_4515348 : Nat := 4983230072969 + 3 ^ 40 * 4515348 * 2
def baseEnd_4515348 : Nat := 2318543846317704913884299

theorem tailTrace_4515348 : CollatzResearch.WordTrace tailWord_4515348 prefixEnd_4515348 2318543846317704913884299 := by
  unfold tailWord_4515348
  simp only [CollatzResearch.WordTrace]
  refine ⟨82344135622836415444161349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109792180830448553925548465 82344135622836415444161349)
  ·
    refine ⟨15439525429281827895780253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82344135622836415444161349 15439525429281827895780253)
    ·
      refine ⟨5789822035980685460917595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15439525429281827895780253 5789822035980685460917595)
      ·
        refine ⟨8684733053971028191376393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5789822035980685460917595 8684733053971028191376393)
        ·
          refine ⟨6513549790478271143532295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8684733053971028191376393 6513549790478271143532295)
          ·
            refine ⟨9770324685717406715298443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6513549790478271143532295 9770324685717406715298443)
            ·
              refine ⟨14655487028576110072947665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9770324685717406715298443 14655487028576110072947665)
              ·
                refine ⟨10991615271432082554710749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14655487028576110072947665 10991615271432082554710749)
                ·
                  refine ⟨4121855726787030958016531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10991615271432082554710749 4121855726787030958016531)
                  ·
                    refine ⟨6182783590180546437024797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4121855726787030958016531 6182783590180546437024797)
                    ·
                      refine ⟨2318543846317704913884299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6182783590180546437024797 2318543846317704913884299)
                      ·
                        rfl

theorem cell23_4515348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_4515348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515348 prefixEnd_4515348 := by exact prefixLift 4515348
  have htrace : WordTrace (prefixWord ++ tailWord_4515348) baseStart_4515348 baseEnd_4515348 := by
    simpa [prefixWord, tailWord_4515348, baseEnd_4515348] using wordTrace_append hprefix tailTrace_4515348
  have hstable : (prefixWord ++ tailWord_4515348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515348).length < 2 ^ (prefixWord ++ tailWord_4515348).sum := by decide
  have hdescent : baseEnd_4515348 < baseStart_4515348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515368 : List Nat := [2, 1, 5, 2, 2, 2, 2, 1, 1, 5]
def baseStart_4515368 : Nat := 118140960795 + 4515368 * 2 ^ 59
def prefixEnd_4515368 : Nat := 4983230072969 + 3 ^ 40 * 4515368 * 2
def baseEnd_4515368 : Nat := 772851371976931611878069

theorem tailTrace_4515368 : CollatzResearch.WordTrace tailWord_4515368 prefixEnd_4515368 772851371976931611878069 := by
  unfold tailWord_4515368
  simp only [CollatzResearch.WordTrace]
  refine ⟨82344500352800187152025379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109792667137066916202700505 82344500352800187152025379)
  ·
    refine ⟨123516750529200280728038069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82344500352800187152025379 123516750529200280728038069)
    ·
      refine ⟨11579695362112526318253569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123516750529200280728038069 11579695362112526318253569)
      ·
        refine ⟨8684771521584394738690177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11579695362112526318253569 8684771521584394738690177)
        ·
          refine ⟨6513578641188296054017633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8684771521584394738690177 6513578641188296054017633)
          ·
            refine ⟨4885183980891222040513225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6513578641188296054017633 4885183980891222040513225)
            ·
              refine ⟨3663887985668416530384919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4885183980891222040513225 3663887985668416530384919)
              ·
                refine ⟨5495831978502624795577379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3663887985668416530384919 5495831978502624795577379)
                ·
                  refine ⟨8243747967753937193366069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5495831978502624795577379 8243747967753937193366069)
                  ·
                    refine ⟨772851371976931611878069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8243747967753937193366069 772851371976931611878069)
                    ·
                      rfl

theorem cell23_4515368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_4515368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515368 prefixEnd_4515368 := by exact prefixLift 4515368
  have htrace : WordTrace (prefixWord ++ tailWord_4515368) baseStart_4515368 baseEnd_4515368 := by
    simpa [prefixWord, tailWord_4515368, baseEnd_4515368] using wordTrace_append hprefix tailTrace_4515368
  have hstable : (prefixWord ++ tailWord_4515368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515368).length < 2 ^ (prefixWord ++ tailWord_4515368).sum := by decide
  have hdescent : baseEnd_4515368 < baseStart_4515368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515381 : List Nat := [1, 3, 3, 1, 1, 5, 1, 2, 2, 4]
def baseStart_4515381 : Nat := 118140960795 + 4515381 * 2 ^ 59
def prefixEnd_4515381 : Nat := 4983230072969 + 3 ^ 40 * 4515381 * 2
def baseEnd_4515381 : Nat := 772853597059767761590549

theorem tailTrace_4515381 : CollatzResearch.WordTrace tailWord_4515381 prefixEnd_4515381 772853597059767761590549 := by
  unfold tailWord_4515381
  simp only [CollatzResearch.WordTrace]
  refine ⟨164689474854553277524273997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109792983236368851682849331 164689474854553277524273997)
  ·
    refine ⟨61758553070457479071602749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164689474854553277524273997 61758553070457479071602749)
    ·
      refine ⟨23159457401421554651851031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61758553070457479071602749 23159457401421554651851031)
      ·
        refine ⟨34739186102132331977776547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23159457401421554651851031 34739186102132331977776547)
        ·
          refine ⟨52108779153198497966664821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34739186102132331977776547 52108779153198497966664821)
          ·
            refine ⟨4885198045612359184374827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52108779153198497966664821 4885198045612359184374827)
            ·
              refine ⟨7327797068418538776562241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4885198045612359184374827 7327797068418538776562241)
              ·
                refine ⟨5495847801313904082421681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7327797068418538776562241 5495847801313904082421681)
                ·
                  refine ⟨4121885850985428061816261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5495847801313904082421681 4121885850985428061816261)
                  ·
                    refine ⟨772853597059767761590549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4121885850985428061816261 772853597059767761590549)
                    ·
                      rfl

theorem cell23_4515381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_4515381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515381 prefixEnd_4515381 := by exact prefixLift 4515381
  have htrace : WordTrace (prefixWord ++ tailWord_4515381) baseStart_4515381 baseEnd_4515381 := by
    simpa [prefixWord, tailWord_4515381, baseEnd_4515381] using wordTrace_append hprefix tailTrace_4515381
  have hstable : (prefixWord ++ tailWord_4515381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515381).length < 2 ^ (prefixWord ++ tailWord_4515381).sum := by decide
  have hdescent : baseEnd_4515381 < baseStart_4515381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515388 : List Nat := [2, 2, 2, 2, 4, 1, 2, 1, 3, 2, 2]
def baseStart_4515388 : Nat := 118140960795 + 4515388 * 2 ^ 59
def prefixEnd_4515388 : Nat := 4983230072969 + 3 ^ 40 * 4515388 * 2
def baseEnd_4515388 : Nat := 2318564385543884757384115

theorem tailTrace_4515388 : CollatzResearch.WordTrace tailWord_4515388 prefixEnd_4515388 2318564385543884757384115 := by
  unfold tailWord_4515388
  simp only [CollatzResearch.WordTrace]
  refine ⟨82344865082763958859889409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109793153443685278479852545 82344865082763958859889409)
  ·
    refine ⟨61758648812072969144917057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82344865082763958859889409 61758648812072969144917057)
    ·
      refine ⟨46318986609054726858687793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61758648812072969144917057 46318986609054726858687793)
      ·
        refine ⟨34739239956791045144015845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46318986609054726858687793 34739239956791045144015845)
        ·
          refine ⟨6513607491898320964502971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34739239956791045144015845 6513607491898320964502971)
          ·
            refine ⟨9770411237847481446754457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6513607491898320964502971 9770411237847481446754457)
            ·
              refine ⟨7327808428385611085065843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9770411237847481446754457 7327808428385611085065843)
              ·
                refine ⟨10991712642578416627598765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7327808428385611085065843 10991712642578416627598765)
                ·
                  refine ⟨4121892240966906235349537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10991712642578416627598765 4121892240966906235349537)
                  ·
                    refine ⟨3091419180725179676512153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4121892240966906235349537 3091419180725179676512153)
                    ·
                      refine ⟨2318564385543884757384115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3091419180725179676512153 2318564385543884757384115)
                      ·
                        rfl

theorem cell23_4515388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_4515388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515388 prefixEnd_4515388 := by exact prefixLift 4515388
  have htrace : WordTrace (prefixWord ++ tailWord_4515388) baseStart_4515388 baseEnd_4515388 := by
    simpa [prefixWord, tailWord_4515388, baseEnd_4515388] using wordTrace_append hprefix tailTrace_4515388
  have hstable : (prefixWord ++ tailWord_4515388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515388).length < 2 ^ (prefixWord ++ tailWord_4515388).sum := by decide
  have hdescent : baseEnd_4515388 < baseStart_4515388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515398 : List Nat := [6, 1, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_4515398 : Nat := 118140960795 + 4515398 * 2 ^ 59
def prefixEnd_4515398 : Nat := 4983230072969 + 3 ^ 40 * 4515398 * 2
def baseEnd_4515398 : Nat := 772856506783476572753023

theorem tailTrace_4515398 : CollatzResearch.WordTrace tailWord_4515398 prefixEnd_4515398 772856506783476572753023 := by
  unfold tailWord_4515398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5146565465484115294613839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 109793396596994459618428565 5146565465484115294613839)
  ·
    refine ⟨7719848198226172941920759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5146565465484115294613839 7719848198226172941920759)
    ·
      refine ⟨11579772297339259412881139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7719848198226172941920759 11579772297339259412881139)
      ·
        refine ⟨17369658446008889119321709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11579772297339259412881139 17369658446008889119321709)
        ·
          refine ⟨6513621917253333419745641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17369658446008889119321709 6513621917253333419745641)
          ·
            refine ⟨4885216437940000064809231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6513621917253333419745641 4885216437940000064809231)
            ·
              refine ⟨7327824656910000097213847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4885216437940000064809231 7327824656910000097213847)
              ·
                refine ⟨10991736985365000145820771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7327824656910000097213847 10991736985365000145820771)
                ·
                  refine ⟨16487605478047500218731157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10991736985365000145820771 16487605478047500218731157)
                  ·
                    refine ⟨772856506783476572753023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16487605478047500218731157 772856506783476572753023)
                    ·
                      rfl

theorem cell23_4515398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_4515398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515398 prefixEnd_4515398 := by exact prefixLift 4515398
  have htrace : WordTrace (prefixWord ++ tailWord_4515398) baseStart_4515398 baseEnd_4515398 := by
    simpa [prefixWord, tailWord_4515398, baseEnd_4515398] using wordTrace_append hprefix tailTrace_4515398
  have hstable : (prefixWord ++ tailWord_4515398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515398).length < 2 ^ (prefixWord ++ tailWord_4515398).sum := by decide
  have hdescent : baseEnd_4515398 < baseStart_4515398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515404 : List Nat := [2, 2, 1, 3, 1, 3, 3, 1, 1, 3, 3]
def baseStart_4515404 : Nat := 118140960795 + 4515404 * 2 ^ 59
def prefixEnd_4515404 : Nat := 4983230072969 + 3 ^ 40 * 4515404 * 2
def baseEnd_4515404 : Nat := 2318572601234356694784041

theorem tailTrace_4515404 : CollatzResearch.WordTrace tailWord_4515404 prefixEnd_4515404 2318572601234356694784041 := by
  unfold tailWord_4515404
  simp only [CollatzResearch.WordTrace]
  refine ⟨82345156866734976226180633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109793542488979968301574177 82345156866734976226180633)
  ·
    refine ⟨61758867650051232169635475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82345156866734976226180633 61758867650051232169635475)
    ·
      refine ⟨92638301475076848254453213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61758867650051232169635475 92638301475076848254453213)
      ·
        refine ⟨34739363053153818095419955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92638301475076848254453213 34739363053153818095419955)
        ·
          refine ⟨52109044579730727143129933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34739363053153818095419955 52109044579730727143129933)
          ·
            refine ⟨19540891717399022678673725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52109044579730727143129933 19540891717399022678673725)
            ·
              refine ⟨7327834394024633504502647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19540891717399022678673725 7327834394024633504502647)
              ·
                refine ⟨10991751591036950256753971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7327834394024633504502647 10991751591036950256753971)
                ·
                  refine ⟨16487627386555425385130957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10991751591036950256753971 16487627386555425385130957)
                  ·
                    refine ⟨6182860269958284519424109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16487627386555425385130957 6182860269958284519424109)
                    ·
                      refine ⟨2318572601234356694784041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6182860269958284519424109 2318572601234356694784041)
                      ·
                        rfl

theorem cell23_4515404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_4515404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515404 prefixEnd_4515404 := by exact prefixLift 4515404
  have htrace : WordTrace (prefixWord ++ tailWord_4515404) baseStart_4515404 baseEnd_4515404 := by
    simpa [prefixWord, tailWord_4515404, baseEnd_4515404] using wordTrace_append hprefix tailTrace_4515404
  have hstable : (prefixWord ++ tailWord_4515404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515404).length < 2 ^ (prefixWord ++ tailWord_4515404).sum := by decide
  have hdescent : baseEnd_4515404 < baseStart_4515404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515431 : List Nat := [1, 1, 5, 1, 1, 1, 4, 3, 1, 3, 2]
def baseStart_4515431 : Nat := 118140960795 + 4515431 * 2 ^ 59
def prefixEnd_4515431 : Nat := 4983230072969 + 3 ^ 40 * 4515431 * 2
def baseEnd_4515431 : Nat := 2318586465212028089146417

theorem tailTrace_4515431 : CollatzResearch.WordTrace tailWord_4515431 prefixEnd_4515431 2318586465212028089146417 := by
  unfold tailWord_4515431
  simp only [CollatzResearch.WordTrace]
  refine ⟨164691298504372136063594147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109794199002914757375729431 164691298504372136063594147)
  ·
    refine ⟨247036947756558204095391221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164691298504372136063594147 247036947756558204095391221)
    ·
      refine ⟨23159713852177331633942927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 247036947756558204095391221 23159713852177331633942927)
      ·
        refine ⟨34739570778265997450914391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23159713852177331633942927 34739570778265997450914391)
        ·
          refine ⟨52109356167398996176371587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34739570778265997450914391 52109356167398996176371587)
          ·
            refine ⟨78164034251098494264557381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52109356167398996176371587 78164034251098494264557381)
            ·
              refine ⟨14655756422080967674604509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78164034251098494264557381 14655756422080967674604509)
              ·
                refine ⟨5495908658280362877976691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14655756422080967674604509 5495908658280362877976691)
                ·
                  refine ⟨8243862987420544316965037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5495908658280362877976691 8243862987420544316965037)
                  ·
                    refine ⟨3091448620282704118861889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8243862987420544316965037 3091448620282704118861889)
                    ·
                      refine ⟨2318586465212028089146417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3091448620282704118861889 2318586465212028089146417)
                      ·
                        rfl

theorem cell23_4515431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_4515431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515431 prefixEnd_4515431 := by exact prefixLift 4515431
  have htrace : WordTrace (prefixWord ++ tailWord_4515431) baseStart_4515431 baseEnd_4515431 := by
    simpa [prefixWord, tailWord_4515431, baseEnd_4515431] using wordTrace_append hprefix tailTrace_4515431
  have hstable : (prefixWord ++ tailWord_4515431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515431).length < 2 ^ (prefixWord ++ tailWord_4515431).sum := by decide
  have hdescent : baseEnd_4515431 < baseStart_4515431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515447 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 3]
def baseStart_4515447 : Nat := 118140960795 + 4515447 * 2 ^ 59
def prefixEnd_4515447 : Nat := 4983230072969 + 3 ^ 40 * 4515447 * 2
def baseEnd_4515447 : Nat := 2318594680902500026546343

theorem tailTrace_4515447 : CollatzResearch.WordTrace tailWord_4515447 prefixEnd_4515447 2318594680902500026546343 := by
  unfold tailWord_4515447
  simp only [CollatzResearch.WordTrace]
  refine ⟨164691882072314170796176595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109794588048209447197451063 164691882072314170796176595)
  ·
    refine ⟨247037823108471256194264893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164691882072314170796176595 247037823108471256194264893)
    ·
      refine ⟨92639183665676721072849335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247037823108471256194264893 92639183665676721072849335)
      ·
        refine ⟨138958775498515081609274003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92639183665676721072849335 138958775498515081609274003)
        ·
          refine ⟨208438163247772622413911005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138958775498515081609274003 208438163247772622413911005)
          ·
            refine ⟨78164311217914733405216627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208438163247772622413911005 78164311217914733405216627)
            ·
              refine ⟨117246466826872100107824941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78164311217914733405216627 117246466826872100107824941)
              ·
                refine ⟨43967425060077037540434353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117246466826872100107824941 43967425060077037540434353)
                ·
                  refine ⟨32975568795057778155325765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43967425060077037540434353 32975568795057778155325765)
                  ·
                    refine ⟨6182919149073333404123581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32975568795057778155325765 6182919149073333404123581)
                    ·
                      refine ⟨2318594680902500026546343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6182919149073333404123581 2318594680902500026546343)
                      ·
                        rfl

theorem cell23_4515447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 3].length) (baseStart_4515447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515447 prefixEnd_4515447 := by exact prefixLift 4515447
  have htrace : WordTrace (prefixWord ++ tailWord_4515447) baseStart_4515447 baseEnd_4515447 := by
    simpa [prefixWord, tailWord_4515447, baseEnd_4515447] using wordTrace_append hprefix tailTrace_4515447
  have hstable : (prefixWord ++ tailWord_4515447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515447).length < 2 ^ (prefixWord ++ tailWord_4515447).sum := by decide
  have hdescent : baseEnd_4515447 < baseStart_4515447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515501 : List Nat := [1, 5, 2, 1, 1, 1, 3, 4, 5]
def baseStart_4515501 : Nat := 118140960795 + 4515501 * 2 ^ 59
def prefixEnd_4515501 : Nat := 4983230072969 + 3 ^ 40 * 4515501 * 2
def baseEnd_4515501 : Nat := 257624712095315868363455

theorem tailTrace_4515501 : CollatzResearch.WordTrace tailWord_4515501 prefixEnd_4515501 257624712095315868363455 := by
  unfold tailWord_4515501
  simp only [CollatzResearch.WordTrace]
  refine ⟨164693851614118538018642357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109795901076079025345761571 164693851614118538018642357)
  ·
    refine ⟨15440048588823612939247721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 164693851614118538018642357 15440048588823612939247721)
    ·
      refine ⟨11580036441617709704435791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15440048588823612939247721 11580036441617709704435791)
      ·
        refine ⟨17370054662426564556653687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11580036441617709704435791 17370054662426564556653687)
        ·
          refine ⟨26055081993639846834980531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17370054662426564556653687 26055081993639846834980531)
          ·
            refine ⟨39082622990459770252470797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26055081993639846834980531 39082622990459770252470797)
            ·
              refine ⟨14655983621422413844676549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39082622990459770252470797 14655983621422413844676549)
              ·
                refine ⟨2747996929016702595876853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14655983621422413844676549 2747996929016702595876853)
                ·
                  refine ⟨257624712095315868363455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2747996929016702595876853 257624712095315868363455)
                  ·
                    rfl

theorem cell23_4515501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_4515501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515501 prefixEnd_4515501 := by exact prefixLift 4515501
  have htrace : WordTrace (prefixWord ++ tailWord_4515501) baseStart_4515501 baseEnd_4515501 := by
    simpa [prefixWord, tailWord_4515501, baseEnd_4515501] using wordTrace_append hprefix tailTrace_4515501
  have hstable : (prefixWord ++ tailWord_4515501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515501).length < 2 ^ (prefixWord ++ tailWord_4515501).sum := by decide
  have hdescent : baseEnd_4515501 < baseStart_4515501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515504 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 2, 5, 2]
def baseStart_4515504 : Nat := 118140960795 + 4515504 * 2 ^ 59
def prefixEnd_4515504 : Nat := 4983230072969 + 3 ^ 40 * 4515504 * 2
def baseEnd_4515504 : Nat := 2318623949299806303533581

theorem tailTrace_4515504 : CollatzResearch.WordTrace tailWord_4515504 prefixEnd_4515504 2318623949299806303533581 := by
  unfold tailWord_4515504
  simp only [CollatzResearch.WordTrace]
  refine ⟨82346980516553834765500783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109795974022071779687334377 82346980516553834765500783)
  ·
    refine ⟨123520470774830752148251175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82346980516553834765500783 123520470774830752148251175)
    ·
      refine ⟨185280706162246128222376763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123520470774830752148251175 185280706162246128222376763)
      ·
        refine ⟨277921059243369192333565145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185280706162246128222376763 277921059243369192333565145)
        ·
          refine ⟨208440794432526894250173859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277921059243369192333565145 208440794432526894250173859)
          ·
            refine ⟨312661191648790341375260789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208440794432526894250173859 312661191648790341375260789)
            ·
              refine ⟨29311986717074094503930699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 312661191648790341375260789 29311986717074094503930699)
              ·
                refine ⟨43967980075611141755896049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29311986717074094503930699 43967980075611141755896049)
                ·
                  refine ⟨32975985056708356316922037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43967980075611141755896049 32975985056708356316922037)
                  ·
                    refine ⟨3091498599066408404711441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32975985056708356316922037 3091498599066408404711441)
                    ·
                      refine ⟨2318623949299806303533581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3091498599066408404711441 2318623949299806303533581)
                      ·
                        rfl

theorem cell23_4515504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 2, 5, 2].length) (baseStart_4515504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515504 prefixEnd_4515504 := by exact prefixLift 4515504
  have htrace : WordTrace (prefixWord ++ tailWord_4515504) baseStart_4515504 baseEnd_4515504 := by
    simpa [prefixWord, tailWord_4515504, baseEnd_4515504] using wordTrace_append hprefix tailTrace_4515504
  have hstable : (prefixWord ++ tailWord_4515504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515504).length < 2 ^ (prefixWord ++ tailWord_4515504).sum := by decide
  have hdescent : baseEnd_4515504 < baseStart_4515504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515507 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 5]
def baseStart_4515507 : Nat := 118140960795 + 4515507 * 2 ^ 59
def prefixEnd_4515507 : Nat := 4983230072969 + 3 ^ 40 * 4515507 * 2
def baseEnd_4515507 : Nat := 2318625489741769791796067

theorem tailTrace_4515507 : CollatzResearch.WordTrace tailWord_4515507 prefixEnd_4515507 2318625489741769791796067 := by
  unfold tailWord_4515507
  simp only [CollatzResearch.WordTrace]
  refine ⟨164694070452096801043360775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109796046968064534028907183 164694070452096801043360775)
  ·
    refine ⟨247041105678145201565041163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164694070452096801043360775 247041105678145201565041163)
    ·
      refine ⟨370561658517217802347561745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247041105678145201565041163 370561658517217802347561745)
      ·
        refine ⟨277921243887913351760671309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 370561658517217802347561745 277921243887913351760671309)
        ·
          refine ⟨104220466457967506910251741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 277921243887913351760671309 104220466457967506910251741)
          ·
            refine ⟨39082674921737815091344403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104220466457967506910251741 39082674921737815091344403)
            ·
              refine ⟨58624012382606722637016605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39082674921737815091344403 58624012382606722637016605)
              ·
                refine ⟨21984004643477520988881227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58624012382606722637016605 21984004643477520988881227)
                ·
                  refine ⟨32976006965216281483321841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21984004643477520988881227 32976006965216281483321841)
                  ·
                    refine ⟨24732005223912211112491381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32976006965216281483321841 24732005223912211112491381)
                    ·
                      refine ⟨2318625489741769791796067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24732005223912211112491381 2318625489741769791796067)
                      ·
                        rfl

theorem cell23_4515507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 5].length) (baseStart_4515507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515507 prefixEnd_4515507 := by exact prefixLift 4515507
  have htrace : WordTrace (prefixWord ++ tailWord_4515507) baseStart_4515507 baseEnd_4515507 := by
    simpa [prefixWord, tailWord_4515507, baseEnd_4515507] using wordTrace_append hprefix tailTrace_4515507
  have hstable : (prefixWord ++ tailWord_4515507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515507).length < 2 ^ (prefixWord ++ tailWord_4515507).sum := by decide
  have hdescent : baseEnd_4515507 < baseStart_4515507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515534 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4]
def baseStart_4515534 : Nat := 118140960795 + 4515534 * 2 ^ 59
def prefixEnd_4515534 : Nat := 4983230072969 + 3 ^ 40 * 4515534 * 2
def baseEnd_4515534 : Nat := 2318639353719441186158443

theorem tailTrace_4515534 : CollatzResearch.WordTrace tailWord_4515534 prefixEnd_4515534 2318639353719441186158443 := by
  unfold tailWord_4515534
  simp only [CollatzResearch.WordTrace]
  refine ⟨20586881902874873081824207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109796703481999323103062437 20586881902874873081824207)
  ·
    refine ⟨30880322854312309622736311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20586881902874873081824207 30880322854312309622736311)
    ·
      refine ⟨46320484281468464434104467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30880322854312309622736311 46320484281468464434104467)
      ·
        refine ⟨69480726422202696651156701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46320484281468464434104467 69480726422202696651156701)
        ·
          refine ⟨26055272408326011244183763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69480726422202696651156701 26055272408326011244183763)
          ·
            refine ⟨39082908612489016866275645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26055272408326011244183763 39082908612489016866275645)
            ·
              refine ⟨14656090729683381324853367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39082908612489016866275645 14656090729683381324853367)
              ·
                refine ⟨21984136094525071987280051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14656090729683381324853367 21984136094525071987280051)
                ·
                  refine ⟨32976204141787607980920077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21984136094525071987280051 32976204141787607980920077)
                  ·
                    refine ⟨12366076553170352992845029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32976204141787607980920077 12366076553170352992845029)
                    ·
                      refine ⟨2318639353719441186158443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12366076553170352992845029 2318639353719441186158443)
                      ·
                        rfl

theorem cell23_4515534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_4515534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515534 prefixEnd_4515534 := by exact prefixLift 4515534
  have htrace : WordTrace (prefixWord ++ tailWord_4515534) baseStart_4515534 baseEnd_4515534 := by
    simpa [prefixWord, tailWord_4515534, baseEnd_4515534] using wordTrace_append hprefix tailTrace_4515534
  have hstable : (prefixWord ++ tailWord_4515534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515534).length < 2 ^ (prefixWord ++ tailWord_4515534).sum := by decide
  have hdescent : baseEnd_4515534 < baseStart_4515534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515544 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 5, 4]
def baseStart_4515544 : Nat := 118140960795 + 4515544 * 2 ^ 59
def prefixEnd_4515544 : Nat := 4983230072969 + 3 ^ 40 * 4515544 * 2
def baseEnd_4515544 : Nat := 772881496175328715677799

theorem tailTrace_4515544 : CollatzResearch.WordTrace tailWord_4515544 prefixEnd_4515544 772881496175328715677799 := by
  unfold tailWord_4515544
  simp only [CollatzResearch.WordTrace]
  refine ⟨82347709976481378181228843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109796946635308504241638457 82347709976481378181228843)
  ·
    refine ⟨123521564964722067271843265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82347709976481378181228843 123521564964722067271843265)
    ·
      refine ⟨92641173723541550453882449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123521564964722067271843265 92641173723541550453882449)
      ·
        refine ⟨69480880292656162840411837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92641173723541550453882449 69480880292656162840411837)
        ·
          refine ⟨26055330109746061065154439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69480880292656162840411837 26055330109746061065154439)
          ·
            refine ⟨39082995164619091597731659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26055330109746061065154439 39082995164619091597731659)
            ·
              refine ⟨58624492746928637396597489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39082995164619091597731659 58624492746928637396597489)
              ·
                refine ⟨43968369560196478047448117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58624492746928637396597489 43968369560196478047448117)
                ·
                  refine ⟨4122034646268419816948261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43968369560196478047448117 4122034646268419816948261)
                  ·
                    refine ⟨772881496175328715677799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4122034646268419816948261 772881496175328715677799)
                    ·
                      rfl

theorem cell23_4515544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 5, 4].length) (baseStart_4515544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515544 prefixEnd_4515544 := by exact prefixLift 4515544
  have htrace : WordTrace (prefixWord ++ tailWord_4515544) baseStart_4515544 baseEnd_4515544 := by
    simpa [prefixWord, tailWord_4515544, baseEnd_4515544] using wordTrace_append hprefix tailTrace_4515544
  have hstable : (prefixWord ++ tailWord_4515544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515544).length < 2 ^ (prefixWord ++ tailWord_4515544).sum := by decide
  have hdescent : baseEnd_4515544 < baseStart_4515544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515611 : List Nat := [1, 1, 1, 1, 1, 1, 4, 6, 2, 3, 2]
def baseStart_4515611 : Nat := 118140960795 + 4515611 * 2 ^ 59
def prefixEnd_4515611 : Nat := 4983230072969 + 3 ^ 40 * 4515611 * 2
def baseEnd_4515611 : Nat := 2318678891729837384895589

theorem tailTrace_4515611 : CollatzResearch.WordTrace tailWord_4515611 prefixEnd_4515611 2318678891729837384895589 := by
  unfold tailWord_4515611
  simp only [CollatzResearch.WordTrace]
  refine ⟨164697863643720026805146687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109798575762480017870097791 164697863643720026805146687)
  ·
    refine ⟨247046795465580040207720031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164697863643720026805146687 247046795465580040207720031)
    ·
      refine ⟨370570193198370060311580047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247046795465580040207720031 370570193198370060311580047)
      ·
        refine ⟨555855289797555090467370071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370570193198370060311580047 555855289797555090467370071)
        ·
          refine ⟨833782934696332635701055107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 555855289797555090467370071 833782934696332635701055107)
          ·
            refine ⟨1250674402044498953551582661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 833782934696332635701055107 1250674402044498953551582661)
            ·
              refine ⟨234501450383343553790921749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1250674402044498953551582661 234501450383343553790921749)
              ·
                refine ⟨10992255486719229083949457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 234501450383343553790921749 10992255486719229083949457)
                ·
                  refine ⟨8244191615039421812962093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10992255486719229083949457 8244191615039421812962093)
                  ·
                    refine ⟨3091571855639783179860785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8244191615039421812962093 3091571855639783179860785)
                    ·
                      refine ⟨2318678891729837384895589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3091571855639783179860785 2318678891729837384895589)
                      ·
                        rfl

theorem cell23_4515611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 3, 2].length) (baseStart_4515611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515611 prefixEnd_4515611 := by exact prefixLift 4515611
  have htrace : WordTrace (prefixWord ++ tailWord_4515611) baseStart_4515611 baseEnd_4515611 := by
    simpa [prefixWord, tailWord_4515611, baseEnd_4515611] using wordTrace_append hprefix tailTrace_4515611
  have hstable : (prefixWord ++ tailWord_4515611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515611).length < 2 ^ (prefixWord ++ tailWord_4515611).sum := by decide
  have hdescent : baseEnd_4515611 < baseStart_4515611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515638 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 3, 5]
def baseStart_4515638 : Nat := 118140960795 + 4515638 * 2 ^ 59
def prefixEnd_4515638 : Nat := 4983230072969 + 3 ^ 40 * 4515638 * 2
def baseEnd_4515638 : Nat := 772897585235836259752655

theorem tailTrace_4515638 : CollatzResearch.WordTrace tailWord_4515638 prefixEnd_4515638 772897585235836259752655 := by
  unfold tailWord_4515638
  simp only [CollatzResearch.WordTrace]
  refine ⟨10293678025913888151023723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109799232276414806944253045 10293678025913888151023723)
  ·
    refine ⟨15440517038870832226535585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10293678025913888151023723 15440517038870832226535585)
    ·
      refine ⟨11580387779153124169901689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15440517038870832226535585 11580387779153124169901689)
      ·
        refine ⟨8685290834364843127426267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11580387779153124169901689 8685290834364843127426267)
        ·
          refine ⟨13027936251547264691139401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8685290834364843127426267 13027936251547264691139401)
          ·
            refine ⟨9770952188660448518354551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13027936251547264691139401 9770952188660448518354551)
            ·
              refine ⟨14656428282990672777531827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9770952188660448518354551 14656428282990672777531827)
              ·
                refine ⟨21984642424486009166297741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14656428282990672777531827 21984642424486009166297741)
                ·
                  refine ⟨8244240909182253437361653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21984642424486009166297741 8244240909182253437361653)
                  ·
                    refine ⟨772897585235836259752655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8244240909182253437361653 772897585235836259752655)
                    ·
                      rfl

theorem cell23_4515638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_4515638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515638 prefixEnd_4515638 := by exact prefixLift 4515638
  have htrace : WordTrace (prefixWord ++ tailWord_4515638) baseStart_4515638 baseEnd_4515638 := by
    simpa [prefixWord, tailWord_4515638, baseEnd_4515638] using wordTrace_append hprefix tailTrace_4515638
  have hstable : (prefixWord ++ tailWord_4515638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515638).length < 2 ^ (prefixWord ++ tailWord_4515638).sum := by decide
  have hdescent : baseEnd_4515638 < baseStart_4515638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515644 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 3, 1, 5]
def baseStart_4515644 : Nat := 118140960795 + 4515644 * 2 ^ 59
def prefixEnd_4515644 : Nat := 4983230072969 + 3 ^ 40 * 4515644 * 2
def baseEnd_4515644 : Nat := 2318695836591435755782937

theorem tailTrace_4515644 : CollatzResearch.WordTrace tailWord_4515644 prefixEnd_4515644 2318695836591435755782937 := by
  unfold tailWord_4515644
  simp only [CollatzResearch.WordTrace]
  refine ⟨82349533626300236720548993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109799378168400315627398657 82349533626300236720548993)
  ·
    refine ⟨61762150219725177540411745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82349533626300236720548993 61762150219725177540411745)
    ·
      refine ⟨46321612664793883155308809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61762150219725177540411745 46321612664793883155308809)
      ·
        refine ⟨34741209498595412366481607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46321612664793883155308809 34741209498595412366481607)
        ·
          refine ⟨52111814247893118549722411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34741209498595412366481607 52111814247893118549722411)
          ·
            refine ⟨78167721371839677824583617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52111814247893118549722411 78167721371839677824583617)
            ·
              refine ⟨58625791028879758368437713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78167721371839677824583617 58625791028879758368437713)
              ·
                refine ⟨43969343271659818776328285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58625791028879758368437713 43969343271659818776328285)
                ·
                  refine ⟨16488503726872432041123107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43969343271659818776328285 16488503726872432041123107)
                  ·
                    refine ⟨24732755590308648061684661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16488503726872432041123107 24732755590308648061684661)
                    ·
                      refine ⟨2318695836591435755782937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24732755590308648061684661 2318695836591435755782937)
                      ·
                        rfl

theorem cell23_4515644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_4515644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515644 prefixEnd_4515644 := by exact prefixLift 4515644
  have htrace : WordTrace (prefixWord ++ tailWord_4515644) baseStart_4515644 baseEnd_4515644 := by
    simpa [prefixWord, tailWord_4515644, baseEnd_4515644] using wordTrace_append hprefix tailTrace_4515644
  have hstable : (prefixWord ++ tailWord_4515644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515644).length < 2 ^ (prefixWord ++ tailWord_4515644).sum := by decide
  have hdescent : baseEnd_4515644 < baseStart_4515644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515645 : List Nat := [1, 4, 1, 4, 1, 2, 2, 1, 2, 3, 2]
def baseStart_4515645 : Nat := 118140960795 + 4515645 * 2 ^ 59
def prefixEnd_4515645 : Nat := 4983230072969 + 3 ^ 40 * 4515645 * 2
def baseEnd_4515645 : Nat := 2318696350072090251870433

theorem tailTrace_4515645 : CollatzResearch.WordTrace tailWord_4515645 prefixEnd_4515645 2318696350072090251870433 := by
  unfold tailWord_4515645
  simp only [CollatzResearch.WordTrace]
  refine ⟨164699103725596850611884389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109799402483731233741256259 164699103725596850611884389)
  ·
    refine ⟨30881081948549409489728323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164699103725596850611884389 30881081948549409489728323)
    ·
      refine ⟨46321622922824114234592485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30881081948549409489728323 46321622922824114234592485)
      ·
        refine ⟨8685304298029521418986091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46321622922824114234592485 8685304298029521418986091)
        ·
          refine ⟨13027956447044282128479137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8685304298029521418986091 13027956447044282128479137)
          ·
            refine ⟨9770967335283211596359353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13027956447044282128479137 9770967335283211596359353)
            ·
              refine ⟨7328225501462408697269515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9770967335283211596359353 7328225501462408697269515)
              ·
                refine ⟨10992338252193613045904273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7328225501462408697269515 10992338252193613045904273)
                ·
                  refine ⟨8244253689145209784428205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10992338252193613045904273 8244253689145209784428205)
                  ·
                    refine ⟨3091595133429453669160577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8244253689145209784428205 3091595133429453669160577)
                    ·
                      refine ⟨2318696350072090251870433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3091595133429453669160577 2318696350072090251870433)
                      ·
                        rfl

theorem cell23_4515645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_4515645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515645 prefixEnd_4515645 := by exact prefixLift 4515645
  have htrace : WordTrace (prefixWord ++ tailWord_4515645) baseStart_4515645 baseEnd_4515645 := by
    simpa [prefixWord, tailWord_4515645, baseEnd_4515645] using wordTrace_append hprefix tailTrace_4515645
  have hstable : (prefixWord ++ tailWord_4515645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515645).length < 2 ^ (prefixWord ++ tailWord_4515645).sum := by decide
  have hdescent : baseEnd_4515645 < baseStart_4515645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515658 : List Nat := [3, 1, 2, 1, 1, 1, 7, 1, 1, 1, 4]
def baseStart_4515658 : Nat := 118140960795 + 4515658 * 2 ^ 59
def prefixEnd_4515658 : Nat := 4983230072969 + 3 ^ 40 * 4515658 * 2
def baseEnd_4515658 : Nat := 2318703025320598701007873

theorem tailTrace_4515658 : CollatzResearch.WordTrace tailWord_4515658 prefixEnd_4515658 2318703025320598701007873 := by
  unfold tailWord_4515658
  simp only [CollatzResearch.WordTrace]
  refine ⟨41174894468637438458026907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109799718583033169221405085 41174894468637438458026907)
  ·
    refine ⟨61762341702956157687040361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41174894468637438458026907 61762341702956157687040361)
    ·
      refine ⟨46321756277217118265280271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61762341702956157687040361 46321756277217118265280271)
      ·
        refine ⟨69482634415825677397920407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46321756277217118265280271 69482634415825677397920407)
        ·
          refine ⟨104223951623738516096880611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69482634415825677397920407 104223951623738516096880611)
          ·
            refine ⟨156335927435607774145320917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104223951623738516096880611 156335927435607774145320917)
            ·
              refine ⟨3664123299272057206530959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 156335927435607774145320917 3664123299272057206530959)
              ·
                refine ⟨5496184948908085809796439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3664123299272057206530959 5496184948908085809796439)
                ·
                  refine ⟨8244277423362128714694659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5496184948908085809796439 8244277423362128714694659)
                  ·
                    refine ⟨12366416135043193072041989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8244277423362128714694659 12366416135043193072041989)
                    ·
                      refine ⟨2318703025320598701007873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12366416135043193072041989 2318703025320598701007873)
                      ·
                        rfl

theorem cell23_4515658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 1, 1, 4].length) (baseStart_4515658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515658 prefixEnd_4515658 := by exact prefixLift 4515658
  have htrace : WordTrace (prefixWord ++ tailWord_4515658) baseStart_4515658 baseEnd_4515658 := by
    simpa [prefixWord, tailWord_4515658, baseEnd_4515658] using wordTrace_append hprefix tailTrace_4515658
  have hstable : (prefixWord ++ tailWord_4515658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515658).length < 2 ^ (prefixWord ++ tailWord_4515658).sum := by decide
  have hdescent : baseEnd_4515658 < baseStart_4515658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515668 : List Nat := [2, 4, 1, 1, 3, 1, 1, 4, 2, 4]
def baseStart_4515668 : Nat := 118140960795 + 4515668 * 2 ^ 59
def prefixEnd_4515668 : Nat := 4983230072969 + 3 ^ 40 * 4515668 * 2
def baseEnd_4515668 : Nat := 772902720042381220627609

theorem tailTrace_4515668 : CollatzResearch.WordTrace tailWord_4515668 prefixEnd_4515668 772902720042381220627609 := by
  unfold tailWord_4515668
  simp only [CollatzResearch.WordTrace]
  refine ⟨82349971302256762769985829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109799961736342350359981105 82349971302256762769985829)
  ·
    refine ⟨15440619619173143019372343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82349971302256762769985829 15440619619173143019372343)
    ·
      refine ⟨23160929428759714529058515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15440619619173143019372343 23160929428759714529058515)
      ·
        refine ⟨34741394143139571793587773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23160929428759714529058515 34741394143139571793587773)
        ·
          refine ⟨13028022803677339422595415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34741394143139571793587773 13028022803677339422595415)
          ·
            refine ⟨19542034205516009133893123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13028022803677339422595415 19542034205516009133893123)
            ·
              refine ⟨29313051308274013700839685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19542034205516009133893123 29313051308274013700839685)
              ·
                refine ⟨5496197120301377568907441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29313051308274013700839685 5496197120301377568907441)
                ·
                  refine ⟨4122147840226033176680581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5496197120301377568907441 4122147840226033176680581)
                  ·
                    refine ⟨772902720042381220627609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4122147840226033176680581 772902720042381220627609)
                    ·
                      rfl

theorem cell23_4515668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_4515668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515668 prefixEnd_4515668 := by exact prefixLift 4515668
  have htrace : WordTrace (prefixWord ++ tailWord_4515668) baseStart_4515668 baseEnd_4515668 := by
    simpa [prefixWord, tailWord_4515668, baseEnd_4515668] using wordTrace_append hprefix tailTrace_4515668
  have hstable : (prefixWord ++ tailWord_4515668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515668).length < 2 ^ (prefixWord ++ tailWord_4515668).sum := by decide
  have hdescent : baseEnd_4515668 < baseStart_4515668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515691 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 6, 1, 3]
def baseStart_4515691 : Nat := 118140960795 + 4515691 * 2 ^ 59
def prefixEnd_4515691 : Nat := 4983230072969 + 3 ^ 40 * 4515691 * 2
def baseEnd_4515691 : Nat := 2318719970182197071895221

theorem tailTrace_4515691 : CollatzResearch.WordTrace tailWord_4515691 prefixEnd_4515691 2318719970182197071895221 := by
  unfold tailWord_4515691
  simp only [CollatzResearch.WordTrace]
  refine ⟨164700781483430200468058927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109800520988953466978705951 164700781483430200468058927)
  ·
    refine ⟨247051172225145300702088391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164700781483430200468058927 247051172225145300702088391)
    ·
      refine ⟨370576758337717951053132587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247051172225145300702088391 370576758337717951053132587)
      ·
        refine ⟨555865137506576926579698881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370576758337717951053132587 555865137506576926579698881)
        ·
          refine ⟨416898853129932694934774161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 555865137506576926579698881 416898853129932694934774161)
          ·
            refine ⟨312674139847449521201080621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 416898853129932694934774161 312674139847449521201080621)
            ·
              refine ⟨117252802442793570450405233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 312674139847449521201080621 117252802442793570450405233)
              ·
                refine ⟨87939601832095177837803925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117252802442793570450405233 87939601832095177837803925)
                ·
                  refine ⟨4122168835879461461147059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87939601832095177837803925 4122168835879461461147059)
                  ·
                    refine ⟨6183253253819192191720589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4122168835879461461147059 6183253253819192191720589)
                    ·
                      refine ⟨2318719970182197071895221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6183253253819192191720589 2318719970182197071895221)
                      ·
                        rfl

theorem cell23_4515691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 1, 3].length) (baseStart_4515691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515691 prefixEnd_4515691 := by exact prefixLift 4515691
  have htrace : WordTrace (prefixWord ++ tailWord_4515691) baseStart_4515691 baseEnd_4515691 := by
    simpa [prefixWord, tailWord_4515691, baseEnd_4515691] using wordTrace_append hprefix tailTrace_4515691
  have hstable : (prefixWord ++ tailWord_4515691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515691).length < 2 ^ (prefixWord ++ tailWord_4515691).sum := by decide
  have hdescent : baseEnd_4515691 < baseStart_4515691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515741 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 2, 6]
def baseStart_4515741 : Nat := 118140960795 + 4515741 * 2 ^ 59
def prefixEnd_4515741 : Nat := 4983230072969 + 3 ^ 40 * 4515741 * 2
def baseEnd_4515741 : Nat := 772915214738307292089997

theorem tailTrace_4515741 : CollatzResearch.WordTrace tailWord_4515741 prefixEnd_4515741 772915214738307292089997 := by
  unfold tailWord_4515741
  simp only [CollatzResearch.WordTrace]
  refine ⟨164702605133249059007379077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109801736755499372671586051 164702605133249059007379077)
  ·
    refine ⟨30881738462484198563883577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164702605133249059007379077 30881738462484198563883577)
    ·
      refine ⟨23161303846863148922912683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30881738462484198563883577 23161303846863148922912683)
      ·
        refine ⟨34741955770294723384369025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23161303846863148922912683 34741955770294723384369025)
        ·
          refine ⟨26056466827721042538276769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34741955770294723384369025 26056466827721042538276769)
          ·
            refine ⟨19542350120790781903707577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26056466827721042538276769 19542350120790781903707577)
            ·
              refine ⟨14656762590593086427780683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19542350120790781903707577 14656762590593086427780683)
              ·
                refine ⟨21985143885889629641671025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14656762590593086427780683 21985143885889629641671025)
                ·
                  refine ⟨16488857914417222231253269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21985143885889629641671025 16488857914417222231253269)
                  ·
                    refine ⟨772915214738307292089997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16488857914417222231253269 772915214738307292089997)
                    ·
                      rfl

theorem cell23_4515741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_4515741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515741 prefixEnd_4515741 := by exact prefixLift 4515741
  have htrace : WordTrace (prefixWord ++ tailWord_4515741) baseStart_4515741 baseEnd_4515741 := by
    simpa [prefixWord, tailWord_4515741, baseEnd_4515741] using wordTrace_append hprefix tailTrace_4515741
  have hstable : (prefixWord ++ tailWord_4515741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515741).length < 2 ^ (prefixWord ++ tailWord_4515741).sum := by decide
  have hdescent : baseEnd_4515741 < baseStart_4515741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515765 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 4, 2, 2]
def baseStart_4515765 : Nat := 118140960795 + 4515765 * 2 ^ 59
def prefixEnd_4515765 : Nat := 4983230072969 + 3 ^ 40 * 4515765 * 2
def baseEnd_4515765 : Nat := 2318757967750629782369881

theorem tailTrace_4515765 : CollatzResearch.WordTrace tailWord_4515765 prefixEnd_4515765 2318757967750629782369881 := by
  unfold tailWord_4515765
  simp only [CollatzResearch.WordTrace]
  refine ⟨164703480485162111106252749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109802320323441407404168499 164703480485162111106252749)
  ·
    refine ⟨61763805181935791664844781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164703480485162111106252749 61763805181935791664844781)
    ·
      refine ⟨23161426943225921874316793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61763805181935791664844781 23161426943225921874316793)
      ·
        refine ⟨17371070207419441405737595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23161426943225921874316793 17371070207419441405737595)
        ·
          refine ⟨26056605311129162108606393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17371070207419441405737595 26056605311129162108606393)
          ·
            refine ⟨19542453983346871581454795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26056605311129162108606393 19542453983346871581454795)
            ·
              refine ⟨29313680975020307372182193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19542453983346871581454795 29313680975020307372182193)
              ·
                refine ⟨21985260731265230529136645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29313680975020307372182193 21985260731265230529136645)
                ·
                  refine ⟨4122236387112230724213121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21985260731265230529136645 4122236387112230724213121)
                  ·
                    refine ⟨3091677290334173043159841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4122236387112230724213121 3091677290334173043159841)
                    ·
                      refine ⟨2318757967750629782369881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3091677290334173043159841 2318757967750629782369881)
                      ·
                        rfl

theorem cell23_4515765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_4515765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515765 prefixEnd_4515765 := by exact prefixLift 4515765
  have htrace : WordTrace (prefixWord ++ tailWord_4515765) baseStart_4515765 baseEnd_4515765 := by
    simpa [prefixWord, tailWord_4515765, baseEnd_4515765] using wordTrace_append hprefix tailTrace_4515765
  have hstable : (prefixWord ++ tailWord_4515765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515765).length < 2 ^ (prefixWord ++ tailWord_4515765).sum := by decide
  have hdescent : baseEnd_4515765 < baseStart_4515765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515781 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 2, 3, 3]
def baseStart_4515781 : Nat := 118140960795 + 4515781 * 2 ^ 59
def prefixEnd_4515781 : Nat := 4983230072969 + 3 ^ 40 * 4515781 * 2
def baseEnd_4515781 : Nat := 2318766183441101719769807

theorem tailTrace_4515781 : CollatzResearch.WordTrace tailWord_4515781 prefixEnd_4515781 2318766183441101719769807 := by
  unfold tailWord_4515781
  simp only [CollatzResearch.WordTrace]
  refine ⟨164704064053104145838835197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109802709368736097225890131 164704064053104145838835197)
  ·
    refine ⟨61764024019914054689563199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164704064053104145838835197 61764024019914054689563199)
    ·
      refine ⟨92646036029871082034344799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61764024019914054689563199 92646036029871082034344799)
      ·
        refine ⟨138969054044806623051517199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92646036029871082034344799 138969054044806623051517199)
        ·
          refine ⟨208453581067209934577275799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138969054044806623051517199 208453581067209934577275799)
          ·
            refine ⟨312680371600814901865913699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208453581067209934577275799 312680371600814901865913699)
            ·
              refine ⟨469020557401222352798870549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312680371600814901865913699 469020557401222352798870549)
              ·
                refine ⟨21985338628182297787447057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 469020557401222352798870549 21985338628182297787447057)
                ·
                  refine ⟨16489003971136723340585293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21985338628182297787447057 16489003971136723340585293)
                  ·
                    refine ⟨6183376489176271252719485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16489003971136723340585293 6183376489176271252719485)
                    ·
                      refine ⟨2318766183441101719769807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6183376489176271252719485 2318766183441101719769807)
                      ·
                        rfl

theorem cell23_4515781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 3, 3].length) (baseStart_4515781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515781 prefixEnd_4515781 := by exact prefixLift 4515781
  have htrace : WordTrace (prefixWord ++ tailWord_4515781) baseStart_4515781 baseEnd_4515781 := by
    simpa [prefixWord, tailWord_4515781, baseEnd_4515781] using wordTrace_append hprefix tailTrace_4515781
  have hstable : (prefixWord ++ tailWord_4515781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515781).length < 2 ^ (prefixWord ++ tailWord_4515781).sum := by decide
  have hdescent : baseEnd_4515781 < baseStart_4515781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515788 : List Nat := [2, 2, 1, 4, 1, 4, 1, 1, 7]
def baseStart_4515788 : Nat := 118140960795 + 4515788 * 2 ^ 59
def prefixEnd_4515788 : Nat := 4983230072969 + 3 ^ 40 * 4515788 * 2
def baseEnd_4515788 : Nat := 257641086422853688042475

theorem tailTrace_4515788 : CollatzResearch.WordTrace tailWord_4515788 prefixEnd_4515788 257641086422853688042475 := by
  unfold tailWord_4515788
  simp only [CollatzResearch.WordTrace]
  refine ⟨82352159682039393017170009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109802879576052524022893345 82352159682039393017170009)
  ·
    refine ⟨61764119761529544762877507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82352159682039393017170009 61764119761529544762877507)
    ·
      refine ⟨92646179642294317144316261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61764119761529544762877507 92646179642294317144316261)
      ·
        refine ⟨17371158682930184464559299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92646179642294317144316261 17371158682930184464559299)
        ·
          refine ⟨26056738024395276696838949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17371158682930184464559299 26056738024395276696838949)
          ·
            refine ⟨4885638379574114380657303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26056738024395276696838949 4885638379574114380657303)
            ·
              refine ⟨7328457569361171570985955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4885638379574114380657303 7328457569361171570985955)
              ·
                refine ⟨10992686354041757356478933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7328457569361171570985955 10992686354041757356478933)
                ·
                  refine ⟨257641086422853688042475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10992686354041757356478933 257641086422853688042475)
                  ·
                    rfl

theorem cell23_4515788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 7].length) (baseStart_4515788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515788 prefixEnd_4515788 := by exact prefixLift 4515788
  have htrace : WordTrace (prefixWord ++ tailWord_4515788) baseStart_4515788 baseEnd_4515788 := by
    simpa [prefixWord, tailWord_4515788, baseEnd_4515788] using wordTrace_append hprefix tailTrace_4515788
  have hstable : (prefixWord ++ tailWord_4515788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515788).length < 2 ^ (prefixWord ++ tailWord_4515788).sum := by decide
  have hdescent : baseEnd_4515788 < baseStart_4515788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515818 : List Nat := [3, 1, 3, 1, 2, 1, 4, 1, 2, 5]
def baseStart_4515818 : Nat := 118140960795 + 4515818 * 2 ^ 59
def prefixEnd_4515818 : Nat := 4983230072969 + 3 ^ 40 * 4515818 * 2
def baseEnd_4515818 : Nat := 772928394075106025002379

theorem tailTrace_4515818 : CollatzResearch.WordTrace tailWord_4515818 prefixEnd_4515818 772928394075106025002379 := by
  unfold tailWord_4515818
  simp only [CollatzResearch.WordTrace]
  refine ⟨41176353388492525289483027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109803609035980067438621405 41176353388492525289483027)
  ·
    refine ⟨61764530082738787934224541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41176353388492525289483027 61764530082738787934224541)
    ·
      refine ⟨23161698781027045475334203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61764530082738787934224541 23161698781027045475334203)
      ·
        refine ⟨34742548171540568213001305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23161698781027045475334203 34742548171540568213001305)
        ·
          refine ⟨26056911128655426159750979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34742548171540568213001305 26056911128655426159750979)
          ·
            refine ⟨39085366692983139239626469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26056911128655426159750979 39085366692983139239626469)
            ·
              refine ⟨7328506254934338607429963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39085366692983139239626469 7328506254934338607429963)
              ·
                refine ⟨10992759382401507911144945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7328506254934338607429963 10992759382401507911144945)
                ·
                  refine ⟨8244569536801130933358709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10992759382401507911144945 8244569536801130933358709)
                  ·
                    refine ⟨772928394075106025002379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8244569536801130933358709 772928394075106025002379)
                    ·
                      rfl

theorem cell23_4515818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_4515818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515818 prefixEnd_4515818 := by exact prefixLift 4515818
  have htrace : WordTrace (prefixWord ++ tailWord_4515818) baseStart_4515818 baseEnd_4515818 := by
    simpa [prefixWord, tailWord_4515818, baseEnd_4515818] using wordTrace_append hprefix tailTrace_4515818
  have hstable : (prefixWord ++ tailWord_4515818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515818).length < 2 ^ (prefixWord ++ tailWord_4515818).sum := by decide
  have hdescent : baseEnd_4515818 < baseStart_4515818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515841 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_4515841 : Nat := 118140960795 + 4515841 * 2 ^ 59
def prefixEnd_4515841 : Nat := 4983230072969 + 3 ^ 40 * 4515841 * 2
def baseEnd_4515841 : Nat := 2318796992280371485019531

theorem tailTrace_4515841 : CollatzResearch.WordTrace tailWord_4515841 prefixEnd_4515841 2318796992280371485019531 := by
  unfold tailWord_4515841
  simp only [CollatzResearch.WordTrace]
  refine ⟨164706252432886776086019377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109804168288591184057346251 164706252432886776086019377)
  ·
    refine ⟨123529689324665082064514533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164706252432886776086019377 123529689324665082064514533)
    ·
      refine ⟨23161816748374702887096475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123529689324665082064514533 23161816748374702887096475)
      ·
        refine ⟨34742725122562054330644713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23161816748374702887096475 34742725122562054330644713)
        ·
          refine ⟨26057043841921540747983535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34742725122562054330644713 26057043841921540747983535)
          ·
            refine ⟨39085565762882311121975303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26057043841921540747983535 39085565762882311121975303)
            ·
              refine ⟨58628348644323466682962955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39085565762882311121975303 58628348644323466682962955)
              ·
                refine ⟨87942522966485200024444433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58628348644323466682962955 87942522966485200024444433)
                ·
                  refine ⟨65956892224863900018333325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87942522966485200024444433 65956892224863900018333325)
                  ·
                    refine ⟨24733834584323962506874997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65956892224863900018333325 24733834584323962506874997)
                    ·
                      refine ⟨2318796992280371485019531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24733834584323962506874997 2318796992280371485019531)
                      ·
                        rfl

theorem cell23_4515841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_4515841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515841 prefixEnd_4515841 := by exact prefixLift 4515841
  have htrace : WordTrace (prefixWord ++ tailWord_4515841) baseStart_4515841 baseEnd_4515841 := by
    simpa [prefixWord, tailWord_4515841, baseEnd_4515841] using wordTrace_append hprefix tailTrace_4515841
  have hstable : (prefixWord ++ tailWord_4515841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515841).length < 2 ^ (prefixWord ++ tailWord_4515841).sum := by decide
  have hdescent : baseEnd_4515841 < baseStart_4515841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515848 : List Nat := [2, 1, 3, 2, 1, 2, 2, 3, 3, 4]
def baseStart_4515848 : Nat := 118140960795 + 4515848 * 2 ^ 59
def prefixEnd_4515848 : Nat := 4983230072969 + 3 ^ 40 * 4515848 * 2
def baseEnd_4515848 : Nat := 772933528881650985877333

theorem tailTrace_4515848 : CollatzResearch.WordTrace tailWord_4515848 prefixEnd_4515848 772933528881650985877333 := by
  unfold tailWord_4515848
  simp only [CollatzResearch.WordTrace]
  refine ⟨82353253871930708140762099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109804338495907610854349465 82353253871930708140762099)
  ·
    refine ⟨123529880807896062211143149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82353253871930708140762099 123529880807896062211143149)
    ·
      refine ⟨46323705302961023329178681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123529880807896062211143149 46323705302961023329178681)
      ·
        refine ⟨34742778977220767496884011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46323705302961023329178681 34742778977220767496884011)
        ·
          refine ⟨52114168465831151245326017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34742778977220767496884011 52114168465831151245326017)
          ·
            refine ⟨39085626349373363433994513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52114168465831151245326017 39085626349373363433994513)
            ·
              refine ⟨29314219762030022575495885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39085626349373363433994513 29314219762030022575495885)
              ·
                refine ⟨10992832410761258465810957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29314219762030022575495885 10992832410761258465810957)
                ·
                  refine ⟨4122312154035471924679109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10992832410761258465810957 4122312154035471924679109)
                  ·
                    refine ⟨772933528881650985877333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4122312154035471924679109 772933528881650985877333)
                    ·
                      rfl

theorem cell23_4515848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_4515848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515848 prefixEnd_4515848 := by exact prefixLift 4515848
  have htrace : WordTrace (prefixWord ++ tailWord_4515848) baseStart_4515848 baseEnd_4515848 := by
    simpa [prefixWord, tailWord_4515848, baseEnd_4515848] using wordTrace_append hprefix tailTrace_4515848
  have hstable : (prefixWord ++ tailWord_4515848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515848).length < 2 ^ (prefixWord ++ tailWord_4515848).sum := by decide
  have hdescent : baseEnd_4515848 < baseStart_4515848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515882 : List Nat := [3, 1, 4, 1, 2, 1, 1, 5, 1, 4]
def baseStart_4515882 : Nat := 118140960795 + 4515882 * 2 ^ 59
def prefixEnd_4515882 : Nat := 4983230072969 + 3 ^ 40 * 4515882 * 2
def baseEnd_4515882 : Nat := 772939348329068608202281

theorem tailTrace_4515882 : CollatzResearch.WordTrace tailWord_4515882 prefixEnd_4515882 772939348329068608202281 := by
  unfold tailWord_4515882
  simp only [CollatzResearch.WordTrace]
  refine ⟨41176936956434560022065475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109805165217158826725507933 41176936956434560022065475)
  ·
    refine ⟨61765405434651840033098213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41176936956434560022065475 61765405434651840033098213)
    ·
      refine ⟨11581013518997220006205915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61765405434651840033098213 11581013518997220006205915)
      ·
        refine ⟨17371520278495830009308873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11581013518997220006205915 17371520278495830009308873)
        ·
          refine ⟨13028640208871872506981655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17371520278495830009308873 13028640208871872506981655)
          ·
            refine ⟨19542960313307808760472483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13028640208871872506981655 19542960313307808760472483)
            ·
              refine ⟨29314440469961713140708725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19542960313307808760472483 29314440469961713140708725)
              ·
                refine ⟨2748228794058910606941443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29314440469961713140708725 2748228794058910606941443)
                ·
                  refine ⟨4122343191088365910412165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2748228794058910606941443 4122343191088365910412165)
                  ·
                    refine ⟨772939348329068608202281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4122343191088365910412165 772939348329068608202281)
                    ·
                      rfl

theorem cell23_4515882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_4515882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515882 prefixEnd_4515882 := by exact prefixLift 4515882
  have htrace : WordTrace (prefixWord ++ tailWord_4515882) baseStart_4515882 baseEnd_4515882 := by
    simpa [prefixWord, tailWord_4515882, baseEnd_4515882] using wordTrace_append hprefix tailTrace_4515882
  have hstable : (prefixWord ++ tailWord_4515882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515882).length < 2 ^ (prefixWord ++ tailWord_4515882).sum := by decide
  have hdescent : baseEnd_4515882 < baseStart_4515882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515925 : List Nat := [1, 3, 2, 2, 1, 4, 2, 2, 1, 5]
def baseStart_4515925 : Nat := 118140960795 + 4515925 * 2 ^ 59
def prefixEnd_4515925 : Nat := 4983230072969 + 3 ^ 40 * 4515925 * 2
def baseEnd_4515925 : Nat := 772946708218449718789715

theorem tailTrace_4515925 : CollatzResearch.WordTrace tailWord_4515925 prefixEnd_4515925 772946708218449718789715 := by
  unfold tailWord_4515925
  simp only [CollatzResearch.WordTrace]
  refine ⟨164709316164582458432077229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109806210776388305621384819 164709316164582458432077229)
  ·
    refine ⟨61765993561718421912028961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164709316164582458432077229 61765993561718421912028961)
    ·
      refine ⟨46324495171288816434021721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61765993561718421912028961 46324495171288816434021721)
      ·
        refine ⟨34743371378466612325516291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46324495171288816434021721 34743371378466612325516291)
        ·
          refine ⟨52115057067699918488274437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34743371378466612325516291 52115057067699918488274437)
          ·
            refine ⟨9771573200193734716551457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52115057067699918488274437 9771573200193734716551457)
            ·
              refine ⟨7328679900145301037413593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9771573200193734716551457 7328679900145301037413593)
              ·
                refine ⟨5496509925108975778060195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7328679900145301037413593 5496509925108975778060195)
                ·
                  refine ⟨8244764887663463667090293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5496509925108975778060195 8244764887663463667090293)
                  ·
                    refine ⟨772946708218449718789715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8244764887663463667090293 772946708218449718789715)
                    ·
                      rfl

theorem cell23_4515925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_4515925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515925 prefixEnd_4515925 := by exact prefixLift 4515925
  have htrace : WordTrace (prefixWord ++ tailWord_4515925) baseStart_4515925 baseEnd_4515925 := by
    simpa [prefixWord, tailWord_4515925, baseEnd_4515925] using wordTrace_append hprefix tailTrace_4515925
  have hstable : (prefixWord ++ tailWord_4515925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515925).length < 2 ^ (prefixWord ++ tailWord_4515925).sum := by decide
  have hdescent : baseEnd_4515925 < baseStart_4515925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515948 : List Nat := [2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 5]
def baseStart_4515948 : Nat := 118140960795 + 4515948 * 2 ^ 59
def prefixEnd_4515948 : Nat := 4983230072969 + 3 ^ 40 * 4515948 * 2
def baseEnd_4515948 : Nat := 2318851934710402566381539

theorem tailTrace_4515948 : CollatzResearch.WordTrace tailWord_4515948 prefixEnd_4515948 2318851934710402566381539 := by
  unfold tailWord_4515948
  simp only [CollatzResearch.WordTrace]
  refine ⟨82355077521749566680082249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109806770028999422240109665 82355077521749566680082249)
  ·
    refine ⟨61766308141312175010061687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82355077521749566680082249 61766308141312175010061687)
    ·
      refine ⟨92649462211968262515092531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61766308141312175010061687 92649462211968262515092531)
      ·
        refine ⟨138974193317952393772638797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92649462211968262515092531 138974193317952393772638797)
        ·
          refine ⟨52115322494232147664739549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138974193317952393772638797 52115322494232147664739549)
          ·
            refine ⟨19543245935337055374277331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52115322494232147664739549 19543245935337055374277331)
            ·
              refine ⟨29314868903005583061415997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19543245935337055374277331 29314868903005583061415997)
              ·
                refine ⟨10993075838627093648030999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29314868903005583061415997 10993075838627093648030999)
                ·
                  refine ⟨16489613757940640472046499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10993075838627093648030999 16489613757940640472046499)
                  ·
                    refine ⟨24734420636910960708069749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16489613757940640472046499 24734420636910960708069749)
                    ·
                      refine ⟨2318851934710402566381539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24734420636910960708069749 2318851934710402566381539)
                      ·
                        rfl

theorem cell23_4515948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_4515948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515948 prefixEnd_4515948 := by exact prefixLift 4515948
  have htrace : WordTrace (prefixWord ++ tailWord_4515948) baseStart_4515948 baseEnd_4515948 := by
    simpa [prefixWord, tailWord_4515948, baseEnd_4515948] using wordTrace_append hprefix tailTrace_4515948
  have hstable : (prefixWord ++ tailWord_4515948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515948).length < 2 ^ (prefixWord ++ tailWord_4515948).sum := by decide
  have hdescent : baseEnd_4515948 < baseStart_4515948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515951 : List Nat := [1, 1, 2, 1, 3, 4, 11]
def baseStart_4515951 : Nat := 118140960795 + 4515951 * 2 ^ 59
def prefixEnd_4515951 : Nat := 4983230072969 + 3 ^ 40 * 4515951 * 2
def baseEnd_4515951 : Nat := 28627820680893408082025

theorem tailTrace_4515951 : CollatzResearch.WordTrace tailWord_4515951 prefixEnd_4515951 28627820680893408082025 := by
  unfold tailWord_4515951
  simp only [CollatzResearch.WordTrace]
  refine ⟨164710264462488264872523707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109806842974992176581682471 164710264462488264872523707)
  ·
    refine ⟨247065396693732397308785561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164710264462488264872523707 247065396693732397308785561)
    ·
      refine ⟨185299047520299297981589171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247065396693732397308785561 185299047520299297981589171)
      ·
        refine ⟨277948571280448946972383757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185299047520299297981589171 277948571280448946972383757)
        ·
          refine ⟨104230714230168355114643909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 277948571280448946972383757 104230714230168355114643909)
          ·
            refine ⟨19543258918156566583995733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104230714230168355114643909 19543258918156566583995733)
            ·
              refine ⟨28627820680893408082025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19543258918156566583995733 28627820680893408082025)
              ·
                rfl

theorem cell23_4515951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 11].length) (baseStart_4515951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515951 prefixEnd_4515951 := by exact prefixLift 4515951
  have htrace : WordTrace (prefixWord ++ tailWord_4515951) baseStart_4515951 baseEnd_4515951 := by
    simpa [prefixWord, tailWord_4515951, baseEnd_4515951] using wordTrace_append hprefix tailTrace_4515951
  have hstable : (prefixWord ++ tailWord_4515951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515951).length < 2 ^ (prefixWord ++ tailWord_4515951).sum := by decide
  have hdescent : baseEnd_4515951 < baseStart_4515951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515982 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3]
def baseStart_4515982 : Nat := 118140960795 + 4515982 * 2 ^ 59
def prefixEnd_4515982 : Nat := 4983230072969 + 3 ^ 40 * 4515982 * 2
def baseEnd_4515982 : Nat := 2318869393052655433356383

theorem tailTrace_4515982 : CollatzResearch.WordTrace tailWord_4515982 prefixEnd_4515982 2318869393052655433356383 := by
  unfold tailWord_4515982
  simp only [CollatzResearch.WordTrace]
  refine ⟨20588924390671994645862775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109807596750250638111268133 20588924390671994645862775)
  ·
    refine ⟨30883386586007991968794163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20588924390671994645862775 30883386586007991968794163)
    ·
      refine ⟨46325079879011987953191245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30883386586007991968794163 46325079879011987953191245)
      ·
        refine ⟨17371904954629495482446717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46325079879011987953191245 17371904954629495482446717)
        ·
          refine ⟨6514464357986060805917519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17371904954629495482446717 6514464357986060805917519)
          ·
            refine ⟨9771696536979091208876279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6514464357986060805917519 9771696536979091208876279)
            ·
              refine ⟨14657544805468636813314419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9771696536979091208876279 14657544805468636813314419)
              ·
                refine ⟨21986317208202955219971629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14657544805468636813314419 21986317208202955219971629)
                ·
                  refine ⟨8244868953076108207489361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21986317208202955219971629 8244868953076108207489361)
                  ·
                    refine ⟨6183651714807081155617021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8244868953076108207489361 6183651714807081155617021)
                    ·
                      refine ⟨2318869393052655433356383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6183651714807081155617021 2318869393052655433356383)
                      ·
                        rfl

theorem cell23_4515982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_4515982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515982 prefixEnd_4515982 := by exact prefixLift 4515982
  have htrace : WordTrace (prefixWord ++ tailWord_4515982) baseStart_4515982 baseEnd_4515982 := by
    simpa [prefixWord, tailWord_4515982, baseEnd_4515982] using wordTrace_append hprefix tailTrace_4515982
  have hstable : (prefixWord ++ tailWord_4515982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515982).length < 2 ^ (prefixWord ++ tailWord_4515982).sum := by decide
  have hdescent : baseEnd_4515982 < baseStart_4515982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4515999 : List Nat := [1, 1, 2, 6, 1, 2, 3, 1, 1, 2, 3]
def baseStart_4515999 : Nat := 118140960795 + 4515999 * 2 ^ 59
def prefixEnd_4515999 : Nat := 4983230072969 + 3 ^ 40 * 4515999 * 2
def baseEnd_4515999 : Nat := 2318878122223781866843805

theorem tailTrace_4515999 : CollatzResearch.WordTrace tailWord_4515999 prefixEnd_4515999 2318878122223781866843805 := by
  unfold tailWord_4515999
  simp only [CollatzResearch.WordTrace]
  refine ⟨164712015166314369070271051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109808010110876246046847367 164712015166314369070271051)
  ·
    refine ⟨247068022749471553605406577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164712015166314369070271051 247068022749471553605406577)
    ·
      refine ⟨185301017062103665204054933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247068022749471553605406577 185301017062103665204054933)
      ·
        refine ⟨8685985174786109306440075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 185301017062103665204054933 8685985174786109306440075)
        ·
          refine ⟨13028977762179163959660113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8685985174786109306440075 13028977762179163959660113)
          ·
            refine ⟨9771733321634372969745085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13028977762179163959660113 9771733321634372969745085)
            ·
              refine ⟨3664399995612889863654407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9771733321634372969745085 3664399995612889863654407)
              ·
                refine ⟨5496599993419334795481611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3664399995612889863654407 5496599993419334795481611)
                ·
                  refine ⟨8244899990129002193222417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5496599993419334795481611 8244899990129002193222417)
                  ·
                    refine ⟨6183674992596751644916813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8244899990129002193222417 6183674992596751644916813)
                    ·
                      refine ⟨2318878122223781866843805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6183674992596751644916813 2318878122223781866843805)
                      ·
                        rfl

theorem cell23_4515999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_4515999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4515999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4515999 prefixEnd_4515999 := by exact prefixLift 4515999
  have htrace : WordTrace (prefixWord ++ tailWord_4515999) baseStart_4515999 baseEnd_4515999 := by
    simpa [prefixWord, tailWord_4515999, baseEnd_4515999] using wordTrace_append hprefix tailTrace_4515999
  have hstable : (prefixWord ++ tailWord_4515999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4515999).length < 2 ^ (prefixWord ++ tailWord_4515999).sum := by decide
  have hdescent : baseEnd_4515999 < baseStart_4515999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4515999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516013 : List Nat := [1, 5, 2, 1, 2, 1, 4, 2, 1, 2, 2]
def baseStart_4516013 : Nat := 118140960795 + 4516013 * 2 ^ 59
def prefixEnd_4516013 : Nat := 4983230072969 + 3 ^ 40 * 4516013 * 2
def baseEnd_4516013 : Nat := 2318885310952944812068741

theorem tailTrace_4516013 : CollatzResearch.WordTrace tailWord_4516013 prefixEnd_4516013 2318885310952944812068741 := by
  unfold tailWord_4516013
  simp only [CollatzResearch.WordTrace]
  refine ⟨164712525788263649461280693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109808350525509099640853795 164712525788263649461280693)
  ·
    refine ⟨15441799292649717136995065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 164712525788263649461280693 15441799292649717136995065)
    ·
      refine ⟨11581349469487287852746299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15441799292649717136995065 11581349469487287852746299)
      ·
        refine ⟨17372024204230931779119449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11581349469487287852746299 17372024204230931779119449)
        ·
          refine ⟨13029018153173198834339587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17372024204230931779119449 13029018153173198834339587)
          ·
            refine ⟨19543527229759798251509381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13029018153173198834339587 19543527229759798251509381)
            ·
              refine ⟨3664411355579962172158009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19543527229759798251509381 3664411355579962172158009)
              ·
                refine ⟨2748308516684971629118507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3664411355579962172158009 2748308516684971629118507)
                ·
                  refine ⟨4122462775027457443677761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2748308516684971629118507 4122462775027457443677761)
                  ·
                    refine ⟨3091847081270593082758321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4122462775027457443677761 3091847081270593082758321)
                    ·
                      refine ⟨2318885310952944812068741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3091847081270593082758321 2318885310952944812068741)
                      ·
                        rfl

theorem cell23_4516013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_4516013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516013 prefixEnd_4516013 := by exact prefixLift 4516013
  have htrace : WordTrace (prefixWord ++ tailWord_4516013) baseStart_4516013 baseEnd_4516013 := by
    simpa [prefixWord, tailWord_4516013, baseEnd_4516013] using wordTrace_append hprefix tailTrace_4516013
  have hstable : (prefixWord ++ tailWord_4516013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516013).length < 2 ^ (prefixWord ++ tailWord_4516013).sum := by decide
  have hdescent : baseEnd_4516013 < baseStart_4516013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516018 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4]
def baseStart_4516018 : Nat := 118140960795 + 4516018 * 2 ^ 59
def prefixEnd_4516018 : Nat := 4983230072969 + 3 ^ 40 * 4516018 * 2
def baseEnd_4516018 : Nat := 2318887878356217292506217

theorem tailTrace_4516018 : CollatzResearch.WordTrace tailWord_4516018 prefixEnd_4516018 2318887878356217292506217 := by
  unfold tailWord_4516018
  simp only [CollatzResearch.WordTrace]
  refine ⟨41178177038311383828803177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109808472102163690210141805 41178177038311383828803177)
  ·
    refine ⟨30883632778733537871602383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41178177038311383828803177 30883632778733537871602383)
    ·
      refine ⟨46325449168100306807403575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30883632778733537871602383 46325449168100306807403575)
      ·
        refine ⟨69488173752150460211105363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46325449168100306807403575 69488173752150460211105363)
        ·
          refine ⟨104232260628225690316658045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69488173752150460211105363 104232260628225690316658045)
          ·
            refine ⟨39087097735584633868746767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104232260628225690316658045 39087097735584633868746767)
            ·
              refine ⟨58630646603376950803120151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39087097735584633868746767 58630646603376950803120151)
              ·
                refine ⟨87945969905065426204680227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58630646603376950803120151 87945969905065426204680227)
                ·
                  refine ⟨131918954857598139307020341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87945969905065426204680227 131918954857598139307020341)
                  ·
                    refine ⟨12367402017899825560033157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 131918954857598139307020341 12367402017899825560033157)
                    ·
                      refine ⟨2318887878356217292506217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12367402017899825560033157 2318887878356217292506217)
                      ·
                        rfl

theorem cell23_4516018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_4516018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516018 prefixEnd_4516018 := by exact prefixLift 4516018
  have htrace : WordTrace (prefixWord ++ tailWord_4516018) baseStart_4516018 baseEnd_4516018 := by
    simpa [prefixWord, tailWord_4516018, baseEnd_4516018] using wordTrace_append hprefix tailTrace_4516018
  have hstable : (prefixWord ++ tailWord_4516018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516018).length < 2 ^ (prefixWord ++ tailWord_4516018).sum := by decide
  have hdescent : baseEnd_4516018 < baseStart_4516018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516056 : List Nat := [2, 1, 2, 2, 4, 3, 2, 1, 1, 3, 2]
def baseStart_4516056 : Nat := 118140960795 + 4516056 * 2 ^ 59
def prefixEnd_4516056 : Nat := 4983230072969 + 3 ^ 40 * 4516056 * 2
def baseEnd_4516056 : Nat := 2318907390621088143831043

theorem tailTrace_4516056 : CollatzResearch.WordTrace tailWord_4516056 prefixEnd_4516056 2318907390621088143831043 := by
  unfold tailWord_4516056
  simp only [CollatzResearch.WordTrace]
  refine ⟨82357047063553933902548011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109809396084738578536730681 82357047063553933902548011)
  ·
    refine ⟨123535570595330900853822017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82357047063553933902548011 123535570595330900853822017)
    ·
      refine ⟨92651677946498175640366513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123535570595330900853822017 92651677946498175640366513)
      ·
        refine ⟨69488758459873631730274885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92651677946498175640366513 69488758459873631730274885)
        ·
          refine ⟨13029142211226305949426541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69488758459873631730274885 13029142211226305949426541)
          ·
            refine ⟨4885928329209864731034953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13029142211226305949426541 4885928329209864731034953)
            ·
              refine ⟨3664446246907398548276215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4885928329209864731034953 3664446246907398548276215)
              ·
                refine ⟨5496669370361097822414323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3664446246907398548276215 5496669370361097822414323)
                ·
                  refine ⟨8245004055541646733621485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5496669370361097822414323 8245004055541646733621485)
                  ·
                    refine ⟨3091876520828117525108057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8245004055541646733621485 3091876520828117525108057)
                    ·
                      refine ⟨2318907390621088143831043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3091876520828117525108057 2318907390621088143831043)
                      ·
                        rfl

theorem cell23_4516056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 1, 3, 2].length) (baseStart_4516056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516056 prefixEnd_4516056 := by exact prefixLift 4516056
  have htrace : WordTrace (prefixWord ++ tailWord_4516056) baseStart_4516056 baseEnd_4516056 := by
    simpa [prefixWord, tailWord_4516056, baseEnd_4516056] using wordTrace_append hprefix tailTrace_4516056
  have hstable : (prefixWord ++ tailWord_4516056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516056).length < 2 ^ (prefixWord ++ tailWord_4516056).sum := by decide
  have hdescent : baseEnd_4516056 < baseStart_4516056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516069 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 4, 2, 2]
def baseStart_4516069 : Nat := 118140960795 + 4516069 * 2 ^ 59
def prefixEnd_4516069 : Nat := 4983230072969 + 3 ^ 40 * 4516069 * 2
def baseEnd_4516069 : Nat := 2318914065869596592968483

theorem tailTrace_4516069 : CollatzResearch.WordTrace tailWord_4516069 prefixEnd_4516069 2318914065869596592968483 := by
  unfold tailWord_4516069
  simp only [CollatzResearch.WordTrace]
  refine ⟨164714568276060771025319261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109809712184040514016879507 164714568276060771025319261)
  ·
    refine ⟨61767963103522789134494723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164714568276060771025319261 61767963103522789134494723)
    ·
      refine ⟨92651944655284183701742085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61767963103522789134494723 92651944655284183701742085)
      ·
        refine ⟨17372239622865784444076641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92651944655284183701742085 17372239622865784444076641)
        ·
          refine ⟨13029179717149338333057481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17372239622865784444076641 13029179717149338333057481)
          ·
            refine ⟨9771884787862003749793111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13029179717149338333057481 9771884787862003749793111)
            ·
              refine ⟨14657827181793005624689667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9771884787862003749793111 14657827181793005624689667)
              ·
                refine ⟨21986740772689508437034501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14657827181793005624689667 21986740772689508437034501)
                ·
                  refine ⟨4122513894879282831943969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21986740772689508437034501 4122513894879282831943969)
                  ·
                    refine ⟨3091885421159462123957977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4122513894879282831943969 3091885421159462123957977)
                    ·
                      refine ⟨2318914065869596592968483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3091885421159462123957977 2318914065869596592968483)
                      ·
                        rfl

theorem cell23_4516069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_4516069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516069 prefixEnd_4516069 := by exact prefixLift 4516069
  have htrace : WordTrace (prefixWord ++ tailWord_4516069) baseStart_4516069 baseEnd_4516069 := by
    simpa [prefixWord, tailWord_4516069, baseEnd_4516069] using wordTrace_append hprefix tailTrace_4516069
  have hstable : (prefixWord ++ tailWord_4516069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516069).length < 2 ^ (prefixWord ++ tailWord_4516069).sum := by decide
  have hdescent : baseEnd_4516069 < baseStart_4516069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516075 : List Nat := [1, 1, 1, 1, 2, 5, 1, 6, 5]
def baseStart_4516075 : Nat := 118140960795 + 4516075 * 2 ^ 59
def prefixEnd_4516075 : Nat := 4983230072969 + 3 ^ 40 * 4516075 * 2
def baseEnd_4516075 : Nat := 257657460750391507721495

theorem tailTrace_4516075 : CollatzResearch.WordTrace tailWord_4516075 prefixEnd_4516075 257657460750391507721495 := by
  unfold tailWord_4516075
  simp only [CollatzResearch.WordTrace]
  refine ⟨164714787114039034050037679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109809858076026022700025119 164714787114039034050037679)
  ·
    refine ⟨247072180671058551075056519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164714787114039034050037679 247072180671058551075056519)
    ·
      refine ⟨370608271006587826612584779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247072180671058551075056519 370608271006587826612584779)
      ·
        refine ⟨555912406509881739918877169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370608271006587826612584779 555912406509881739918877169)
        ·
          refine ⟨416934304882411304939157877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 555912406509881739918877169 416934304882411304939157877)
          ·
            refine ⟨39087591082726059838046051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 416934304882411304939157877 39087591082726059838046051)
            ·
              refine ⟨58631386624089089757069077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39087591082726059838046051 58631386624089089757069077)
              ·
                refine ⟨2748346248004176082362613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58631386624089089757069077 2748346248004176082362613)
                ·
                  refine ⟨257657460750391507721495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2748346248004176082362613 257657460750391507721495)
                  ·
                    rfl

theorem cell23_4516075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 5].length) (baseStart_4516075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516075 prefixEnd_4516075 := by exact prefixLift 4516075
  have htrace : WordTrace (prefixWord ++ tailWord_4516075) baseStart_4516075 baseEnd_4516075 := by
    simpa [prefixWord, tailWord_4516075, baseEnd_4516075] using wordTrace_append hprefix tailTrace_4516075
  have hstable : (prefixWord ++ tailWord_4516075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516075).length < 2 ^ (prefixWord ++ tailWord_4516075).sum := by decide
  have hdescent : baseEnd_4516075 < baseStart_4516075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516122 : List Nat := [3, 1, 1, 3, 4, 1, 1, 2, 2, 5]
def baseStart_4516122 : Nat := 118140960795 + 4516122 * 2 ^ 59
def prefixEnd_4516122 : Nat := 4983230072969 + 3 ^ 40 * 4516122 * 2
def baseEnd_4516122 : Nat := 772980426781428295201913

theorem tailTrace_4516122 : CollatzResearch.WordTrace tailWord_4516122 prefixEnd_4516122 772980426781428295201913 := by
  unfold tailWord_4516122
  simp only [CollatzResearch.WordTrace]
  refine ⟨41179125336217190269249655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109811000896579174051332413 41179125336217190269249655)
  ·
    refine ⟨61768688004325785403874483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41179125336217190269249655 61768688004325785403874483)
    ·
      refine ⟨92653032006488678105811725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61768688004325785403874483 92653032006488678105811725)
      ·
        refine ⟨34744887002433254289679397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92653032006488678105811725 34744887002433254289679397)
        ·
          refine ⟨6514666312956235179314887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34744887002433254289679397 6514666312956235179314887)
          ·
            refine ⟨9771999469434352768972331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6514666312956235179314887 9771999469434352768972331)
            ·
              refine ⟨14657999204151529153458497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9771999469434352768972331 14657999204151529153458497)
              ·
                refine ⟨10993499403113646865093873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14657999204151529153458497 10993499403113646865093873)
                ·
                  refine ⟨8245124552335235148820405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10993499403113646865093873 8245124552335235148820405)
                  ·
                    refine ⟨772980426781428295201913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8245124552335235148820405 772980426781428295201913)
                    ·
                      rfl

theorem cell23_4516122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 2, 5].length) (baseStart_4516122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516122 prefixEnd_4516122 := by exact prefixLift 4516122
  have htrace : WordTrace (prefixWord ++ tailWord_4516122) baseStart_4516122 baseEnd_4516122 := by
    simpa [prefixWord, tailWord_4516122, baseEnd_4516122] using wordTrace_append hprefix tailTrace_4516122
  have hstable : (prefixWord ++ tailWord_4516122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516122).length < 2 ^ (prefixWord ++ tailWord_4516122).sum := by decide
  have hdescent : baseEnd_4516122 < baseStart_4516122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516195 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 5, 5]
def baseStart_4516195 : Nat := 118140960795 + 4516195 * 2 ^ 59
def prefixEnd_4516195 : Nat := 4983230072969 + 3 ^ 40 * 4516195 * 2
def baseEnd_4516195 : Nat := 772992921477354366664301

theorem tailTrace_4516195 : CollatzResearch.WordTrace tailWord_4516195 prefixEnd_4516195 772992921477354366664301 := by
  unfold tailWord_4516195
  simp only [CollatzResearch.WordTrace]
  refine ⟨164719163873604294544406039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109812775915736196362937359 164719163873604294544406039)
  ·
    refine ⟨247078745810406441816609059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164719163873604294544406039 247078745810406441816609059)
    ·
      refine ⟨370618118715609662724913589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247078745810406441816609059 370618118715609662724913589)
      ·
        refine ⟨34745448629588405880460649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 370618118715609662724913589 34745448629588405880460649)
        ·
          refine ⟨26059086472191304410345487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34745448629588405880460649 26059086472191304410345487)
          ·
            refine ⟨39088629708286956615518231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26059086472191304410345487 39088629708286956615518231)
            ·
              refine ⟨58632944562430434923277347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39088629708286956615518231 58632944562430434923277347)
              ·
                refine ⟨87949416843645652384916021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58632944562430434923277347 87949416843645652384916021)
                ·
                  refine ⟨8245257829091779911085877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87949416843645652384916021 8245257829091779911085877)
                  ·
                    refine ⟨772992921477354366664301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8245257829091779911085877 772992921477354366664301)
                    ·
                      rfl

theorem cell23_4516195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 5].length) (baseStart_4516195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516195 prefixEnd_4516195 := by exact prefixLift 4516195
  have htrace : WordTrace (prefixWord ++ tailWord_4516195) baseStart_4516195 baseEnd_4516195 := by
    simpa [prefixWord, tailWord_4516195, baseEnd_4516195] using wordTrace_append hprefix tailTrace_4516195
  have hstable : (prefixWord ++ tailWord_4516195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516195).length < 2 ^ (prefixWord ++ tailWord_4516195).sum := by decide
  have hdescent : baseEnd_4516195 < baseStart_4516195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516205 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_4516205 : Nat := 118140960795 + 4516205 * 2 ^ 59
def prefixEnd_4516205 : Nat := 4983230072969 + 3 ^ 40 * 4516205 * 2
def baseEnd_4516205 : Nat := 2318983899238608060867857

theorem tailTrace_4516205 : CollatzResearch.WordTrace tailWord_4516205 prefixEnd_4516205 2318983899238608060867857 := by
  unfold tailWord_4516205
  simp only [CollatzResearch.WordTrace]
  refine ⟨164719528603568066252270069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109813019069045377501513379 164719528603568066252270069)
  ·
    refine ⟨15442455806584506211150319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 164719528603568066252270069 15442455806584506211150319)
    ·
      refine ⟨23163683709876759316725479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15442455806584506211150319 23163683709876759316725479)
      ·
        refine ⟨34745525564815138975088219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23163683709876759316725479 34745525564815138975088219)
        ·
          refine ⟨52118288347222708462632329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34745525564815138975088219 52118288347222708462632329)
          ·
            refine ⟨39088716260417031346974247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52118288347222708462632329 39088716260417031346974247)
            ·
              refine ⟨58633074390625547020461371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39088716260417031346974247 58633074390625547020461371)
              ·
                refine ⟨87949611585938320530692057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58633074390625547020461371 87949611585938320530692057)
                ·
                  refine ⟨65962208689453740398019043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87949611585938320530692057 65962208689453740398019043)
                  ·
                    refine ⟨98943313034180610597028565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65962208689453740398019043 98943313034180610597028565)
                    ·
                      refine ⟨2318983899238608060867857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98943313034180610597028565 2318983899238608060867857)
                      ·
                        rfl

theorem cell23_4516205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_4516205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516205 prefixEnd_4516205 := by exact prefixLift 4516205
  have htrace : WordTrace (prefixWord ++ tailWord_4516205) baseStart_4516205 baseEnd_4516205 := by
    simpa [prefixWord, tailWord_4516205, baseEnd_4516205] using wordTrace_append hprefix tailTrace_4516205
  have hstable : (prefixWord ++ tailWord_4516205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516205).length < 2 ^ (prefixWord ++ tailWord_4516205).sum := by decide
  have hdescent : baseEnd_4516205 < baseStart_4516205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516219 : List Nat := [1, 1, 1, 1, 1, 7, 3, 1, 2, 3, 2]
def baseStart_4516219 : Nat := 118140960795 + 4516219 * 2 ^ 59
def prefixEnd_4516219 : Nat := 4983230072969 + 3 ^ 40 * 4516219 * 2
def baseEnd_4516219 : Nat := 2318991087967771006092793

theorem tailTrace_4516219 : CollatzResearch.WordTrace tailWord_4516219 prefixEnd_4516219 2318991087967771006092793 := by
  unfold tailWord_4516219
  simp only [CollatzResearch.WordTrace]
  refine ⟨164720039225517346643279711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109813359483678231095519807 164720039225517346643279711)
  ·
    refine ⟨247080058838276019964919567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164720039225517346643279711 247080058838276019964919567)
    ·
      refine ⟨370620088257414029947379351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247080058838276019964919567 370620088257414029947379351)
      ·
        refine ⟨555930132386121044921069027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370620088257414029947379351 555930132386121044921069027)
        ·
          refine ⟨833895198579181567381603541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 555930132386121044921069027 833895198579181567381603541)
          ·
            refine ⟨19544418716699567985506333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 833895198579181567381603541 19544418716699567985506333)
            ·
              refine ⟨7329157018762337994564875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19544418716699567985506333 7329157018762337994564875)
              ·
                refine ⟨10993735528143506991847313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7329157018762337994564875 10993735528143506991847313)
                ·
                  refine ⟨8245301646107630243885485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10993735528143506991847313 8245301646107630243885485)
                  ·
                    refine ⟨3091988117290361341457057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8245301646107630243885485 3091988117290361341457057)
                    ·
                      refine ⟨2318991087967771006092793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3091988117290361341457057 2318991087967771006092793)
                      ·
                        rfl

theorem cell23_4516219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 3, 2].length) (baseStart_4516219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516219 prefixEnd_4516219 := by exact prefixLift 4516219
  have htrace : WordTrace (prefixWord ++ tailWord_4516219) baseStart_4516219 baseEnd_4516219 := by
    simpa [prefixWord, tailWord_4516219, baseEnd_4516219] using wordTrace_append hprefix tailTrace_4516219
  have hstable : (prefixWord ++ tailWord_4516219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516219).length < 2 ^ (prefixWord ++ tailWord_4516219).sum := by decide
  have hdescent : baseEnd_4516219 < baseStart_4516219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516245 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 1, 1, 6]
def baseStart_4516245 : Nat := 118140960795 + 4516245 * 2 ^ 59
def prefixEnd_4516245 : Nat := 4983230072969 + 3 ^ 40 * 4516245 * 2
def baseEnd_4516245 : Nat := 2319004438464787904367673

theorem tailTrace_4516245 : CollatzResearch.WordTrace tailWord_4516245 prefixEnd_4516245 2319004438464787904367673 := by
  unfold tailWord_4516245
  simp only [CollatzResearch.WordTrace]
  refine ⟨164720987523423153083726189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109813991682282102055817459 164720987523423153083726189)
  ·
    refine ⟨61770370321283682406397321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164720987523423153083726189 61770370321283682406397321)
    ·
      refine ⟨46327777740962761804797991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61770370321283682406397321 46327777740962761804797991)
      ·
        refine ⟨69491666611444142707196987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46327777740962761804797991 69491666611444142707196987)
        ·
          refine ⟨104237499917166214060795481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69491666611444142707196987 104237499917166214060795481)
          ·
            refine ⟨78178124937874660545596611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104237499917166214060795481 78178124937874660545596611)
            ·
              refine ⟨117267187406811990818394917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78178124937874660545596611 117267187406811990818394917)
              ·
                refine ⟨21987597638777248278449047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117267187406811990818394917 21987597638777248278449047)
                ·
                  refine ⟨32981396458165872417673571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21987597638777248278449047 32981396458165872417673571)
                  ·
                    refine ⟨49472094687248808626510357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32981396458165872417673571 49472094687248808626510357)
                    ·
                      refine ⟨2319004438464787904367673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49472094687248808626510357 2319004438464787904367673)
                      ·
                        rfl

theorem cell23_4516245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_4516245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516245 prefixEnd_4516245 := by exact prefixLift 4516245
  have htrace : WordTrace (prefixWord ++ tailWord_4516245) baseStart_4516245 baseEnd_4516245 := by
    simpa [prefixWord, tailWord_4516245, baseEnd_4516245] using wordTrace_append hprefix tailTrace_4516245
  have hstable : (prefixWord ++ tailWord_4516245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516245).length < 2 ^ (prefixWord ++ tailWord_4516245).sum := by decide
  have hdescent : baseEnd_4516245 < baseStart_4516245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516255 : List Nat := [1, 1, 2, 5, 1, 1, 2, 10]
def baseStart_4516255 : Nat := 118140960795 + 4516255 * 2 ^ 59
def prefixEnd_4516255 : Nat := 4983230072969 + 3 ^ 40 * 4516255 * 2
def baseEnd_4516255 : Nat := 85889243454493809823801

theorem tailTrace_4516255 : CollatzResearch.WordTrace tailWord_4516255 prefixEnd_4516255 85889243454493809823801 := by
  unfold tailWord_4516255
  simp only [CollatzResearch.WordTrace]
  refine ⟨164721352253386924791590219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109814234835591283194393479 164721352253386924791590219)
  ·
    refine ⟨247082028380080387187385329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164721352253386924791590219 247082028380080387187385329)
    ·
      refine ⟨185311521285060290390538997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247082028380080387187385329 185311521285060290390538997)
      ·
        refine ⟨17372955120474402224113031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 185311521285060290390538997 17372955120474402224113031)
        ·
          refine ⟨26059432680711603336169547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17372955120474402224113031 26059432680711603336169547)
          ·
            refine ⟨39089149021067405004254321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26059432680711603336169547 39089149021067405004254321)
            ·
              refine ⟨29316861765800553753190741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39089149021067405004254321 29316861765800553753190741)
              ·
                refine ⟨85889243454493809823801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29316861765800553753190741 85889243454493809823801)
                ·
                  rfl

theorem cell23_4516255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 10].length) (baseStart_4516255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516255 prefixEnd_4516255 := by exact prefixLift 4516255
  have htrace : WordTrace (prefixWord ++ tailWord_4516255) baseStart_4516255 baseEnd_4516255 := by
    simpa [prefixWord, tailWord_4516255, baseEnd_4516255] using wordTrace_append hprefix tailTrace_4516255
  have hstable : (prefixWord ++ tailWord_4516255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516255).length < 2 ^ (prefixWord ++ tailWord_4516255).sum := by decide
  have hdescent : baseEnd_4516255 < baseStart_4516255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516282 : List Nat := [3, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3]
def baseStart_4516282 : Nat := 118140960795 + 4516282 * 2 ^ 59
def prefixEnd_4516282 : Nat := 4983230072969 + 3 ^ 40 * 4516282 * 2
def baseEnd_4516282 : Nat := 2319023437249004259605003

theorem tailTrace_4516282 : CollatzResearch.WordTrace tailWord_4516282 prefixEnd_4516282 2319023437249004259605003 := by
  unfold tailWord_4516282
  simp only [CollatzResearch.WordTrace]
  refine ⟨41180584256072277100705775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109814891349526072268548733 41180584256072277100705775)
  ·
    refine ⟨61770876384108415651058663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41180584256072277100705775 61770876384108415651058663)
    ·
      refine ⟨92656314576162623476587995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61770876384108415651058663 92656314576162623476587995)
      ·
        refine ⟨138984471864243935214881993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92656314576162623476587995 138984471864243935214881993)
        ·
          refine ⟨104238353898182951411161495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138984471864243935214881993 104238353898182951411161495)
          ·
            refine ⟨156357530847274427116742243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104238353898182951411161495 156357530847274427116742243)
            ·
              refine ⟨234536296270911640675113365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156357530847274427116742243 234536296270911640675113365)
              ·
                refine ⟨10993888887698983156645939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 234536296270911640675113365 10993888887698983156645939)
                ·
                  refine ⟨16490833331548474734968909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10993888887698983156645939 16490833331548474734968909)
                  ·
                    refine ⟨6184062499330678025613341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16490833331548474734968909 6184062499330678025613341)
                    ·
                      refine ⟨2319023437249004259605003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6184062499330678025613341 2319023437249004259605003)
                      ·
                        rfl

theorem cell23_4516282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3].length) (baseStart_4516282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516282 prefixEnd_4516282 := by exact prefixLift 4516282
  have htrace : WordTrace (prefixWord ++ tailWord_4516282) baseStart_4516282 baseEnd_4516282 := by
    simpa [prefixWord, tailWord_4516282, baseEnd_4516282] using wordTrace_append hprefix tailTrace_4516282
  have hstable : (prefixWord ++ tailWord_4516282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516282).length < 2 ^ (prefixWord ++ tailWord_4516282).sum := by decide
  have hdescent : baseEnd_4516282 < baseStart_4516282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516299 : List Nat := [1, 1, 1, 1, 3, 3, 1, 6, 2, 1, 3]
def baseStart_4516299 : Nat := 118140960795 + 4516299 * 2 ^ 59
def prefixEnd_4516299 : Nat := 4983230072969 + 3 ^ 40 * 4516299 * 2
def baseEnd_4516299 : Nat := 2319032166420130693092425

theorem tailTrace_4516299 : CollatzResearch.WordTrace tailWord_4516299 prefixEnd_4516299 2319032166420130693092425 := by
  unfold tailWord_4516299
  simp only [CollatzResearch.WordTrace]
  refine ⟨164722957065227520306191951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109815304710151680204127967 164722957065227520306191951)
  ·
    refine ⟨247084435597841280459287927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164722957065227520306191951 247084435597841280459287927)
    ·
      refine ⟨370626653396761920688931891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247084435597841280459287927 370626653396761920688931891)
      ·
        refine ⟨555939980095142881033397837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370626653396761920688931891 555939980095142881033397837)
        ·
          refine ⟨208477492535678580387524189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 555939980095142881033397837 208477492535678580387524189)
          ·
            refine ⟨78179059700879467645321571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208477492535678580387524189 78179059700879467645321571)
            ·
              refine ⟨117268589551319201467982357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78179059700879467645321571 117268589551319201467982357)
              ·
                refine ⟨5496965135218087568811673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 117268589551319201467982357 5496965135218087568811673)
                ·
                  refine ⟨4122723851413565676608755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5496965135218087568811673 4122723851413565676608755)
                  ·
                    refine ⟨6184085777120348514913133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4122723851413565676608755 6184085777120348514913133)
                    ·
                      refine ⟨2319032166420130693092425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6184085777120348514913133 2319032166420130693092425)
                      ·
                        rfl

theorem cell23_4516299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 1, 3].length) (baseStart_4516299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516299 prefixEnd_4516299 := by exact prefixLift 4516299
  have htrace : WordTrace (prefixWord ++ tailWord_4516299) baseStart_4516299 baseEnd_4516299 := by
    simpa [prefixWord, tailWord_4516299, baseEnd_4516299] using wordTrace_append hprefix tailTrace_4516299
  have hstable : (prefixWord ++ tailWord_4516299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516299).length < 2 ^ (prefixWord ++ tailWord_4516299).sum := by decide
  have hdescent : baseEnd_4516299 < baseStart_4516299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516300 : List Nat := [2, 2, 1, 4, 4, 1, 1, 1, 3, 2, 2]
def baseStart_4516300 : Nat := 118140960795 + 4516300 * 2 ^ 59
def prefixEnd_4516300 : Nat := 4983230072969 + 3 ^ 40 * 4516300 * 2
def baseEnd_4516300 : Nat := 2319032679900785189179921

theorem tailTrace_4516300 : CollatzResearch.WordTrace tailWord_4516300 prefixEnd_4516300 2319032679900785189179921 := by
  unfold tailWord_4516300
  simp only [CollatzResearch.WordTrace]
  refine ⟨82361496769111948738489177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109815329025482598317985569 82361496769111948738489177)
  ·
    refine ⟨61771122576833961553866883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82361496769111948738489177 61771122576833961553866883)
    ·
      refine ⟨92656683865250942330800325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61771122576833961553866883 92656683865250942330800325)
      ·
        refine ⟨17373128224734551687025061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92656683865250942330800325 17373128224734551687025061)
        ·
          refine ⟨3257461542137728441317199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17373128224734551687025061 3257461542137728441317199)
          ·
            refine ⟨4886192313206592661975799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3257461542137728441317199 4886192313206592661975799)
            ·
              refine ⟨7329288469809888992963699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4886192313206592661975799 7329288469809888992963699)
              ·
                refine ⟨10993932704714833489445549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7329288469809888992963699 10993932704714833489445549)
                ·
                  refine ⟨4122724764268062558542081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10993932704714833489445549 4122724764268062558542081)
                  ·
                    refine ⟨3092043573201046918906561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4122724764268062558542081 3092043573201046918906561)
                    ·
                      refine ⟨2319032679900785189179921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3092043573201046918906561 2319032679900785189179921)
                      ·
                        rfl

theorem cell23_4516300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_4516300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516300 prefixEnd_4516300 := by exact prefixLift 4516300
  have htrace : WordTrace (prefixWord ++ tailWord_4516300) baseStart_4516300 baseEnd_4516300 := by
    simpa [prefixWord, tailWord_4516300, baseEnd_4516300] using wordTrace_append hprefix tailTrace_4516300
  have hstable : (prefixWord ++ tailWord_4516300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516300).length < 2 ^ (prefixWord ++ tailWord_4516300).sum := by decide
  have hdescent : baseEnd_4516300 < baseStart_4516300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516339 : List Nat := [1, 1, 1, 2, 2, 2, 5, 2, 1, 4, 2]
def baseStart_4516339 : Nat := 118140960795 + 4516339 * 2 ^ 59
def prefixEnd_4516339 : Nat := 4983230072969 + 3 ^ 40 * 4516339 * 2
def baseEnd_4516339 : Nat := 2319052705646310536592241

theorem tailTrace_4516339 : CollatzResearch.WordTrace tailWord_4516339 prefixEnd_4516339 2319052705646310536592241 := by
  unfold tailWord_4516339
  simp only [CollatzResearch.WordTrace]
  refine ⟨164724415985082607137648071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109816277323388404758432047 164724415985082607137648071)
  ·
    refine ⟨247086623977623910706472107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164724415985082607137648071 247086623977623910706472107)
    ·
      refine ⟨370629935966435866059708161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247086623977623910706472107 370629935966435866059708161)
      ·
        refine ⟨277972451974826899544781121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 370629935966435866059708161 277972451974826899544781121)
        ·
          refine ⟨208479338981120174658585841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277972451974826899544781121 208479338981120174658585841)
          ·
            refine ⟨156359504235840130993939381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208479338981120174658585841 156359504235840130993939381)
            ·
              refine ⟨14658703522110012280681817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 156359504235840130993939381 14658703522110012280681817)
              ·
                refine ⟨10994027641582509210511363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14658703522110012280681817 10994027641582509210511363)
                ·
                  refine ⟨16491041462373763815767045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10994027641582509210511363 16491041462373763815767045)
                  ·
                    refine ⟨3092070274195080715456321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16491041462373763815767045 3092070274195080715456321)
                    ·
                      refine ⟨2319052705646310536592241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3092070274195080715456321 2319052705646310536592241)
                      ·
                        rfl

theorem cell23_4516339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 4, 2].length) (baseStart_4516339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516339 prefixEnd_4516339 := by exact prefixLift 4516339
  have htrace : WordTrace (prefixWord ++ tailWord_4516339) baseStart_4516339 baseEnd_4516339 := by
    simpa [prefixWord, tailWord_4516339, baseEnd_4516339] using wordTrace_append hprefix tailTrace_4516339
  have hstable : (prefixWord ++ tailWord_4516339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516339).length < 2 ^ (prefixWord ++ tailWord_4516339).sum := by decide
  have hdescent : baseEnd_4516339 < baseStart_4516339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516362 : List Nat := [3, 1, 2, 2, 2, 1, 2, 3, 7]
def baseStart_4516362 : Nat := 118140960795 + 4516362 * 2 ^ 59
def prefixEnd_4516362 : Nat := 4983230072969 + 3 ^ 40 * 4516362 * 2
def baseEnd_4516362 : Nat := 257673835077929327400515

theorem tailTrace_4516362 : CollatzResearch.WordTrace tailWord_4516362 prefixEnd_4516362 257673835077929327400515 := by
  unfold tailWord_4516362
  simp only [CollatzResearch.WordTrace]
  refine ⟨41181313715999820516433835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109816836575999521377156893 41181313715999820516433835)
  ·
    refine ⟨61771970573999730774650753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41181313715999820516433835 61771970573999730774650753)
    ·
      refine ⟨46328977930499798080988065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61771970573999730774650753 46328977930499798080988065)
      ·
        refine ⟨34746733447874848560741049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46328977930499798080988065 34746733447874848560741049)
        ·
          refine ⟨26060050085906136420555787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34746733447874848560741049 26060050085906136420555787)
          ·
            refine ⟨39090075128859204630833681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26060050085906136420555787 39090075128859204630833681)
            ·
              refine ⟨29317556346644403473125261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39090075128859204630833681 29317556346644403473125261)
              ·
                refine ⟨10994083629991651302421973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29317556346644403473125261 10994083629991651302421973)
                ·
                  refine ⟨257673835077929327400515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10994083629991651302421973 257673835077929327400515)
                  ·
                    rfl

theorem cell23_4516362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 7].length) (baseStart_4516362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516362 prefixEnd_4516362 := by exact prefixLift 4516362
  have htrace : WordTrace (prefixWord ++ tailWord_4516362) baseStart_4516362 baseEnd_4516362 := by
    simpa [prefixWord, tailWord_4516362, baseEnd_4516362] using wordTrace_append hprefix tailTrace_4516362
  have hstable : (prefixWord ++ tailWord_4516362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516362).length < 2 ^ (prefixWord ++ tailWord_4516362).sum := by decide
  have hdescent : baseEnd_4516362 < baseStart_4516362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516402 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5]
def baseStart_4516402 : Nat := 118140960795 + 4516402 * 2 ^ 59
def prefixEnd_4516402 : Nat := 4983230072969 + 3 ^ 40 * 4516402 * 2
def baseEnd_4516402 : Nat := 2319085054927543790104451

theorem tailTrace_4516402 : CollatzResearch.WordTrace tailWord_4516402 prefixEnd_4516402 2319085054927543790104451 := by
  unfold tailWord_4516402
  simp only [CollatzResearch.WordTrace]
  refine ⟨41181678445963592224297865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109817809189236245931460973 41181678445963592224297865)
  ·
    refine ⟨30886258834472694168223399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41181678445963592224297865 30886258834472694168223399)
    ·
      refine ⟨46329388251709041252335099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30886258834472694168223399 46329388251709041252335099)
      ·
        refine ⟨69494082377563561878502649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46329388251709041252335099 69494082377563561878502649)
        ·
          refine ⟨52120561783172671408876987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69494082377563561878502649 52120561783172671408876987)
          ·
            refine ⟨78180842674759007113315481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52120561783172671408876987 78180842674759007113315481)
            ·
              refine ⟨58635632006069255334986611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78180842674759007113315481 58635632006069255334986611)
              ·
                refine ⟨87953448009103883002479917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58635632006069255334986611 87953448009103883002479917)
                ·
                  refine ⟨32982543003413956125929969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87953448009103883002479917 32982543003413956125929969)
                  ·
                    refine ⟨24736907252560467094447477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32982543003413956125929969 24736907252560467094447477)
                    ·
                      refine ⟨2319085054927543790104451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24736907252560467094447477 2319085054927543790104451)
                      ·
                        rfl

theorem cell23_4516402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_4516402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516402 prefixEnd_4516402 := by exact prefixLift 4516402
  have htrace : WordTrace (prefixWord ++ tailWord_4516402) baseStart_4516402 baseEnd_4516402 := by
    simpa [prefixWord, tailWord_4516402, baseEnd_4516402] using wordTrace_append hprefix tailTrace_4516402
  have hstable : (prefixWord ++ tailWord_4516402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516402).length < 2 ^ (prefixWord ++ tailWord_4516402).sum := by decide
  have hdescent : baseEnd_4516402 < baseStart_4516402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516406 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_4516406 : Nat := 118140960795 + 4516406 * 2 ^ 59
def prefixEnd_4516406 : Nat := 4983230072969 + 3 ^ 40 * 4516406 * 2
def baseEnd_4516406 : Nat := 2319087108850161774454433

theorem tailTrace_4516406 : CollatzResearch.WordTrace tailWord_4516406 prefixEnd_4516406 2319087108850161774454433 := by
  unfold tailWord_4516406
  simp only [CollatzResearch.WordTrace]
  refine ⟨10295428729739992348771067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109817906450559918386891381 10295428729739992348771067)
  ·
    refine ⟨15443143094609988523156601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10295428729739992348771067 15443143094609988523156601)
    ·
      refine ⟨11582357320957491392367451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15443143094609988523156601 11582357320957491392367451)
      ·
        refine ⟨17373535981436237088551177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11582357320957491392367451 17373535981436237088551177)
        ·
          refine ⟨13030151986077177816413383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17373535981436237088551177 13030151986077177816413383)
          ·
            refine ⟨19545227979115766724620075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13030151986077177816413383 19545227979115766724620075)
            ·
              refine ⟨29317841968673650086930113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19545227979115766724620075 29317841968673650086930113)
              ·
                refine ⟨21988381476505237565197585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29317841968673650086930113 21988381476505237565197585)
                ·
                  refine ⟨16491286107378928173898189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21988381476505237565197585 16491286107378928173898189)
                  ·
                    refine ⟨6184232290267098065211821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16491286107378928173898189 6184232290267098065211821)
                    ·
                      refine ⟨2319087108850161774454433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6184232290267098065211821 2319087108850161774454433)
                      ·
                        rfl

theorem cell23_4516406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_4516406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516406 prefixEnd_4516406 := by exact prefixLift 4516406
  have htrace : WordTrace (prefixWord ++ tailWord_4516406) baseStart_4516406 baseEnd_4516406 := by
    simpa [prefixWord, tailWord_4516406, baseEnd_4516406] using wordTrace_append hprefix tailTrace_4516406
  have hstable : (prefixWord ++ tailWord_4516406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516406).length < 2 ^ (prefixWord ++ tailWord_4516406).sum := by decide
  have hdescent : baseEnd_4516406 < baseStart_4516406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516439 : List Nat := [1, 1, 3, 2, 2, 2, 1, 4, 3, 4]
def baseStart_4516439 : Nat := 118140960795 + 4516439 * 2 ^ 59
def prefixEnd_4516439 : Nat := 4983230072969 + 3 ^ 40 * 4516439 * 2
def baseEnd_4516439 : Nat := 773034684570586715113927

theorem tailTrace_4516439 : CollatzResearch.WordTrace tailWord_4516439 prefixEnd_4516439 773034684570586715113927 := by
  unfold tailWord_4516439
  simp only [CollatzResearch.WordTrace]
  refine ⟨164728063284720324216288371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109818708856480216144192247 164728063284720324216288371)
  ·
    refine ⟨247092094927080486324432557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164728063284720324216288371 247092094927080486324432557)
    ·
      refine ⟨92659535597655182371662209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247092094927080486324432557 92659535597655182371662209)
      ·
        refine ⟨69494651698241386778746657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92659535597655182371662209 69494651698241386778746657)
        ·
          refine ⟨52120988773681040084059993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69494651698241386778746657 52120988773681040084059993)
          ·
            refine ⟨39090741580260780063044995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52120988773681040084059993 39090741580260780063044995)
            ·
              refine ⟨58636112370391170094567493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39090741580260780063044995 58636112370391170094567493)
              ·
                refine ⟨10994271069448344392731405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58636112370391170094567493 10994271069448344392731405)
                ·
                  refine ⟨4122851651043129147274277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10994271069448344392731405 4122851651043129147274277)
                  ·
                    refine ⟨773034684570586715113927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4122851651043129147274277 773034684570586715113927)
                    ·
                      rfl

theorem cell23_4516439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 4].length) (baseStart_4516439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516439 prefixEnd_4516439 := by exact prefixLift 4516439
  have htrace : WordTrace (prefixWord ++ tailWord_4516439) baseStart_4516439 baseEnd_4516439 := by
    simpa [prefixWord, tailWord_4516439, baseEnd_4516439] using wordTrace_append hprefix tailTrace_4516439
  have hstable : (prefixWord ++ tailWord_4516439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516439).length < 2 ^ (prefixWord ++ tailWord_4516439).sum := by decide
  have hdescent : baseEnd_4516439 < baseStart_4516439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516449 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 1, 4, 3]
def baseStart_4516449 : Nat := 118140960795 + 4516449 * 2 ^ 59
def prefixEnd_4516449 : Nat := 4983230072969 + 3 ^ 40 * 4516449 * 2
def baseEnd_4516449 : Nat := 2319109188518305106216735

theorem tailTrace_4516449 : CollatzResearch.WordTrace tailWord_4516449 prefixEnd_4516449 2319109188518305106216735 := by
  unfold tailWord_4516449
  simp only [CollatzResearch.WordTrace]
  refine ⟨164728428014684095924152401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109818952009789397282768267 164728428014684095924152401)
  ·
    refine ⟨123546321011013071943114301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164728428014684095924152401 123546321011013071943114301)
    ·
      refine ⟨46329870379129901978667863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123546321011013071943114301 46329870379129901978667863)
      ·
        refine ⟨69494805568694852968001795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46329870379129901978667863 69494805568694852968001795)
        ·
          refine ⟨104242208353042279452002693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69494805568694852968001795 104242208353042279452002693)
          ·
            refine ⟨19545414066195427397250505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104242208353042279452002693 19545414066195427397250505)
            ·
              refine ⟨14659060549646570547937879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19545414066195427397250505 14659060549646570547937879)
              ·
                refine ⟨21988590824469855821906819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14659060549646570547937879 21988590824469855821906819)
                ·
                  refine ⟨32982886236704783732860229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21988590824469855821906819 32982886236704783732860229)
                  ·
                    refine ⟨6184291169382146949911293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32982886236704783732860229 6184291169382146949911293)
                    ·
                      refine ⟨2319109188518305106216735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6184291169382146949911293 2319109188518305106216735)
                      ·
                        rfl

theorem cell23_4516449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_4516449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516449 prefixEnd_4516449 := by exact prefixLift 4516449
  have htrace : WordTrace (prefixWord ++ tailWord_4516449) baseStart_4516449 baseEnd_4516449 := by
    simpa [prefixWord, tailWord_4516449, baseEnd_4516449] using wordTrace_append hprefix tailTrace_4516449
  have hstable : (prefixWord ++ tailWord_4516449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516449).length < 2 ^ (prefixWord ++ tailWord_4516449).sum := by decide
  have hdescent : baseEnd_4516449 < baseStart_4516449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516452 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 10]
def baseStart_4516452 : Nat := 118140960795 + 4516452 * 2 ^ 59
def prefixEnd_4516452 : Nat := 4983230072969 + 3 ^ 40 * 4516452 * 2
def baseEnd_4516452 : Nat := 257678969884474288275469

theorem tailTrace_4516452 : CollatzResearch.WordTrace tailWord_4516452 prefixEnd_4516452 257678969884474288275469 := by
  unfold tailWord_4516452
  simp only [CollatzResearch.WordTrace]
  refine ⟨82364268716836613718255805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109819024955782151624341073 82364268716836613718255805)
  ·
    refine ⟨30886600768813730144345927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82364268716836613718255805 30886600768813730144345927)
    ·
      refine ⟨46329901153220595216518891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30886600768813730144345927 46329901153220595216518891)
      ·
        refine ⟨69494851729830892824778337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46329901153220595216518891 69494851729830892824778337)
        ·
          refine ⟨52121138797373169618583753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69494851729830892824778337 52121138797373169618583753)
          ·
            refine ⟨39090854098029877213937815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52121138797373169618583753 39090854098029877213937815)
            ·
              refine ⟨58636281147044815820906723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39090854098029877213937815 58636281147044815820906723)
              ·
                refine ⟨87954421720567223731360085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58636281147044815820906723 87954421720567223731360085)
                ·
                  refine ⟨257678969884474288275469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 87954421720567223731360085 257678969884474288275469)
                  ·
                    rfl

theorem cell23_4516452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_4516452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516452 prefixEnd_4516452 := by exact prefixLift 4516452
  have htrace : WordTrace (prefixWord ++ tailWord_4516452) baseStart_4516452 baseEnd_4516452 := by
    simpa [prefixWord, tailWord_4516452, baseEnd_4516452] using wordTrace_append hprefix tailTrace_4516452
  have hstable : (prefixWord ++ tailWord_4516452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516452).length < 2 ^ (prefixWord ++ tailWord_4516452).sum := by decide
  have hdescent : baseEnd_4516452 < baseStart_4516452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516492 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 7]
def baseStart_4516492 : Nat := 118140960795 + 4516492 * 2 ^ 59
def prefixEnd_4516492 : Nat := 4983230072969 + 3 ^ 40 * 4516492 * 2
def baseEnd_4516492 : Nat := 2319131268186448437979037

theorem tailTrace_4516492 : CollatzResearch.WordTrace tailWord_4516492 prefixEnd_4516492 2319131268186448437979037 := by
  unfold tailWord_4516492
  simp only [CollatzResearch.WordTrace]
  refine ⟨82364998176764157133983865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109819997569018876178645153 82364998176764157133983865)
  ·
    refine ⟨61773748632573117850487899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82364998176764157133983865 61773748632573117850487899)
    ·
      refine ⟨92660622948859676775731849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61773748632573117850487899 92660622948859676775731849)
      ·
        refine ⟨69495467211644757581798887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92660622948859676775731849 69495467211644757581798887)
        ·
          refine ⟨104243200817467136372698331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69495467211644757581798887 104243200817467136372698331)
          ·
            refine ⟨156364801226200704559047497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104243200817467136372698331 156364801226200704559047497)
            ·
              refine ⟨117273600919650528419285623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156364801226200704559047497 117273600919650528419285623)
              ·
                refine ⟨175910401379475792628928435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117273600919650528419285623 175910401379475792628928435)
                ·
                  refine ⟨263865602069213688943392653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175910401379475792628928435 263865602069213688943392653)
                  ·
                    refine ⟨98949600775955133353772245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 263865602069213688943392653 98949600775955133353772245)
                    ·
                      refine ⟨2319131268186448437979037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98949600775955133353772245 2319131268186448437979037)
                      ·
                        rfl

theorem cell23_4516492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_4516492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516492 prefixEnd_4516492 := by exact prefixLift 4516492
  have htrace : WordTrace (prefixWord ++ tailWord_4516492) baseStart_4516492 baseEnd_4516492 := by
    simpa [prefixWord, tailWord_4516492, baseEnd_4516492] using wordTrace_append hprefix tailTrace_4516492
  have hstable : (prefixWord ++ tailWord_4516492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516492).length < 2 ^ (prefixWord ++ tailWord_4516492).sum := by decide
  have hdescent : baseEnd_4516492 < baseStart_4516492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516597 : List Nat := [1, 3, 6, 1, 1, 2, 1, 1, 1, 6]
def baseStart_4516597 : Nat := 118140960795 + 4516597 * 2 ^ 59
def prefixEnd_4516597 : Nat := 4983230072969 + 3 ^ 40 * 4516597 * 2
def baseEnd_4516597 : Nat := 773061727885056842388685

theorem tailTrace_4516597 : CollatzResearch.WordTrace tailWord_4516597 prefixEnd_4516597 773061727885056842388685 := by
  unfold tailWord_4516597
  simp only [CollatzResearch.WordTrace]
  refine ⟨164733826018147917200540045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109822550678765278133693363 164733826018147917200540045)
  ·
    refine ⟨61775184756805468950202517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164733826018147917200540045 61775184756805468950202517)
    ·
      refine ⟨2895711785475256357040743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 61775184756805468950202517 2895711785475256357040743)
      ·
        refine ⟨4343567678212884535561115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2895711785475256357040743 4343567678212884535561115)
        ·
          refine ⟨6515351517319326803341673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4343567678212884535561115 6515351517319326803341673)
          ·
            refine ⟨4886513637989495102506255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6515351517319326803341673 4886513637989495102506255)
            ·
              refine ⟨7329770456984242653759383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4886513637989495102506255 7329770456984242653759383)
              ·
                refine ⟨10994655685476363980639075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7329770456984242653759383 10994655685476363980639075)
                ·
                  refine ⟨16491983528214545970958613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10994655685476363980639075 16491983528214545970958613)
                  ·
                    refine ⟨773061727885056842388685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16491983528214545970958613 773061727885056842388685)
                    ·
                      rfl

theorem cell23_4516597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_4516597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516597 prefixEnd_4516597 := by exact prefixLift 4516597
  have htrace : WordTrace (prefixWord ++ tailWord_4516597) baseStart_4516597 baseEnd_4516597 := by
    simpa [prefixWord, tailWord_4516597, baseEnd_4516597] using wordTrace_append hprefix tailTrace_4516597
  have hstable : (prefixWord ++ tailWord_4516597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516597).length < 2 ^ (prefixWord ++ tailWord_4516597).sum := by decide
  have hdescent : baseEnd_4516597 < baseStart_4516597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516654 : List Nat := [4, 1, 3, 2, 1, 3, 2, 1, 2, 1, 3]
def baseStart_4516654 : Nat := 118140960795 + 4516654 * 2 ^ 59
def prefixEnd_4516654 : Nat := 4983230072969 + 3 ^ 40 * 4516654 * 2
def baseEnd_4516654 : Nat := 2319214452052476804153293

theorem tailTrace_4516654 : CollatzResearch.WordTrace tailWord_4516654 prefixEnd_4516654 2319214452052476804153293 := by
  unfold tailWord_4516654
  simp only [CollatzResearch.WordTrace]
  refine ⟨20591988122367676991920627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109823936652627610623576677 20591988122367676991920627)
  ·
    refine ⟨30887982183551515487880941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20591988122367676991920627 30887982183551515487880941)
    ·
      refine ⟨11582993318831818307955353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30887982183551515487880941 11582993318831818307955353)
      ·
        refine ⟨8687244989123863730966515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11582993318831818307955353 8687244989123863730966515)
        ·
          refine ⟨13030867483685795596449773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8687244989123863730966515 13030867483685795596449773)
          ·
            refine ⟨4886575306382173348668665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13030867483685795596449773 4886575306382173348668665)
            ·
              refine ⟨3664931479786630011501499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4886575306382173348668665 3664931479786630011501499)
              ·
                refine ⟨5497397219679945017252249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3664931479786630011501499 5497397219679945017252249)
                ·
                  refine ⟨4123047914759958762939187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5497397219679945017252249 4123047914759958762939187)
                  ·
                    refine ⟨6184571872139938144408781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4123047914759958762939187 6184571872139938144408781)
                    ·
                      refine ⟨2319214452052476804153293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6184571872139938144408781 2319214452052476804153293)
                      ·
                        rfl

theorem cell23_4516654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_4516654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516654 prefixEnd_4516654 := by exact prefixLift 4516654
  have htrace : WordTrace (prefixWord ++ tailWord_4516654) baseStart_4516654 baseEnd_4516654 := by
    simpa [prefixWord, tailWord_4516654, baseEnd_4516654] using wordTrace_append hprefix tailTrace_4516654
  have hstable : (prefixWord ++ tailWord_4516654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516654).length < 2 ^ (prefixWord ++ tailWord_4516654).sum := by decide
  have hdescent : baseEnd_4516654 < baseStart_4516654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516700 : List Nat := [2, 2, 4, 2, 1, 2, 1, 4, 5]
def baseStart_4516700 : Nat := 118140960795 + 4516700 * 2 ^ 59
def prefixEnd_4516700 : Nat := 4983230072969 + 3 ^ 40 * 4516700 * 2
def baseEnd_4516700 : Nat := 257693119129175958242009

theorem tailTrace_4516700 : CollatzResearch.WordTrace tailWord_4516700 prefixEnd_4516700 257693119129175958242009 := by
  unfold tailWord_4516700
  simp only [CollatzResearch.WordTrace]
  refine ⟨82368791368387382895769777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109825055157849843861026369 82368791368387382895769777)
  ·
    refine ⟨61776593526290537171827333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82368791368387382895769777 61776593526290537171827333)
    ·
      refine ⟨11583111286179475719717625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61776593526290537171827333 11583111286179475719717625)
      ·
        refine ⟨8687333464634606789788219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11583111286179475719717625 8687333464634606789788219)
        ·
          refine ⟨13031000196951910184682329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8687333464634606789788219 13031000196951910184682329)
          ·
            refine ⟨9773250147713932638511747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13031000196951910184682329 9773250147713932638511747)
            ·
              refine ⟨14659875221570898957767621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9773250147713932638511747 14659875221570898957767621)
              ·
                refine ⟨2748726604044543554581429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14659875221570898957767621 2748726604044543554581429)
                ·
                  refine ⟨257693119129175958242009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2748726604044543554581429 257693119129175958242009)
                  ·
                    rfl

theorem cell23_4516700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 5].length) (baseStart_4516700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516700 prefixEnd_4516700 := by exact prefixLift 4516700
  have htrace : WordTrace (prefixWord ++ tailWord_4516700) baseStart_4516700 baseEnd_4516700 := by
    simpa [prefixWord, tailWord_4516700, baseEnd_4516700] using wordTrace_append hprefix tailTrace_4516700
  have hstable : (prefixWord ++ tailWord_4516700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516700).length < 2 ^ (prefixWord ++ tailWord_4516700).sum := by decide
  have hdescent : baseEnd_4516700 < baseStart_4516700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516716 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 4]
def baseStart_4516716 : Nat := 118140960795 + 4516716 * 2 ^ 59
def prefixEnd_4516716 : Nat := 4983230072969 + 3 ^ 40 * 4516716 * 2
def baseEnd_4516716 : Nat := 2319246287853055561578007

theorem tailTrace_4516716 : CollatzResearch.WordTrace tailWord_4516716 prefixEnd_4516716 2319246287853055561578007 := by
  unfold tailWord_4516716
  simp only [CollatzResearch.WordTrace]
  refine ⟨82369083152358400262061001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109825444203144533682748001 82369083152358400262061001)
  ·
    refine ⟨61776812364268800196545751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82369083152358400262061001 61776812364268800196545751)
    ·
      refine ⟨92665218546403200294818627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61776812364268800196545751 92665218546403200294818627)
      ·
        refine ⟨138997827819604800442227941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92665218546403200294818627 138997827819604800442227941)
        ·
          refine ⟨26062092716175900082917739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138997827819604800442227941 26062092716175900082917739)
          ·
            refine ⟨39093139074263850124376609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26062092716175900082917739 39093139074263850124376609)
            ·
              refine ⟨29319854305697887593282457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39093139074263850124376609 29319854305697887593282457)
              ·
                refine ⟨21989890729273415694961843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29319854305697887593282457 21989890729273415694961843)
                ·
                  refine ⟨32984836093910123542442765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21989890729273415694961843 32984836093910123542442765)
                  ·
                    refine ⟨12369313535216296328416037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32984836093910123542442765 12369313535216296328416037)
                    ·
                      refine ⟨2319246287853055561578007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12369313535216296328416037 2319246287853055561578007)
                      ·
                        rfl

theorem cell23_4516716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_4516716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516716 prefixEnd_4516716 := by exact prefixLift 4516716
  have htrace : WordTrace (prefixWord ++ tailWord_4516716) baseStart_4516716 baseEnd_4516716 := by
    simpa [prefixWord, tailWord_4516716, baseEnd_4516716] using wordTrace_append hprefix tailTrace_4516716
  have hstable : (prefixWord ++ tailWord_4516716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516716).length < 2 ^ (prefixWord ++ tailWord_4516716).sum := by decide
  have hdescent : baseEnd_4516716 < baseStart_4516716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516733 : List Nat := [1, 4, 1, 1, 2, 1, 5, 1, 2, 1, 4]
def baseStart_4516733 : Nat := 118140960795 + 4516733 * 2 ^ 59
def prefixEnd_4516733 : Nat := 4983230072969 + 3 ^ 40 * 4516733 * 2
def baseEnd_4516733 : Nat := 2319255017024181995065429

theorem tailTrace_4516733 : CollatzResearch.WordTrace tailWord_4516733 prefixEnd_4516733 2319255017024181995065429 := by
  unfold tailWord_4516733
  simp only [CollatzResearch.WordTrace]
  refine ⟨164738786345655212427490853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109825857563770141618327235 164738786345655212427490853)
  ·
    refine ⟨30888522439810352330154535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164738786345655212427490853 30888522439810352330154535)
    ·
      refine ⟨46332783659715528495231803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30888522439810352330154535 46332783659715528495231803)
      ·
        refine ⟨69499175489573292742847705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46332783659715528495231803 69499175489573292742847705)
        ·
          refine ⟨52124381617179969557135779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69499175489573292742847705 52124381617179969557135779)
          ·
            refine ⟨78186572425769954335703669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52124381617179969557135779 78186572425769954335703669)
            ·
              refine ⟨7329991164915933218972219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78186572425769954335703669 7329991164915933218972219)
              ·
                refine ⟨10994986747373899828458329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7329991164915933218972219 10994986747373899828458329)
                ·
                  refine ⟨8246240060530424871343747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10994986747373899828458329 8246240060530424871343747)
                  ·
                    refine ⟨12369360090795637307015621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8246240060530424871343747 12369360090795637307015621)
                    ·
                      refine ⟨2319255017024181995065429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12369360090795637307015621 2319255017024181995065429)
                      ·
                        rfl

theorem cell23_4516733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_4516733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516733 prefixEnd_4516733 := by exact prefixLift 4516733
  have htrace : WordTrace (prefixWord ++ tailWord_4516733) baseStart_4516733 baseEnd_4516733 := by
    simpa [prefixWord, tailWord_4516733, baseEnd_4516733] using wordTrace_append hprefix tailTrace_4516733
  have hstable : (prefixWord ++ tailWord_4516733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516733).length < 2 ^ (prefixWord ++ tailWord_4516733).sum := by decide
  have hdescent : baseEnd_4516733 < baseStart_4516733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516783 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 5, 1, 3]
def baseStart_4516783 : Nat := 118140960795 + 4516783 * 2 ^ 59
def prefixEnd_4516783 : Nat := 4983230072969 + 3 ^ 40 * 4516783 * 2
def baseEnd_4516783 : Nat := 2319280691056906799440199

theorem tailTrace_4516783 : CollatzResearch.WordTrace tailWord_4516783 prefixEnd_4516783 2319280691056906799440199 := by
  unfold tailWord_4516783
  simp only [CollatzResearch.WordTrace]
  refine ⟨164740609995474070966811003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109827073330316047311207335 164740609995474070966811003)
  ·
    refine ⟨247110914993211106450216505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164740609995474070966811003 247110914993211106450216505)
    ·
      refine ⟨185333186244908329837662379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247110914993211106450216505 185333186244908329837662379)
      ·
        refine ⟨277999779367362494756493569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185333186244908329837662379 277999779367362494756493569)
        ·
          refine ⟨208499834525521871067370177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277999779367362494756493569 208499834525521871067370177)
          ·
            refine ⟨156374875894141403300527633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208499834525521871067370177 156374875894141403300527633)
            ·
              refine ⟨117281156920606052475395725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156374875894141403300527633 117281156920606052475395725)
              ·
                refine ⟨43980433845227269678273397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117281156920606052475395725 43980433845227269678273397)
                ·
                  refine ⟨4123165672990056532338131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43980433845227269678273397 4123165672990056532338131)
                  ·
                    refine ⟨6184748509485084798507197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4123165672990056532338131 6184748509485084798507197)
                    ·
                      refine ⟨2319280691056906799440199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6184748509485084798507197 2319280691056906799440199)
                      ·
                        rfl

theorem cell23_4516783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 1, 3].length) (baseStart_4516783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516783 prefixEnd_4516783 := by exact prefixLift 4516783
  have htrace : WordTrace (prefixWord ++ tailWord_4516783) baseStart_4516783 baseEnd_4516783 := by
    simpa [prefixWord, tailWord_4516783, baseEnd_4516783] using wordTrace_append hprefix tailTrace_4516783
  have hstable : (prefixWord ++ tailWord_4516783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516783).length < 2 ^ (prefixWord ++ tailWord_4516783).sum := by decide
  have hdescent : baseEnd_4516783 < baseStart_4516783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516823 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 2, 6, 2]
def baseStart_4516823 : Nat := 118140960795 + 4516823 * 2 ^ 59
def prefixEnd_4516823 : Nat := 4983230072969 + 3 ^ 40 * 4516823 * 2
def baseEnd_4516823 : Nat := 2319301230283086642940015

theorem tailTrace_4516823 : CollatzResearch.WordTrace tailWord_4516823 prefixEnd_4516823 2319301230283086642940015 := by
  unfold tailWord_4516823
  simp only [CollatzResearch.WordTrace]
  refine ⟨164742068915329157798267123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109828045943552771865511415 164742068915329157798267123)
  ·
    refine ⟨247113103372993736697400685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164742068915329157798267123 247113103372993736697400685)
    ·
      refine ⟨92667413764872651261525257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247113103372993736697400685 92667413764872651261525257)
      ·
        refine ⟨69500560323654488446143943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92667413764872651261525257 69500560323654488446143943)
        ·
          refine ⟨104250840485481732669215915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69500560323654488446143943 104250840485481732669215915)
          ·
            refine ⟨156376260728222599003823873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104250840485481732669215915 156376260728222599003823873)
            ·
              refine ⟨117282195546166949252867905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156376260728222599003823873 117282195546166949252867905)
              ·
                refine ⟨87961646659625211939650929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117282195546166949252867905 87961646659625211939650929)
                ·
                  refine ⟨65971234994718908954738197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87961646659625211939650929 65971234994718908954738197)
                  ·
                    refine ⟨3092401640377448857253353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65971234994718908954738197 3092401640377448857253353)
                    ·
                      refine ⟨2319301230283086642940015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3092401640377448857253353 2319301230283086642940015)
                      ·
                        rfl

theorem cell23_4516823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 6, 2].length) (baseStart_4516823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516823 prefixEnd_4516823 := by exact prefixLift 4516823
  have htrace : WordTrace (prefixWord ++ tailWord_4516823) baseStart_4516823 baseEnd_4516823 := by
    simpa [prefixWord, tailWord_4516823, baseEnd_4516823] using wordTrace_append hprefix tailTrace_4516823
  have hstable : (prefixWord ++ tailWord_4516823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516823).length < 2 ^ (prefixWord ++ tailWord_4516823).sum := by decide
  have hdescent : baseEnd_4516823 < baseStart_4516823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516840 : List Nat := [2, 1, 4, 1, 1, 1, 5, 2, 1, 1, 4]
def baseStart_4516840 : Nat := 118140960795 + 4516840 * 2 ^ 59
def prefixEnd_4516840 : Nat := 4983230072969 + 3 ^ 40 * 4516840 * 2
def baseEnd_4516840 : Nat := 2319309959454213076427437

theorem tailTrace_4516840 : CollatzResearch.WordTrace tailWord_4516840 prefixEnd_4516840 2319309959454213076427437 := by
  unfold tailWord_4516840
  simp only [CollatzResearch.WordTrace]
  refine ⟨82371344478133784850817987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109828459304178379801090649 82371344478133784850817987)
  ·
    refine ⟨123557016717200677276226981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82371344478133784850817987 123557016717200677276226981)
    ·
      refine ⟨23166940634475126989292559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123557016717200677276226981 23166940634475126989292559)
      ·
        refine ⟨34750410951712690483938839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23166940634475126989292559 34750410951712690483938839)
        ·
          refine ⟨52125616427569035725908259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34750410951712690483938839 52125616427569035725908259)
          ·
            refine ⟨78188424641353553588862389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52125616427569035725908259 78188424641353553588862389)
            ·
              refine ⟨7330164810126895648955849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78188424641353553588862389 7330164810126895648955849)
              ·
                refine ⟨5497623607595171736716887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7330164810126895648955849 5497623607595171736716887)
                ·
                  refine ⟨8246435411392757605075331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5497623607595171736716887 8246435411392757605075331)
                  ·
                    refine ⟨12369653117089136407612997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8246435411392757605075331 12369653117089136407612997)
                    ·
                      refine ⟨2319309959454213076427437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12369653117089136407612997 2319309959454213076427437)
                      ·
                        rfl

theorem cell23_4516840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_4516840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516840 prefixEnd_4516840 := by exact prefixLift 4516840
  have htrace : WordTrace (prefixWord ++ tailWord_4516840) baseStart_4516840 baseEnd_4516840 := by
    simpa [prefixWord, tailWord_4516840, baseEnd_4516840] using wordTrace_append hprefix tailTrace_4516840
  have hstable : (prefixWord ++ tailWord_4516840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516840).length < 2 ^ (prefixWord ++ tailWord_4516840).sum := by decide
  have hdescent : baseEnd_4516840 < baseStart_4516840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516860 : List Nat := [2, 2, 2, 1, 2, 5, 1, 1, 1, 1, 5]
def baseStart_4516860 : Nat := 118140960795 + 4516860 * 2 ^ 59
def prefixEnd_4516860 : Nat := 4983230072969 + 3 ^ 40 * 4516860 * 2
def baseEnd_4516860 : Nat := 2319320229067302998177345

theorem tailTrace_4516860 : CollatzResearch.WordTrace tailWord_4516860 prefixEnd_4516860 2319320229067302998177345 := by
  unfold tailWord_4516860
  simp only [CollatzResearch.WordTrace]
  refine ⟨82371709208097556558682017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109828945610796742078242689 82371709208097556558682017)
  ·
    refine ⟨61778781906073167419011513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82371709208097556558682017 61778781906073167419011513)
    ·
      refine ⟨46334086429554875564258635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61778781906073167419011513 46334086429554875564258635)
      ·
        refine ⟨69501129644332313346387953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46334086429554875564258635 69501129644332313346387953)
        ·
          refine ⟨52125847233249235009790965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69501129644332313346387953 52125847233249235009790965)
          ·
            refine ⟨4886798178117115782167903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52125847233249235009790965 4886798178117115782167903)
            ·
              refine ⟨7330197267175673673251855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4886798178117115782167903 7330197267175673673251855)
              ·
                refine ⟨10995295900763510509877783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7330197267175673673251855 10995295900763510509877783)
                ·
                  refine ⟨16492943851145265764816675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10995295900763510509877783 16492943851145265764816675)
                  ·
                    refine ⟨24739415776717898647225013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16492943851145265764816675 24739415776717898647225013)
                    ·
                      refine ⟨2319320229067302998177345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24739415776717898647225013 2319320229067302998177345)
                      ·
                        rfl

theorem cell23_4516860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_4516860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516860 prefixEnd_4516860 := by exact prefixLift 4516860
  have htrace : WordTrace (prefixWord ++ tailWord_4516860) baseStart_4516860 baseEnd_4516860 := by
    simpa [prefixWord, tailWord_4516860, baseEnd_4516860] using wordTrace_append hprefix tailTrace_4516860
  have hstable : (prefixWord ++ tailWord_4516860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516860).length < 2 ^ (prefixWord ++ tailWord_4516860).sum := by decide
  have hdescent : baseEnd_4516860 < baseStart_4516860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516890 : List Nat := [3, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3]
def baseStart_4516890 : Nat := 118140960795 + 4516890 * 2 ^ 59
def prefixEnd_4516890 : Nat := 4983230072969 + 3 ^ 40 * 4516890 * 2
def baseEnd_4516890 : Nat := 2319335633486937880802207

theorem tailTrace_4516890 : CollatzResearch.WordTrace tailWord_4516890 prefixEnd_4516890 2319335633486937880802207 := by
  unfold tailWord_4516890
  simp only [CollatzResearch.WordTrace]
  refine ⟨41186128151521607060239031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109829675070724285493970749 41186128151521607060239031)
  ·
    refine ⟨61779192227282410590358547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41186128151521607060239031 61779192227282410590358547)
    ·
      refine ⟨92668788340923615885537821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61779192227282410590358547 92668788340923615885537821)
      ·
        refine ⟨34750795627846355957076683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92668788340923615885537821 34750795627846355957076683)
        ·
          refine ⟨52126193441769533935615025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34750795627846355957076683 52126193441769533935615025)
          ·
            refine ⟨39094645081327150451711269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52126193441769533935615025 39094645081327150451711269)
            ·
              refine ⟨7330245952748840709695863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39094645081327150451711269 7330245952748840709695863)
              ·
                refine ⟨10995368929123261064543795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7330245952748840709695863 10995368929123261064543795)
                ·
                  refine ⟨16493053393684891596815693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10995368929123261064543795 16493053393684891596815693)
                  ·
                    refine ⟨6184895022631834348805885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16493053393684891596815693 6184895022631834348805885)
                    ·
                      refine ⟨2319335633486937880802207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6184895022631834348805885 2319335633486937880802207)
                      ·
                        rfl

theorem cell23_4516890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_4516890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516890 prefixEnd_4516890 := by exact prefixLift 4516890
  have htrace : WordTrace (prefixWord ++ tailWord_4516890) baseStart_4516890 baseEnd_4516890 := by
    simpa [prefixWord, tailWord_4516890, baseEnd_4516890] using wordTrace_append hprefix tailTrace_4516890
  have hstable : (prefixWord ++ tailWord_4516890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516890).length < 2 ^ (prefixWord ++ tailWord_4516890).sum := by decide
  have hdescent : baseEnd_4516890 < baseStart_4516890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516924 : List Nat := [2, 2, 2, 2, 2, 4, 1, 2, 2, 1, 3]
def baseStart_4516924 : Nat := 118140960795 + 4516924 * 2 ^ 59
def prefixEnd_4516924 : Nat := 4983230072969 + 3 ^ 40 * 4516924 * 2
def baseEnd_4516924 : Nat := 2319353091829190747777051

theorem tailTrace_4516924 : CollatzResearch.WordTrace tailWord_4516924 prefixEnd_4516924 2319353091829190747777051 := by
  unfold tailWord_4516924
  simp only [CollatzResearch.WordTrace]
  refine ⟨82372876343981626023846913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109830501791975501365129217 82372876343981626023846913)
  ·
    refine ⟨61779657257986219517885185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82372876343981626023846913 61779657257986219517885185)
    ·
      refine ⟨46334742943489664638413889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61779657257986219517885185 46334742943489664638413889)
      ·
        refine ⟨34751057207617248478810417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46334742943489664638413889 34751057207617248478810417)
        ·
          refine ⟨26063292905712936359107813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34751057207617248478810417 26063292905712936359107813)
          ·
            refine ⟨4886867419821175567332715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26063292905712936359107813 4886867419821175567332715)
            ·
              refine ⟨7330301129731763350999073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4886867419821175567332715 7330301129731763350999073)
              ·
                refine ⟨5497725847298822513249305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7330301129731763350999073 5497725847298822513249305)
                ·
                  refine ⟨4123294385474116884936979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5497725847298822513249305 4123294385474116884936979)
                  ·
                    refine ⟨6184941578211175327405469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4123294385474116884936979 6184941578211175327405469)
                    ·
                      refine ⟨2319353091829190747777051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6184941578211175327405469 2319353091829190747777051)
                      ·
                        rfl

theorem cell23_4516924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_4516924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516924 prefixEnd_4516924 := by exact prefixLift 4516924
  have htrace : WordTrace (prefixWord ++ tailWord_4516924) baseStart_4516924 baseEnd_4516924 := by
    simpa [prefixWord, tailWord_4516924, baseEnd_4516924] using wordTrace_append hprefix tailTrace_4516924
  have hstable : (prefixWord ++ tailWord_4516924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516924).length < 2 ^ (prefixWord ++ tailWord_4516924).sum := by decide
  have hdescent : baseEnd_4516924 < baseStart_4516924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516933 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 1, 6, 3]
def baseStart_4516933 : Nat := 118140960795 + 4516933 * 2 ^ 59
def prefixEnd_4516933 : Nat := 4983230072969 + 3 ^ 40 * 4516933 * 2
def baseEnd_4516933 : Nat := 2319357713155081212564509

theorem tailTrace_4516933 : CollatzResearch.WordTrace tailWord_4516933 prefixEnd_4516933 2319357713155081212564509 := by
  unfold tailWord_4516933
  simp only [CollatzResearch.WordTrace]
  refine ⟨164746080944930646584771453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109830720629953764389847635 164746080944930646584771453)
  ·
    refine ⟨61779780354348992469289295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164746080944930646584771453 61779780354348992469289295)
    ·
      refine ⟨92669670531523488703933943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61779780354348992469289295 92669670531523488703933943)
      ·
        refine ⟨139004505797285233055900915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92669670531523488703933943 139004505797285233055900915)
        ·
          refine ⟨208506758695927849583851373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139004505797285233055900915 208506758695927849583851373)
          ·
            refine ⟨78190034510972943593944265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208506758695927849583851373 78190034510972943593944265)
            ·
              refine ⟨58642525883229707695458199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78190034510972943593944265 58642525883229707695458199)
              ·
                refine ⟨87963788824844561543187299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58642525883229707695458199 87963788824844561543187299)
                ·
                  refine ⟨131945683237266842314780949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87963788824844561543187299 131945683237266842314780949)
                  ·
                    refine ⟨6184953901746883233505357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 131945683237266842314780949 6184953901746883233505357)
                    ·
                      refine ⟨2319357713155081212564509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6184953901746883233505357 2319357713155081212564509)
                      ·
                        rfl

theorem cell23_4516933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 6, 3].length) (baseStart_4516933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516933 prefixEnd_4516933 := by exact prefixLift 4516933
  have htrace : WordTrace (prefixWord ++ tailWord_4516933) baseStart_4516933 baseEnd_4516933 := by
    simpa [prefixWord, tailWord_4516933, baseEnd_4516933] using wordTrace_append hprefix tailTrace_4516933
  have hstable : (prefixWord ++ tailWord_4516933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516933).length < 2 ^ (prefixWord ++ tailWord_4516933).sum := by decide
  have hdescent : baseEnd_4516933 < baseStart_4516933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4516941 : List Nat := [1, 6, 1, 1, 1, 3, 3, 1, 2, 1, 3]
def baseStart_4516941 : Nat := 118140960795 + 4516941 * 2 ^ 59
def prefixEnd_4516941 : Nat := 4983230072969 + 3 ^ 40 * 4516941 * 2
def baseEnd_4516941 : Nat := 2319361821000317181264473

theorem tailTrace_4516941 : CollatzResearch.WordTrace tailWord_4516941 prefixEnd_4516941 2319361821000317181264473 := by
  unfold tailWord_4516941
  simp only [CollatzResearch.WordTrace]
  refine ⟨164746372728901663951062677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109830915152601109300708451 164746372728901663951062677)
  ·
    refine ⟨7722486221667265497706063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 164746372728901663951062677 7722486221667265497706063)
    ·
      refine ⟨11583729332500898246559095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7722486221667265497706063 11583729332500898246559095)
      ·
        refine ⟨17375593998751347369838643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11583729332500898246559095 17375593998751347369838643)
        ·
          refine ⟨26063390998127021054757965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17375593998751347369838643 26063390998127021054757965)
          ·
            refine ⟨9773771624297632895534237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26063390998127021054757965 9773771624297632895534237)
            ·
              refine ⟨3665164359111612335825339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9773771624297632895534237 3665164359111612335825339)
              ·
                refine ⟨5497746538667418503738009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3665164359111612335825339 5497746538667418503738009)
                ·
                  refine ⟨4123309904000563877803507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5497746538667418503738009 4123309904000563877803507)
                  ·
                    refine ⟨6184964856000845816705261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4123309904000563877803507 6184964856000845816705261)
                    ·
                      refine ⟨2319361821000317181264473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6184964856000845816705261 2319361821000317181264473)
                      ·
                        rfl

theorem cell23_4516941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_4516941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4516941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4516941 prefixEnd_4516941 := by exact prefixLift 4516941
  have htrace : WordTrace (prefixWord ++ tailWord_4516941) baseStart_4516941 baseEnd_4516941 := by
    simpa [prefixWord, tailWord_4516941, baseEnd_4516941] using wordTrace_append hprefix tailTrace_4516941
  have hstable : (prefixWord ++ tailWord_4516941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4516941).length < 2 ^ (prefixWord ++ tailWord_4516941).sum := by decide
  have hdescent : baseEnd_4516941 < baseStart_4516941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4516941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517003 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 4]
def baseStart_4517003 : Nat := 118140960795 + 4517003 * 2 ^ 59
def prefixEnd_4517003 : Nat := 4983230072969 + 3 ^ 40 * 4517003 * 2
def baseEnd_4517003 : Nat := 2319393656800895938689187

theorem tailTrace_4517003 : CollatzResearch.WordTrace tailWord_4517003 prefixEnd_4517003 2319393656800895938689187 := by
  unfold tailWord_4517003
  simp only [CollatzResearch.WordTrace]
  refine ⟨164748634054677048539819663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109832422703118032359879775 164748634054677048539819663)
  ·
    refine ⟨247122951082015572809729495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164748634054677048539819663 247122951082015572809729495)
    ·
      refine ⟨370684426623023359214594243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247122951082015572809729495 370684426623023359214594243)
      ·
        refine ⟨556026639934535038821891365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370684426623023359214594243 556026639934535038821891365)
        ·
          refine ⟨104254994987725319779104631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 556026639934535038821891365 104254994987725319779104631)
          ·
            refine ⟨156382492481587979668656947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104254994987725319779104631 156382492481587979668656947)
            ·
              refine ⟨234573738722381969502985421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156382492481587979668656947 234573738722381969502985421)
              ·
                refine ⟨87965152020893238563619533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234573738722381969502985421 87965152020893238563619533)
                ·
                  refine ⟨32986932007834964461357325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87965152020893238563619533 32986932007834964461357325)
                  ·
                    refine ⟨12370099502938111673008997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32986932007834964461357325 12370099502938111673008997)
                    ·
                      refine ⟨2319393656800895938689187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12370099502938111673008997 2319393656800895938689187)
                      ·
                        rfl

theorem cell23_4517003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 4].length) (baseStart_4517003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517003 prefixEnd_4517003 := by exact prefixLift 4517003
  have htrace : WordTrace (prefixWord ++ tailWord_4517003) baseStart_4517003 baseEnd_4517003 := by
    simpa [prefixWord, tailWord_4517003, baseEnd_4517003] using wordTrace_append hprefix tailTrace_4517003
  have hstable : (prefixWord ++ tailWord_4517003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517003).length < 2 ^ (prefixWord ++ tailWord_4517003).sum := by decide
  have hdescent : baseEnd_4517003 < baseStart_4517003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517033 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 3, 6, 4]
def baseStart_4517033 : Nat := 118140960795 + 4517033 * 2 ^ 59
def prefixEnd_4517033 : Nat := 4983230072969 + 3 ^ 40 * 4517033 * 2
def baseEnd_4517033 : Nat := 2319409061220530821314049

theorem tailTrace_4517033 : CollatzResearch.WordTrace tailWord_4517033 prefixEnd_4517033 2319409061220530821314049 := by
  unfold tailWord_4517033
  simp only [CollatzResearch.WordTrace]
  refine ⟨164749728244568363663411753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109833152163045575775607835 164749728244568363663411753)
  ·
    refine ⟨123562296183426272747558815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164749728244568363663411753 123562296183426272747558815)
    ·
      refine ⟨185343444275139409121338223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123562296183426272747558815 185343444275139409121338223)
      ·
        refine ⟨278015166412709113682007335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185343444275139409121338223 278015166412709113682007335)
        ·
          refine ⟨417022749619063670523011003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278015166412709113682007335 417022749619063670523011003)
          ·
            refine ⟨625534124428595505784516505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417022749619063670523011003 625534124428595505784516505)
            ·
              refine ⟨469150593321446629338387379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 625534124428595505784516505 469150593321446629338387379)
              ·
                refine ⟨703725889982169944007581069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469150593321446629338387379 703725889982169944007581069)
                ·
                  refine ⟨263897208743313729002842901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 703725889982169944007581069 263897208743313729002842901)
                  ·
                    refine ⟨12370181659842831047008261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 263897208743313729002842901 12370181659842831047008261)
                    ·
                      refine ⟨2319409061220530821314049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12370181659842831047008261 2319409061220530821314049)
                      ·
                        rfl

theorem cell23_4517033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 6, 4].length) (baseStart_4517033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517033 prefixEnd_4517033 := by exact prefixLift 4517033
  have htrace : WordTrace (prefixWord ++ tailWord_4517033) baseStart_4517033 baseEnd_4517033 := by
    simpa [prefixWord, tailWord_4517033, baseEnd_4517033] using wordTrace_append hprefix tailTrace_4517033
  have hstable : (prefixWord ++ tailWord_4517033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517033).length < 2 ^ (prefixWord ++ tailWord_4517033).sum := by decide
  have hdescent : baseEnd_4517033 < baseStart_4517033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517043 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 8]
def baseStart_4517043 : Nat := 118140960795 + 4517043 * 2 ^ 59
def prefixEnd_4517043 : Nat := 4983230072969 + 3 ^ 40 * 4517043 * 2
def baseEnd_4517043 : Nat := 257712688447452864687667

theorem tailTrace_4517043 : CollatzResearch.WordTrace tailWord_4517043 prefixEnd_4517043 257712688447452864687667 := by
  unfold tailWord_4517043
  simp only [CollatzResearch.WordTrace]
  refine ⟨164750092974532135371275783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109833395316354756914183855 164750092974532135371275783)
  ·
    refine ⟨247125139461798203056913675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164750092974532135371275783 247125139461798203056913675)
    ·
      refine ⟨370687709192697304585370513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247125139461798203056913675 370687709192697304585370513)
      ·
        refine ⟨278015781894522978439027885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 370687709192697304585370513 278015781894522978439027885)
        ·
          refine ⟨104255918210446116914635457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 278015781894522978439027885 104255918210446116914635457)
          ·
            refine ⟨78191938657834587685976593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104255918210446116914635457 78191938657834587685976593)
            ·
              refine ⟨58643953993375940764482445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78191938657834587685976593 58643953993375940764482445)
              ·
                refine ⟨21991482747515977786680917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58643953993375940764482445 21991482747515977786680917)
                ·
                  refine ⟨257712688447452864687667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21991482747515977786680917 257712688447452864687667)
                  ·
                    rfl

theorem cell23_4517043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 8].length) (baseStart_4517043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517043 prefixEnd_4517043 := by exact prefixLift 4517043
  have htrace : WordTrace (prefixWord ++ tailWord_4517043) baseStart_4517043 baseEnd_4517043 := by
    simpa [prefixWord, tailWord_4517043, baseEnd_4517043] using wordTrace_append hprefix tailTrace_4517043
  have hstable : (prefixWord ++ tailWord_4517043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517043).length < 2 ^ (prefixWord ++ tailWord_4517043).sum := by decide
  have hdescent : baseEnd_4517043 < baseStart_4517043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517054 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2]
def baseStart_4517054 : Nat := 118140960795 + 4517054 * 2 ^ 59
def prefixEnd_4517054 : Nat := 4983230072969 + 3 ^ 40 * 4517054 * 2
def baseEnd_4517054 : Nat := 2319419844314275239151453

theorem tailTrace_4517054 : CollatzResearch.WordTrace tailWord_4517054 prefixEnd_4517054 2319419844314275239151453 := by
  unfold tailWord_4517054
  simp only [CollatzResearch.WordTrace]
  refine ⟨20593811772186535531240777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109833662784994856166617477 20593811772186535531240777)
  ·
    refine ⟨15445358829139901648430583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20593811772186535531240777 15445358829139901648430583)
    ·
      refine ⟨23168038243709852472645875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15445358829139901648430583 23168038243709852472645875)
      ·
        refine ⟨34752057365564778708968813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23168038243709852472645875 34752057365564778708968813)
        ·
          refine ⟨13032021512086792015863305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34752057365564778708968813 13032021512086792015863305)
          ·
            refine ⟨9774016134065094011897479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13032021512086792015863305 9774016134065094011897479)
            ·
              refine ⟨14661024201097641017846219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9774016134065094011897479 14661024201097641017846219)
              ·
                refine ⟨21991536301646461526769329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14661024201097641017846219 21991536301646461526769329)
                ·
                  refine ⟨16493652226234846145076997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21991536301646461526769329 16493652226234846145076997)
                  ·
                    refine ⟨3092559792419033652201937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16493652226234846145076997 3092559792419033652201937)
                    ·
                      refine ⟨2319419844314275239151453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3092559792419033652201937 2319419844314275239151453)
                      ·
                        rfl

theorem cell23_4517054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_4517054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517054 prefixEnd_4517054 := by exact prefixLift 4517054
  have htrace : WordTrace (prefixWord ++ tailWord_4517054) baseStart_4517054 baseEnd_4517054 := by
    simpa [prefixWord, tailWord_4517054, baseEnd_4517054] using wordTrace_append hprefix tailTrace_4517054
  have hstable : (prefixWord ++ tailWord_4517054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517054).length < 2 ^ (prefixWord ++ tailWord_4517054).sum := by decide
  have hdescent : baseEnd_4517054 < baseStart_4517054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517083 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 7]
def baseStart_4517083 : Nat := 118140960795 + 4517083 * 2 ^ 59
def prefixEnd_4517083 : Nat := 4983230072969 + 3 ^ 40 * 4517083 * 2
def baseEnd_4517083 : Nat := 2319434735253255625688819

theorem tailTrace_4517083 : CollatzResearch.WordTrace tailWord_4517083 prefixEnd_4517083 2319434735253255625688819 := by
  unfold tailWord_4517083
  simp only [CollatzResearch.WordTrace]
  refine ⟨164751551894387222202731903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109834367929591481468487935 164751551894387222202731903)
  ·
    refine ⟨247127327841580833304097855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164751551894387222202731903 247127327841580833304097855)
    ·
      refine ⟨370690991762371249956146783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247127327841580833304097855 370690991762371249956146783)
      ·
        refine ⟨556036487643556874934220175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370690991762371249956146783 556036487643556874934220175)
        ·
          refine ⟨834054731465335312401330263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556036487643556874934220175 834054731465335312401330263)
          ·
            refine ⟨1251082097198002968601995395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 834054731465335312401330263 1251082097198002968601995395)
            ·
              refine ⟨1876623145797004452902993093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1251082097198002968601995395 1876623145797004452902993093)
              ·
                refine ⟨351866839836938334919311205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1876623145797004452902993093 351866839836938334919311205)
                ·
                  refine ⟨65975032469425937797370851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 351866839836938334919311205 65975032469425937797370851)
                  ·
                    refine ⟨98962548704138906696056277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65975032469425937797370851 98962548704138906696056277)
                    ·
                      refine ⟨2319434735253255625688819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98962548704138906696056277 2319434735253255625688819)
                      ·
                        rfl

theorem cell23_4517083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 7].length) (baseStart_4517083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517083 prefixEnd_4517083 := by exact prefixLift 4517083
  have htrace : WordTrace (prefixWord ++ tailWord_4517083) baseStart_4517083 baseEnd_4517083 := by
    simpa [prefixWord, tailWord_4517083, baseEnd_4517083] using wordTrace_append hprefix tailTrace_4517083
  have hstable : (prefixWord ++ tailWord_4517083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517083).length < 2 ^ (prefixWord ++ tailWord_4517083).sum := by decide
  have hdescent : baseEnd_4517083 < baseStart_4517083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517124 : List Nat := [2, 3, 2, 2, 2, 2, 2, 2, 1, 5]
def baseStart_4517124 : Nat := 118140960795 + 4517124 * 2 ^ 59
def prefixEnd_4517124 : Nat := 4983230072969 + 3 ^ 40 * 4517124 * 2
def baseEnd_4517124 : Nat := 773151929320029988425377

theorem tailTrace_4517124 : CollatzResearch.WordTrace tailWord_4517124 prefixEnd_4517124 773151929320029988425377 := by
  unfold tailWord_4517124
  simp only [CollatzResearch.WordTrace]
  refine ⟨82376523643619343102487213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109835364858159124136649617 82376523643619343102487213)
  ·
    refine ⟨30891196366357253663432705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82376523643619343102487213 30891196366357253663432705)
    ·
      refine ⟨23168397274767940247574529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30891196366357253663432705 23168397274767940247574529)
      ·
        refine ⟨17376297956075955185680897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23168397274767940247574529 17376297956075955185680897)
        ·
          refine ⟨13032223467056966389260673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17376297956075955185680897 13032223467056966389260673)
          ·
            refine ⟨9774167600292724791945505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13032223467056966389260673 9774167600292724791945505)
            ·
              refine ⟨7330625700219543593959129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9774167600292724791945505 7330625700219543593959129)
              ·
                refine ⟨5497969275164657695469347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7330625700219543593959129 5497969275164657695469347)
                ·
                  refine ⟨8246953912746986543204021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5497969275164657695469347 8246953912746986543204021)
                  ·
                    refine ⟨773151929320029988425377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8246953912746986543204021 773151929320029988425377)
                    ·
                      rfl

theorem cell23_4517124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_4517124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517124 prefixEnd_4517124 := by exact prefixLift 4517124
  have htrace : WordTrace (prefixWord ++ tailWord_4517124) baseStart_4517124 baseEnd_4517124 := by
    simpa [prefixWord, tailWord_4517124, baseEnd_4517124] using wordTrace_append hprefix tailTrace_4517124
  have hstable : (prefixWord ++ tailWord_4517124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517124).length < 2 ^ (prefixWord ++ tailWord_4517124).sum := by decide
  have hdescent : baseEnd_4517124 < baseStart_4517124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517130 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5]
def baseStart_4517130 : Nat := 118140960795 + 4517130 * 2 ^ 59
def prefixEnd_4517130 : Nat := 4983230072969 + 3 ^ 40 * 4517130 * 2
def baseEnd_4517130 : Nat := 2319458868844016941801103

theorem tailTrace_4517130 : CollatzResearch.WordTrace tailWord_4517130 prefixEnd_4517130 2319458868844016941801103 := by
  unfold tailWord_4517130
  simp only [CollatzResearch.WordTrace]
  refine ⟨41188316531304237307423211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109835510750144632819795229 41188316531304237307423211)
  ·
    refine ⟨61782474796956355961134817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41188316531304237307423211 61782474796956355961134817)
    ·
      refine ⟨46336856097717266970851113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61782474796956355961134817 46336856097717266970851113)
      ·
        refine ⟨34752642073287950228138335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46336856097717266970851113 34752642073287950228138335)
        ·
          refine ⟨52128963109931925342207503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34752642073287950228138335 52128963109931925342207503)
          ·
            refine ⟨78193444664897888013311255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52128963109931925342207503 78193444664897888013311255)
            ·
              refine ⟨117290166997346832019966883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78193444664897888013311255 117290166997346832019966883)
              ·
                refine ⟨175935250496020248029950325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117290166997346832019966883 175935250496020248029950325)
                ·
                  refine ⟨16493929734001898252807843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 175935250496020248029950325 16493929734001898252807843)
                  ·
                    refine ⟨24740894601002847379211765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16493929734001898252807843 24740894601002847379211765)
                    ·
                      refine ⟨2319458868844016941801103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24740894601002847379211765 2319458868844016941801103)
                      ·
                        rfl

theorem cell23_4517130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_4517130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517130 prefixEnd_4517130 := by exact prefixLift 4517130
  have htrace : WordTrace (prefixWord ++ tailWord_4517130) baseStart_4517130 baseEnd_4517130 := by
    simpa [prefixWord, tailWord_4517130, baseEnd_4517130] using wordTrace_append hprefix tailTrace_4517130
  have hstable : (prefixWord ++ tailWord_4517130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517130).length < 2 ^ (prefixWord ++ tailWord_4517130).sum := by decide
  have hdescent : baseEnd_4517130 < baseStart_4517130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517171 : List Nat := [1, 1, 1, 2, 5, 4, 2, 1, 2, 4]
def baseStart_4517171 : Nat := 118140960795 + 4517171 * 2 ^ 59
def prefixEnd_4517171 : Nat := 4983230072969 + 3 ^ 40 * 4517171 * 2
def baseEnd_4517171 : Nat := 773159973850283760462805

theorem tailTrace_4517171 : CollatzResearch.WordTrace tailWord_4517171 prefixEnd_4517171 773159973850283760462805 := by
  unfold tailWord_4517171
  simp only [CollatzResearch.WordTrace]
  refine ⟨164754761518068413231935367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109836507678712275487956911 164754761518068413231935367)
  ·
    refine ⟨247132142277102619847903051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164754761518068413231935367 247132142277102619847903051)
    ·
      refine ⟨370698213415653929771854577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247132142277102619847903051 370698213415653929771854577)
      ·
        refine ⟨278023660061740447328890933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 370698213415653929771854577 278023660061740447328890933)
        ·
          refine ⟨26064718130788166937083525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 278023660061740447328890933 26064718130788166937083525)
          ·
            refine ⟨4887134649522781300703161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26064718130788166937083525 4887134649522781300703161)
            ·
              refine ⟨3665350987142085975527371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4887134649522781300703161 3665350987142085975527371)
              ·
                refine ⟨5498026480713128963291057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3665350987142085975527371 5498026480713128963291057)
                ·
                  refine ⟨4123519860534846722468293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5498026480713128963291057 4123519860534846722468293)
                  ·
                    refine ⟨773159973850283760462805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4123519860534846722468293 773159973850283760462805)
                    ·
                      rfl

theorem cell23_4517171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 2, 4].length) (baseStart_4517171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517171 prefixEnd_4517171 := by exact prefixLift 4517171
  have htrace : WordTrace (prefixWord ++ tailWord_4517171) baseStart_4517171 baseEnd_4517171 := by
    simpa [prefixWord, tailWord_4517171, baseEnd_4517171] using wordTrace_append hprefix tailTrace_4517171
  have hstable : (prefixWord ++ tailWord_4517171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517171).length < 2 ^ (prefixWord ++ tailWord_4517171).sum := by decide
  have hdescent : baseEnd_4517171 < baseStart_4517171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517181 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 3, 2, 3]
def baseStart_4517181 : Nat := 118140960795 + 4517181 * 2 ^ 59
def prefixEnd_4517181 : Nat := 4983230072969 + 3 ^ 40 * 4517181 * 2
def baseEnd_4517181 : Nat := 2319485056357396242263369

theorem tailTrace_4517181 : CollatzResearch.WordTrace tailWord_4517181 prefixEnd_4517181 2319485056357396242263369 := by
  unfold tailWord_4517181
  simp only [CollatzResearch.WordTrace]
  refine ⟨164755126248032184939799397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109836750832021456626532931 164755126248032184939799397)
  ·
    refine ⟨30891586171506034676212387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164755126248032184939799397 30891586171506034676212387)
    ·
      refine ⟨46337379257259052014318581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30891586171506034676212387 46337379257259052014318581)
      ·
        refine ⟨4344129305368036126342367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46337379257259052014318581 4344129305368036126342367)
        ·
          refine ⟨6516193958052054189513551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4344129305368036126342367 6516193958052054189513551)
          ·
            refine ⟨9774290937078081284270327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6516193958052054189513551 9774290937078081284270327)
            ·
              refine ⟨14661436405617121926405491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9774290937078081284270327 14661436405617121926405491)
              ·
                refine ⟨21992154608425682889608237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14661436405617121926405491 21992154608425682889608237)
                ·
                  refine ⟨8247057978159631083603089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21992154608425682889608237 8247057978159631083603089)
                  ·
                    refine ⟨6185293483619723312702317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8247057978159631083603089 6185293483619723312702317)
                    ·
                      refine ⟨2319485056357396242263369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6185293483619723312702317 2319485056357396242263369)
                      ·
                        rfl

theorem cell23_4517181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_4517181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517181 prefixEnd_4517181 := by exact prefixLift 4517181
  have htrace : WordTrace (prefixWord ++ tailWord_4517181) baseStart_4517181 baseEnd_4517181 := by
    simpa [prefixWord, tailWord_4517181, baseEnd_4517181] using wordTrace_append hprefix tailTrace_4517181
  have hstable : (prefixWord ++ tailWord_4517181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517181).length < 2 ^ (prefixWord ++ tailWord_4517181).sum := by decide
  have hdescent : baseEnd_4517181 < baseStart_4517181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517206 : List Nat := [5, 2, 3, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_4517206 : Nat := 118140960795 + 4517206 * 2 ^ 59
def prefixEnd_4517206 : Nat := 4983230072969 + 3 ^ 40 * 4517206 * 2
def baseEnd_4517206 : Nat := 2319497893373758644450755

theorem tailTrace_4517206 : CollatzResearch.WordTrace tailWord_4517206 prefixEnd_4517206 2319497893373758644450755 := by
  unfold tailWord_4517206
  simp only [CollatzResearch.WordTrace]
  refine ⟨10297252379558850888091217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109837358715294409472972981 10297252379558850888091217)
  ·
    refine ⟨7722939284669138166068413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10297252379558850888091217 7722939284669138166068413)
    ·
      refine ⟨2896102231750926812275655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7722939284669138166068413 2896102231750926812275655)
      ·
        refine ⟨4344153347626390218413483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2896102231750926812275655 4344153347626390218413483)
        ·
          refine ⟨6516230021439585327620225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4344153347626390218413483 6516230021439585327620225)
          ·
            refine ⟨4887172516079688995715169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6516230021439585327620225 4887172516079688995715169)
            ·
              refine ⟨3665379387059766746786377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4887172516079688995715169 3665379387059766746786377)
              ·
                refine ⟨2749034540294825060089783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3665379387059766746786377 2749034540294825060089783)
                ·
                  refine ⟨4123551810442237590134675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2749034540294825060089783 4123551810442237590134675)
                  ·
                    refine ⟨6185327715663356385202013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4123551810442237590134675 6185327715663356385202013)
                    ·
                      refine ⟨2319497893373758644450755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6185327715663356385202013 2319497893373758644450755)
                      ·
                        rfl

theorem cell23_4517206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_4517206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517206 prefixEnd_4517206 := by exact prefixLift 4517206
  have htrace : WordTrace (prefixWord ++ tailWord_4517206) baseStart_4517206 baseEnd_4517206 := by
    simpa [prefixWord, tailWord_4517206, baseEnd_4517206] using wordTrace_append hprefix tailTrace_4517206
  have hstable : (prefixWord ++ tailWord_4517206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517206).length < 2 ^ (prefixWord ++ tailWord_4517206).sum := by decide
  have hdescent : baseEnd_4517206 < baseStart_4517206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517268 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 4, 2, 2]
def baseStart_4517268 : Nat := 118140960795 + 4517268 * 2 ^ 59
def prefixEnd_4517268 : Nat := 4983230072969 + 3 ^ 40 * 4517268 * 2
def baseEnd_4517268 : Nat := 2319529729174337401875469

theorem tailTrace_4517268 : CollatzResearch.WordTrace tailWord_4517268 prefixEnd_4517268 2319529729174337401875469 := by
  unfold tailWord_4517268
  simp only [CollatzResearch.WordTrace]
  refine ⟨82379149699358499399108229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109838866265811332532144305 82379149699358499399108229)
  ·
    refine ⟨15446090568629718637332793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82379149699358499399108229 15446090568629718637332793)
    ·
      refine ⟨11584567926472288977999595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15446090568629718637332793 11584567926472288977999595)
      ·
        refine ⟨17376851889708433466999393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11584567926472288977999595 17376851889708433466999393)
        ·
          refine ⟨13032638917281325100249545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17376851889708433466999393 13032638917281325100249545)
          ·
            refine ⟨9774479187960993825187159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13032638917281325100249545 9774479187960993825187159)
            ·
              refine ⟨14661718781941490737780739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9774479187960993825187159 14661718781941490737780739)
              ·
                refine ⟨21992578172912236106671109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14661718781941490737780739 21992578172912236106671109)
                ·
                  refine ⟨4123608407421044270000833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21992578172912236106671109 4123608407421044270000833)
                  ·
                    refine ⟨3092706305565783202500625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4123608407421044270000833 3092706305565783202500625)
                    ·
                      refine ⟨2319529729174337401875469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3092706305565783202500625 2319529729174337401875469)
                      ·
                        rfl

theorem cell23_4517268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_4517268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517268 prefixEnd_4517268 := by exact prefixLift 4517268
  have htrace : WordTrace (prefixWord ++ tailWord_4517268) baseStart_4517268 baseEnd_4517268 := by
    simpa [prefixWord, tailWord_4517268, baseEnd_4517268] using wordTrace_append hprefix tailTrace_4517268
  have hstable : (prefixWord ++ tailWord_4517268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517268).length < 2 ^ (prefixWord ++ tailWord_4517268).sum := by decide
  have hdescent : baseEnd_4517268 < baseStart_4517268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517274 : List Nat := [3, 1, 1, 4, 1, 1, 1, 6, 5]
def baseStart_4517274 : Nat := 118140960795 + 4517274 * 2 ^ 59
def prefixEnd_4517274 : Nat := 4983230072969 + 3 ^ 40 * 4517274 * 2
def baseEnd_4517274 : Nat := 257725867784251597600049

theorem tailTrace_4517274 : CollatzResearch.WordTrace tailWord_4517274 prefixEnd_4517274 257725867784251597600049 := by
  unfold tailWord_4517274
  simp only [CollatzResearch.WordTrace]
  refine ⟨41189629559173815455733719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109839012157796841215289917 41189629559173815455733719)
  ·
    refine ⟨61784444338760723183600579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41189629559173815455733719 61784444338760723183600579)
    ·
      refine ⟨92676666508141084775400869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61784444338760723183600579 92676666508141084775400869)
      ·
        refine ⟨17376874970276453395387663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92676666508141084775400869 17376874970276453395387663)
        ·
          refine ⟨26065312455414680093081495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17376874970276453395387663 26065312455414680093081495)
          ·
            refine ⟨39097968683122020139622243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26065312455414680093081495 39097968683122020139622243)
            ·
              refine ⟨58646953024683030209433365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39097968683122020139622243 58646953024683030209433365)
              ·
                refine ⟨2749075923032017041067189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58646953024683030209433365 2749075923032017041067189)
                ·
                  refine ⟨257725867784251597600049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2749075923032017041067189 257725867784251597600049)
                  ·
                    rfl

theorem cell23_4517274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 5].length) (baseStart_4517274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517274 prefixEnd_4517274 := by exact prefixLift 4517274
  have htrace : WordTrace (prefixWord ++ tailWord_4517274) baseStart_4517274 baseEnd_4517274 := by
    simpa [prefixWord, tailWord_4517274, baseEnd_4517274] using wordTrace_append hprefix tailTrace_4517274
  have hstable : (prefixWord ++ tailWord_4517274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517274).length < 2 ^ (prefixWord ++ tailWord_4517274).sum := by decide
  have hdescent : baseEnd_4517274 < baseStart_4517274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517287 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 3, 7]
def baseStart_4517287 : Nat := 118140960795 + 4517287 * 2 ^ 59
def prefixEnd_4517287 : Nat := 4983230072969 + 3 ^ 40 * 4517287 * 2
def baseEnd_4517287 : Nat := 773179828435590942512627

theorem tailTrace_4517287 : CollatzResearch.WordTrace tailWord_4517287 prefixEnd_4517287 773179828435590942512627 := by
  unfold tailWord_4517287
  simp only [CollatzResearch.WordTrace]
  refine ⟨164758992385648165043158115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109839328257098776695438743 164758992385648165043158115)
  ·
    refine ⟨247138488578472247564737173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164758992385648165043158115 247138488578472247564737173)
    ·
      refine ⟨11584616652115886604597055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 247138488578472247564737173 11584616652115886604597055)
      ·
        refine ⟨17376924978173829906895583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11584616652115886604597055 17376924978173829906895583)
        ·
          refine ⟨26065387467260744860343375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17376924978173829906895583 26065387467260744860343375)
          ·
            refine ⟨39098081200891117290515063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26065387467260744860343375 39098081200891117290515063)
            ·
              refine ⟨58647121801336675935772595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39098081200891117290515063 58647121801336675935772595)
              ·
                refine ⟨87970682702005013903658893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58647121801336675935772595 87970682702005013903658893)
                ·
                  refine ⟨32989006013251880213872085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87970682702005013903658893 32989006013251880213872085)
                  ·
                    refine ⟨773179828435590942512627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32989006013251880213872085 773179828435590942512627)
                    ·
                      rfl

theorem cell23_4517287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_4517287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517287 prefixEnd_4517287 := by exact prefixLift 4517287
  have htrace : WordTrace (prefixWord ++ tailWord_4517287) baseStart_4517287 baseEnd_4517287 := by
    simpa [prefixWord, tailWord_4517287, baseEnd_4517287] using wordTrace_append hprefix tailTrace_4517287
  have hstable : (prefixWord ++ tailWord_4517287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517287).length < 2 ^ (prefixWord ++ tailWord_4517287).sum := by decide
  have hdescent : baseEnd_4517287 < baseStart_4517287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517308 : List Nat := [2, 2, 2, 4, 2, 2, 1, 3, 5]
def baseStart_4517308 : Nat := 118140960795 + 4517308 * 2 ^ 59
def prefixEnd_4517308 : Nat := 4983230072969 + 3 ^ 40 * 4517308 * 2
def baseEnd_4517308 : Nat := 257727807600057471708365

theorem tailTrace_4517308 : CollatzResearch.WordTrace tailWord_4517308 prefixEnd_4517308 257727807600057471708365 := by
  unfold tailWord_4517308
  simp only [CollatzResearch.WordTrace]
  refine ⟨82379879159286042814836289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109839838879048057086448385 82379879159286042814836289)
  ·
    refine ⟨61784909369464532111127217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82379879159286042814836289 61784909369464532111127217)
    ·
      refine ⟨46338682027098399083345413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61784909369464532111127217 46338682027098399083345413)
      ·
        refine ⟨8688502880080949828127265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46338682027098399083345413 8688502880080949828127265)
        ·
          refine ⟨6516377160060712371095449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8688502880080949828127265 6516377160060712371095449)
          ·
            refine ⟨4887282870045534278321587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6516377160060712371095449 4887282870045534278321587)
            ·
              refine ⟨7330924305068301417482381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4887282870045534278321587 7330924305068301417482381)
              ·
                refine ⟨2749096614400613031555893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7330924305068301417482381 2749096614400613031555893)
                ·
                  refine ⟨257727807600057471708365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2749096614400613031555893 257727807600057471708365)
                  ·
                    rfl

theorem cell23_4517308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 5].length) (baseStart_4517308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517308 prefixEnd_4517308 := by exact prefixLift 4517308
  have htrace : WordTrace (prefixWord ++ tailWord_4517308) baseStart_4517308 baseEnd_4517308 := by
    simpa [prefixWord, tailWord_4517308, baseEnd_4517308] using wordTrace_append hprefix tailTrace_4517308
  have hstable : (prefixWord ++ tailWord_4517308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517308).length < 2 ^ (prefixWord ++ tailWord_4517308).sum := by decide
  have hdescent : baseEnd_4517308 < baseStart_4517308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517324 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 4, 1, 4]
def baseStart_4517324 : Nat := 118140960795 + 4517324 * 2 ^ 59
def prefixEnd_4517324 : Nat := 4983230072969 + 3 ^ 40 * 4517324 * 2
def baseEnd_4517324 : Nat := 2319558484090989182775211

theorem tailTrace_4517324 : CollatzResearch.WordTrace tailWord_4517324 prefixEnd_4517324 2319558484090989182775211 := by
  unfold tailWord_4517324
  simp only [CollatzResearch.WordTrace]
  refine ⟨82380170943257060181127513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109840227924342746908170017 82380170943257060181127513)
  ·
    refine ⟨61785128207442795135845635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82380170943257060181127513 61785128207442795135845635)
    ·
      refine ⟨92677692311164192703768453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61785128207442795135845635 92677692311164192703768453)
      ·
        refine ⟨17377067308343286131956585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92677692311164192703768453 17377067308343286131956585)
        ·
          refine ⟨13032800481257464598967439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17377067308343286131956585 13032800481257464598967439)
          ·
            refine ⟨19549200721886196898451159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13032800481257464598967439 19549200721886196898451159)
            ·
              refine ⟨29323801082829295347676739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19549200721886196898451159 29323801082829295347676739)
              ·
                refine ⟨43985701624243943021515109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29323801082829295347676739 43985701624243943021515109)
                ·
                  refine ⟨8247319054545739316534083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43985701624243943021515109 8247319054545739316534083)
                  ·
                    refine ⟨12370978581818608974801125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8247319054545739316534083 12370978581818608974801125)
                    ·
                      refine ⟨2319558484090989182775211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12370978581818608974801125 2319558484090989182775211)
                      ·
                        rfl

theorem cell23_4517324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_4517324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517324 prefixEnd_4517324 := by exact prefixLift 4517324
  have htrace : WordTrace (prefixWord ++ tailWord_4517324) baseStart_4517324 baseEnd_4517324 := by
    simpa [prefixWord, tailWord_4517324, baseEnd_4517324] using wordTrace_append hprefix tailTrace_4517324
  have hstable : (prefixWord ++ tailWord_4517324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517324).length < 2 ^ (prefixWord ++ tailWord_4517324).sum := by decide
  have hdescent : baseEnd_4517324 < baseStart_4517324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517361 : List Nat := [1, 2, 2, 2, 3, 3, 2, 1, 2, 2, 3]
def baseStart_4517361 : Nat := 118140960795 + 4517361 * 2 ^ 59
def prefixEnd_4517361 : Nat := 4983230072969 + 3 ^ 40 * 4517361 * 2
def baseEnd_4517361 : Nat := 2319577482875205538012541

theorem tailTrace_4517361 : CollatzResearch.WordTrace tailWord_4517361 prefixEnd_4517361 2319577482875205538012541 := by
  unfold tailWord_4517361
  simp only [CollatzResearch.WordTrace]
  refine ⟨164761691387380075681351937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109841127591586717120901291 164761691387380075681351937)
  ·
    refine ⟨123571268540535056761013953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164761691387380075681351937 123571268540535056761013953)
    ·
      refine ⟨92678451405401292570760465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123571268540535056761013953 92678451405401292570760465)
      ·
        refine ⟨69508838554050969428070349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92678451405401292570760465 69508838554050969428070349)
        ·
          refine ⟨26065814457769113535526381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69508838554050969428070349 26065814457769113535526381)
          ·
            refine ⟨9774680421663417575822393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26065814457769113535526381 9774680421663417575822393)
            ·
              refine ⟨7331010316247563181866795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9774680421663417575822393 7331010316247563181866795)
              ·
                refine ⟨10996515474371344772800193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7331010316247563181866795 10996515474371344772800193)
                ·
                  refine ⟨8247386605778508579600145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10996515474371344772800193 8247386605778508579600145)
                  ·
                    refine ⟨6185539954333881434700109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8247386605778508579600145 6185539954333881434700109)
                    ·
                      refine ⟨2319577482875205538012541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6185539954333881434700109 2319577482875205538012541)
                      ·
                        rfl

theorem cell23_4517361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_4517361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517361 prefixEnd_4517361 := by exact prefixLift 4517361
  have htrace : WordTrace (prefixWord ++ tailWord_4517361) baseStart_4517361 baseEnd_4517361 := by
    simpa [prefixWord, tailWord_4517361, baseEnd_4517361] using wordTrace_append hprefix tailTrace_4517361
  have hstable : (prefixWord ++ tailWord_4517361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517361).length < 2 ^ (prefixWord ++ tailWord_4517361).sum := by decide
  have hdescent : baseEnd_4517361 < baseStart_4517361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517378 : List Nat := [3, 4, 1, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_4517378 : Nat := 118140960795 + 4517378 * 2 ^ 59
def prefixEnd_4517378 : Nat := 4983230072969 + 3 ^ 40 * 4517378 * 2
def baseEnd_4517378 : Nat := 2319586212046331971499963

theorem tailTrace_4517378 : CollatzResearch.WordTrace tailWord_4517378 prefixEnd_4517378 2319586212046331971499963 := by
  unfold tailWord_4517378
  simp only [CollatzResearch.WordTrace]
  refine ⟨41190577857079621896180197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109841540952212325056480525 41190577857079621896180197)
  ·
    refine ⟨7723233348202429105533787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41190577857079621896180197 7723233348202429105533787)
    ·
      refine ⟨11584850022303643658300681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7723233348202429105533787 11584850022303643658300681)
      ·
        refine ⟨8688637516727732743725511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11584850022303643658300681 8688637516727732743725511)
        ·
          refine ⟨13032956275091599115588267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8688637516727732743725511 13032956275091599115588267)
          ·
            refine ⟨19549434412637398673382401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13032956275091599115588267 19549434412637398673382401)
            ·
              refine ⟨14662075809478049005036801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19549434412637398673382401 14662075809478049005036801)
              ·
                refine ⟨10996556857108536753777601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14662075809478049005036801 10996556857108536753777601)
                ·
                  refine ⟨8247417642831402565333201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10996556857108536753777601 8247417642831402565333201)
                  ·
                    refine ⟨6185563232123551923999901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8247417642831402565333201 6185563232123551923999901)
                    ·
                      refine ⟨2319586212046331971499963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6185563232123551923999901 2319586212046331971499963)
                      ·
                        rfl

theorem cell23_4517378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_4517378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517378 prefixEnd_4517378 := by exact prefixLift 4517378
  have htrace : WordTrace (prefixWord ++ tailWord_4517378) baseStart_4517378 baseEnd_4517378 := by
    simpa [prefixWord, tailWord_4517378, baseEnd_4517378] using wordTrace_append hprefix tailTrace_4517378
  have hstable : (prefixWord ++ tailWord_4517378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517378).length < 2 ^ (prefixWord ++ tailWord_4517378).sum := by decide
  have hdescent : baseEnd_4517378 < baseStart_4517378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517408 : List Nat := [2, 1, 1, 6, 1, 2, 1, 2, 3, 1, 3]
def baseStart_4517408 : Nat := 118140960795 + 4517408 * 2 ^ 59
def prefixEnd_4517408 : Nat := 4983230072969 + 3 ^ 40 * 4517408 * 2
def baseEnd_4517408 : Nat := 2319601616465966854124825

theorem tailTrace_4517408 : CollatzResearch.WordTrace tailWord_4517408 prefixEnd_4517408 2319601616465966854124825 := by
  unfold tailWord_4517408
  simp only [CollatzResearch.WordTrace]
  refine ⟨82381702809104901354156439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109842270412139868472208585 82381702809104901354156439)
  ·
    refine ⟨123572554213657352031234659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82381702809104901354156439 123572554213657352031234659)
    ·
      refine ⟨185358831320486028046851989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123572554213657352031234659 185358831320486028046851989)
      ·
        refine ⟨8688695218147782564696187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 185358831320486028046851989 8688695218147782564696187)
        ·
          refine ⟨13033042827221673847044281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8688695218147782564696187 13033042827221673847044281)
          ·
            refine ⟨9774782120416255385283211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13033042827221673847044281 9774782120416255385283211)
            ·
              refine ⟨14662173180624383077924817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9774782120416255385283211 14662173180624383077924817)
              ·
                refine ⟨10996629885468287308443613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14662173180624383077924817 10996629885468287308443613)
                ·
                  refine ⟨4123736207050607740666355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10996629885468287308443613 4123736207050607740666355)
                  ·
                    refine ⟨6185604310575911610999533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4123736207050607740666355 6185604310575911610999533)
                    ·
                      refine ⟨2319601616465966854124825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6185604310575911610999533 2319601616465966854124825)
                      ·
                        rfl

theorem cell23_4517408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_4517408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517408 prefixEnd_4517408 := by exact prefixLift 4517408
  have htrace : WordTrace (prefixWord ++ tailWord_4517408) baseStart_4517408 baseEnd_4517408 := by
    simpa [prefixWord, tailWord_4517408, baseEnd_4517408] using wordTrace_append hprefix tailTrace_4517408
  have hstable : (prefixWord ++ tailWord_4517408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517408).length < 2 ^ (prefixWord ++ tailWord_4517408).sum := by decide
  have hdescent : baseEnd_4517408 < baseStart_4517408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517424 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 4, 4]
def baseStart_4517424 : Nat := 118140960795 + 4517424 * 2 ^ 59
def prefixEnd_4517424 : Nat := 4983230072969 + 3 ^ 40 * 4517424 * 2
def baseEnd_4517424 : Nat := 773203277385479597174917

theorem tailTrace_4517424 : CollatzResearch.WordTrace tailWord_4517424 prefixEnd_4517424 773203277385479597174917 := by
  unfold tailWord_4517424
  simp only [CollatzResearch.WordTrace]
  refine ⟨82381994593075918720447663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109842659457434558293930217 82381994593075918720447663)
  ·
    refine ⟨123572991889613878080671495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82381994593075918720447663 123572991889613878080671495)
    ·
      refine ⟨185359487834420817121007243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123572991889613878080671495 185359487834420817121007243)
      ·
        refine ⟨278039231751631225681510865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185359487834420817121007243 278039231751631225681510865)
        ·
          refine ⟨208529423813723419261133149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278039231751631225681510865 208529423813723419261133149)
          ·
            refine ⟨78198533930146282222924931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208529423813723419261133149 78198533930146282222924931)
            ·
              refine ⟨117297800895219423334387397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78198533930146282222924931 117297800895219423334387397)
              ·
                refine ⟨21993337667853641875197637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117297800895219423334387397 21993337667853641875197637)
                ·
                  refine ⟨4123750812722557851599557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21993337667853641875197637 4123750812722557851599557)
                  ·
                    refine ⟨773203277385479597174917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4123750812722557851599557 773203277385479597174917)
                    ·
                      rfl

theorem cell23_4517424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 4, 4].length) (baseStart_4517424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517424 prefixEnd_4517424 := by exact prefixLift 4517424
  have htrace : WordTrace (prefixWord ++ tailWord_4517424) baseStart_4517424 baseEnd_4517424 := by
    simpa [prefixWord, tailWord_4517424, baseEnd_4517424] using wordTrace_append hprefix tailTrace_4517424
  have hstable : (prefixWord ++ tailWord_4517424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517424).length < 2 ^ (prefixWord ++ tailWord_4517424).sum := by decide
  have hdescent : baseEnd_4517424 < baseStart_4517424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517431 : List Nat := [1, 1, 3, 1, 2, 5, 1, 3, 1, 1, 4]
def baseStart_4517431 : Nat := 118140960795 + 4517431 * 2 ^ 59
def prefixEnd_4517431 : Nat := 4983230072969 + 3 ^ 40 * 4517431 * 2
def baseEnd_4517431 : Nat := 2319613426521020264137219

theorem tailTrace_4517431 : CollatzResearch.WordTrace tailWord_4517431 prefixEnd_4517431 2319613426521020264137219 := by
  unfold tailWord_4517431
  simp only [CollatzResearch.WordTrace]
  refine ⟨164764244497126477636400147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109842829664750985090933431 164764244497126477636400147)
  ·
    refine ⟨247146366745689716454600221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164764244497126477636400147 247146366745689716454600221)
    ·
      refine ⟨92679887529633643670475083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247146366745689716454600221 92679887529633643670475083)
      ·
        refine ⟨139019831294450465505712625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92679887529633643670475083 139019831294450465505712625)
        ·
          refine ⟨104264873470837849129284469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139019831294450465505712625 104264873470837849129284469)
          ·
            refine ⟨9774831887891048355870419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104264873470837849129284469 9774831887891048355870419)
            ·
              refine ⟨14662247831836572533805629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9774831887891048355870419 14662247831836572533805629)
              ·
                refine ⟨5498342936938714700177111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14662247831836572533805629 5498342936938714700177111)
                ·
                  refine ⟨8247514405408072050265667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5498342936938714700177111 8247514405408072050265667)
                  ·
                    refine ⟨12371271608112108075398501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8247514405408072050265667 12371271608112108075398501)
                    ·
                      refine ⟨2319613426521020264137219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12371271608112108075398501 2319613426521020264137219)
                      ·
                        rfl

theorem cell23_4517431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 1, 4].length) (baseStart_4517431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517431 prefixEnd_4517431 := by exact prefixLift 4517431
  have htrace : WordTrace (prefixWord ++ tailWord_4517431) baseStart_4517431 baseEnd_4517431 := by
    simpa [prefixWord, tailWord_4517431, baseEnd_4517431] using wordTrace_append hprefix tailTrace_4517431
  have hstable : (prefixWord ++ tailWord_4517431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517431).length < 2 ^ (prefixWord ++ tailWord_4517431).sum := by decide
  have hdescent : baseEnd_4517431 < baseStart_4517431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517434 : List Nat := [3, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5]
def baseStart_4517434 : Nat := 118140960795 + 4517434 * 2 ^ 59
def prefixEnd_4517434 : Nat := 4983230072969 + 3 ^ 40 * 4517434 * 2
def baseEnd_4517434 : Nat := 2319614966962983752399705

theorem tailTrace_4517434 : CollatzResearch.WordTrace tailWord_4517434 prefixEnd_4517434 2319614966962983752399705 := by
  unfold tailWord_4517434
  simp only [CollatzResearch.WordTrace]
  refine ⟨41191088479028902287189839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109842902610743739432506237 41191088479028902287189839)
  ·
    refine ⟨61786632718543353430784759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41191088479028902287189839 61786632718543353430784759)
    ·
      refine ⟨92679949077815030146177139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61786632718543353430784759 92679949077815030146177139)
      ·
        refine ⟨139019923616722545219265709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92679949077815030146177139 139019923616722545219265709)
        ·
          refine ⟨52132471356270954457224641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139019923616722545219265709 52132471356270954457224641)
          ·
            refine ⟨39099353517203215842918481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52132471356270954457224641 39099353517203215842918481)
            ·
              refine ⟨29324515137902411882188861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39099353517203215842918481 29324515137902411882188861)
              ·
                refine ⟨10996693176713404455820823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29324515137902411882188861 10996693176713404455820823)
                ·
                  refine ⟨16495039765070106683731235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10996693176713404455820823 16495039765070106683731235)
                  ·
                    refine ⟨24742559647605160025596853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16495039765070106683731235 24742559647605160025596853)
                    ·
                      refine ⟨2319614966962983752399705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24742559647605160025596853 2319614966962983752399705)
                      ·
                        rfl

theorem cell23_4517434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_4517434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517434 prefixEnd_4517434 := by exact prefixLift 4517434
  have htrace : WordTrace (prefixWord ++ tailWord_4517434) baseStart_4517434 baseEnd_4517434 := by
    simpa [prefixWord, tailWord_4517434, baseEnd_4517434] using wordTrace_append hprefix tailTrace_4517434
  have hstable : (prefixWord ++ tailWord_4517434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517434).length < 2 ^ (prefixWord ++ tailWord_4517434).sum := by decide
  have hdescent : baseEnd_4517434 < baseStart_4517434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517441 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 4, 4]
def baseStart_4517441 : Nat := 118140960795 + 4517441 * 2 ^ 59
def prefixEnd_4517441 : Nat := 4983230072969 + 3 ^ 40 * 4517441 * 2
def baseEnd_4517441 : Nat := 773206187109188408337391

theorem tailTrace_4517441 : CollatzResearch.WordTrace tailWord_4517441 prefixEnd_4517441 773206187109188408337391 := by
  unfold tailWord_4517441
  simp only [CollatzResearch.WordTrace]
  refine ⟨164764609227090249344264177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109843072818060166229509451 164764609227090249344264177)
  ·
    refine ⟨123573456920317687008198133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164764609227090249344264177 123573456920317687008198133)
    ·
      refine ⟨11585011586279783157018575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123573456920317687008198133 11585011586279783157018575)
      ·
        refine ⟨17377517379419674735527863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11585011586279783157018575 17377517379419674735527863)
        ·
          refine ⟨26066276069129512103291795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17377517379419674735527863 26066276069129512103291795)
          ·
            refine ⟨39099414103694268154937693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26066276069129512103291795 39099414103694268154937693)
            ·
              refine ⟨14662280288885350558101635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39099414103694268154937693 14662280288885350558101635)
              ·
                refine ⟨21993420433328025837152453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14662280288885350558101635 21993420433328025837152453)
                ·
                  refine ⟨4123766331249004844466085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21993420433328025837152453 4123766331249004844466085)
                  ·
                    refine ⟨773206187109188408337391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4123766331249004844466085 773206187109188408337391)
                    ·
                      rfl

theorem cell23_4517441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_4517441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517441 prefixEnd_4517441 := by exact prefixLift 4517441
  have htrace : WordTrace (prefixWord ++ tailWord_4517441) baseStart_4517441 baseEnd_4517441 := by
    simpa [prefixWord, tailWord_4517441, baseEnd_4517441] using wordTrace_append hprefix tailTrace_4517441
  have hstable : (prefixWord ++ tailWord_4517441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517441).length < 2 ^ (prefixWord ++ tailWord_4517441).sum := by decide
  have hdescent : baseEnd_4517441 < baseStart_4517441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517462 : List Nat := [5, 2, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_4517462 : Nat := 118140960795 + 4517462 * 2 ^ 59
def prefixEnd_4517462 : Nat := 4983230072969 + 3 ^ 40 * 4517462 * 2
def baseEnd_4517462 : Nat := 773209781473769880949859

theorem tailTrace_4517462 : CollatzResearch.WordTrace tailWord_4517462 prefixEnd_4517462 773209781473769880949859 := by
  unfold tailWord_4517462
  simp only [CollatzResearch.WordTrace]
  refine ⟨10297835947500885620673665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109843583440009446620519093 10297835947500885620673665)
  ·
    refine ⟨7723376960625664215505249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10297835947500885620673665 7723376960625664215505249)
    ·
      refine ⟨5792532720469248161628937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7723376960625664215505249 5792532720469248161628937)
      ·
        refine ⟨4344399540351936121221703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5792532720469248161628937 4344399540351936121221703)
        ·
          refine ⟨6516599310527904181832555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4344399540351936121221703 6516599310527904181832555)
          ·
            refine ⟨9774898965791856272748833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6516599310527904181832555 9774898965791856272748833)
            ·
              refine ⟨7331174224343892204561625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9774898965791856272748833 7331174224343892204561625)
              ·
                refine ⟨5498380668257919153421219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7331174224343892204561625 5498380668257919153421219)
                ·
                  refine ⟨8247571002386878730131829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5498380668257919153421219 8247571002386878730131829)
                  ·
                    refine ⟨773209781473769880949859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8247571002386878730131829 773209781473769880949859)
                    ·
                      rfl

theorem cell23_4517462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_4517462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517462 prefixEnd_4517462 := by exact prefixLift 4517462
  have htrace : WordTrace (prefixWord ++ tailWord_4517462) baseStart_4517462 baseEnd_4517462 := by
    simpa [prefixWord, tailWord_4517462, baseEnd_4517462] using wordTrace_append hprefix tailTrace_4517462
  have hstable : (prefixWord ++ tailWord_4517462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517462).length < 2 ^ (prefixWord ++ tailWord_4517462).sum := by decide
  have hdescent : baseEnd_4517462 < baseStart_4517462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517468 : List Nat := [2, 2, 4, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_4517468 : Nat := 118140960795 + 4517468 * 2 ^ 59
def prefixEnd_4517468 : Nat := 4983230072969 + 3 ^ 40 * 4517468 * 2
def baseEnd_4517468 : Nat := 2319632425305236619374549

theorem tailTrace_4517468 : CollatzResearch.WordTrace tailWord_4517468 prefixEnd_4517468 2319632425305236619374549 := by
  unfold tailWord_4517468
  simp only [CollatzResearch.WordTrace]
  refine ⟨82382796998996216477748529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109843729331994955303664705 82382796998996216477748529)
  ·
    refine ⟨61787097749247162358311397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82382796998996216477748529 61787097749247162358311397)
    ·
      refine ⟨11585080827983842942183387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61787097749247162358311397 11585080827983842942183387)
      ·
        refine ⟨17377621241975764413275081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11585080827983842942183387 17377621241975764413275081)
        ·
          refine ⟨13033215931481823309956311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17377621241975764413275081 13033215931481823309956311)
          ·
            refine ⟨19549823897222734964934467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13033215931481823309956311 19549823897222734964934467)
            ·
              refine ⟨29324735845834102447401701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19549823897222734964934467 29324735845834102447401701)
              ·
                refine ⟨5498387971093894208887819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29324735845834102447401701 5498387971093894208887819)
                ·
                  refine ⟨8247581956640841313331729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5498387971093894208887819 8247581956640841313331729)
                  ·
                    refine ⟨6185686467480630984998797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8247581956640841313331729 6185686467480630984998797)
                    ·
                      refine ⟨2319632425305236619374549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6185686467480630984998797 2319632425305236619374549)
                      ·
                        rfl

theorem cell23_4517468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_4517468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517468 prefixEnd_4517468 := by exact prefixLift 4517468
  have htrace : WordTrace (prefixWord ++ tailWord_4517468) baseStart_4517468 baseEnd_4517468 := by
    simpa [prefixWord, tailWord_4517468, baseEnd_4517468] using wordTrace_append hprefix tailTrace_4517468
  have hstable : (prefixWord ++ tailWord_4517468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517468).length < 2 ^ (prefixWord ++ tailWord_4517468).sum := by decide
  have hdescent : baseEnd_4517468 < baseStart_4517468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517481 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 4, 1, 3]
def baseStart_4517481 : Nat := 118140960795 + 4517481 * 2 ^ 59
def prefixEnd_4517481 : Nat := 4983230072969 + 3 ^ 40 * 4517481 * 2
def baseEnd_4517481 : Nat := 2319639100553745068511989

theorem tailTrace_4517481 : CollatzResearch.WordTrace tailWord_4517481 prefixEnd_4517481 2319639100553745068511989 := by
  unfold tailWord_4517481
  simp only [CollatzResearch.WordTrace]
  refine ⟨164766068146945336175720297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109844045431296890783813531 164766068146945336175720297)
  ·
    refine ⟨123574551110209002131790223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164766068146945336175720297 123574551110209002131790223)
    ·
      refine ⟨185361826665313503197685335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123574551110209002131790223 185361826665313503197685335)
      ·
        refine ⟨278042739997970254796528003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185361826665313503197685335 278042739997970254796528003)
        ·
          refine ⟨417064109996955382194792005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278042739997970254796528003 417064109996955382194792005)
          ·
            refine ⟨78199520624429134161523501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 417064109996955382194792005 78199520624429134161523501)
            ·
              refine ⟨29324820234160925310571313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78199520624429134161523501 29324820234160925310571313)
              ·
                refine ⟨21993615175620693982928485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29324820234160925310571313 21993615175620693982928485)
                ·
                  refine ⟨4123802845428880121799091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21993615175620693982928485 4123802845428880121799091)
                  ·
                    refine ⟨6185704268143320182698637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4123802845428880121799091 6185704268143320182698637)
                    ·
                      refine ⟨2319639100553745068511989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6185704268143320182698637 2319639100553745068511989)
                      ·
                        rfl

theorem cell23_4517481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 1, 3].length) (baseStart_4517481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517481 prefixEnd_4517481 := by exact prefixLift 4517481
  have htrace : WordTrace (prefixWord ++ tailWord_4517481) baseStart_4517481 baseEnd_4517481 := by
    simpa [prefixWord, tailWord_4517481, baseEnd_4517481] using wordTrace_append hprefix tailTrace_4517481
  have hstable : (prefixWord ++ tailWord_4517481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517481).length < 2 ^ (prefixWord ++ tailWord_4517481).sum := by decide
  have hdescent : baseEnd_4517481 < baseStart_4517481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517482 : List Nat := [3, 1, 3, 2, 1, 2, 3, 3, 1, 2, 2]
def baseStart_4517482 : Nat := 118140960795 + 4517482 * 2 ^ 59
def prefixEnd_4517482 : Nat := 4983230072969 + 3 ^ 40 * 4517482 * 2
def baseEnd_4517482 : Nat := 2319639614034399564599485

theorem tailTrace_4517482 : CollatzResearch.WordTrace tailWord_4517482 prefixEnd_4517482 2319639614034399564599485 := by
  unfold tailWord_4517482
  simp only [CollatzResearch.WordTrace]
  refine ⟨41191526154985428336626675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109844069746627808897671133 41191526154985428336626675)
  ·
    refine ⟨61787289232478142504940013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41191526154985428336626675 61787289232478142504940013)
    ·
      refine ⟨23170233462179303439352505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61787289232478142504940013 23170233462179303439352505)
      ·
        refine ⟨17377675096634477579514379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23170233462179303439352505 17377675096634477579514379)
        ·
          refine ⟨26066512644951716369271569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17377675096634477579514379 26066512644951716369271569)
          ·
            refine ⟨19549884483713787276953677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26066512644951716369271569 19549884483713787276953677)
            ·
              refine ⟨7331206681392670228857629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19549884483713787276953677 7331206681392670228857629)
              ·
                refine ⟨2749202505522251335821611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7331206681392670228857629 2749202505522251335821611)
                ·
                  refine ⟨4123803758283377003732417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2749202505522251335821611 4123803758283377003732417)
                  ·
                    refine ⟨3092852818712532752799313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4123803758283377003732417 3092852818712532752799313)
                    ·
                      refine ⟨2319639614034399564599485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3092852818712532752799313 2319639614034399564599485)
                      ·
                        rfl

theorem cell23_4517482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_4517482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517482 prefixEnd_4517482 := by exact prefixLift 4517482
  have htrace : WordTrace (prefixWord ++ tailWord_4517482) baseStart_4517482 baseEnd_4517482 := by
    simpa [prefixWord, tailWord_4517482, baseEnd_4517482] using wordTrace_append hprefix tailTrace_4517482
  have hstable : (prefixWord ++ tailWord_4517482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517482).length < 2 ^ (prefixWord ++ tailWord_4517482).sum := by decide
  have hdescent : baseEnd_4517482 < baseStart_4517482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517504 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 4]
def baseStart_4517504 : Nat := 118140960795 + 4517504 * 2 ^ 59
def prefixEnd_4517504 : Nat := 4983230072969 + 3 ^ 40 * 4517504 * 2
def baseEnd_4517504 : Nat := 2319650910608798478524383

theorem tailTrace_4517504 : CollatzResearch.WordTrace tailWord_4517504 prefixEnd_4517504 2319650910608798478524383 := by
  unfold tailWord_4517504
  simp only [CollatzResearch.WordTrace]
  refine ⟨82383453512931005551903783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109844604683908007402538377 82383453512931005551903783)
  ·
    refine ⟨123575180269396508327855675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82383453512931005551903783 123575180269396508327855675)
    ·
      refine ⟨185362770404094762491783513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123575180269396508327855675 185362770404094762491783513)
      ·
        refine ⟨139022077803071071868837635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185362770404094762491783513 139022077803071071868837635)
        ·
          refine ⟨208533116704606607803256453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139022077803071071868837635 208533116704606607803256453)
          ·
            refine ⟨39099959382113738963110585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 208533116704606607803256453 39099959382113738963110585)
            ·
              refine ⟨29324969536585304222332939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39099959382113738963110585 29324969536585304222332939)
              ·
                refine ⟨43987454304877956333499409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29324969536585304222332939 43987454304877956333499409)
                ·
                  refine ⟨32990590728658467250124557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43987454304877956333499409 32990590728658467250124557)
                  ·
                    refine ⟨12371471523246925218796709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32990590728658467250124557 12371471523246925218796709)
                    ·
                      refine ⟨2319650910608798478524383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12371471523246925218796709 2319650910608798478524383)
                      ·
                        rfl

theorem cell23_4517504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_4517504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517504 prefixEnd_4517504 := by exact prefixLift 4517504
  have htrace : WordTrace (prefixWord ++ tailWord_4517504) baseStart_4517504 baseEnd_4517504 := by
    simpa [prefixWord, tailWord_4517504, baseEnd_4517504] using wordTrace_append hprefix tailTrace_4517504
  have hstable : (prefixWord ++ tailWord_4517504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517504).length < 2 ^ (prefixWord ++ tailWord_4517504).sum := by decide
  have hdescent : baseEnd_4517504 < baseStart_4517504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517554 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7]
def baseStart_4517554 : Nat := 118140960795 + 4517554 * 2 ^ 59
def prefixEnd_4517554 : Nat := 4983230072969 + 3 ^ 40 * 4517554 * 2
def baseEnd_4517554 : Nat := 2319676584641523282899153

theorem tailTrace_4517554 : CollatzResearch.WordTrace tailWord_4517554 prefixEnd_4517554 2319676584641523282899153 := by
  unfold tailWord_4517554
  simp only [CollatzResearch.WordTrace]
  refine ⟨41192182668920217410781929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109845820450453913095418477 41192182668920217410781929)
  ·
    refine ⟨30894137001690163058086447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41192182668920217410781929 30894137001690163058086447)
    ·
      refine ⟨46341205502535244587129671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30894137001690163058086447 46341205502535244587129671)
      ·
        refine ⟨69511808253802866880694507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46341205502535244587129671 69511808253802866880694507)
        ·
          refine ⟨104267712380704300321041761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69511808253802866880694507 104267712380704300321041761)
          ·
            refine ⟨78200784285528225240781321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104267712380704300321041761 78200784285528225240781321)
            ·
              refine ⟨58650588214146168930585991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78200784285528225240781321 58650588214146168930585991)
              ·
                refine ⟨87975882321219253395878987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58650588214146168930585991 87975882321219253395878987)
                ·
                  refine ⟨131963823481828880093818481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87975882321219253395878987 131963823481828880093818481)
                  ·
                    refine ⟨98972867611371660070363861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 131963823481828880093818481 98972867611371660070363861)
                    ·
                      refine ⟨2319676584641523282899153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98972867611371660070363861 2319676584641523282899153)
                      ·
                        rfl

theorem cell23_4517554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_4517554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517554 prefixEnd_4517554 := by exact prefixLift 4517554
  have htrace : WordTrace (prefixWord ++ tailWord_4517554) baseStart_4517554 baseEnd_4517554 := by
    simpa [prefixWord, tailWord_4517554, baseEnd_4517554] using wordTrace_append hprefix tailTrace_4517554
  have hstable : (prefixWord ++ tailWord_4517554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517554).length < 2 ^ (prefixWord ++ tailWord_4517554).sum := by decide
  have hdescent : baseEnd_4517554 < baseStart_4517554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517555 : List Nat := [1, 1, 1, 2, 3, 3, 4, 2, 2, 2, 2]
def baseStart_4517555 : Nat := 118140960795 + 4517555 * 2 ^ 59
def prefixEnd_4517555 : Nat := 4983230072969 + 3 ^ 40 * 4517555 * 2
def baseEnd_4517555 : Nat := 2319677098122177778986649

theorem tailTrace_4517555 : CollatzResearch.WordTrace tailWord_4517555 prefixEnd_4517555 2319677098122177778986649 := by
  unfold tailWord_4517555
  simp only [CollatzResearch.WordTrace]
  refine ⟨164768767148677246813914119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109845844765784831209276079 164768767148677246813914119)
  ·
    refine ⟨247153150723015870220871179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164768767148677246813914119 247153150723015870220871179)
    ·
      refine ⟨370729726084523805331306769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247153150723015870220871179 370729726084523805331306769)
      ·
        refine ⟨278047294563392853998480077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 370729726084523805331306769 278047294563392853998480077)
        ·
          refine ⟨104267735461272320249430029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 278047294563392853998480077 104267735461272320249430029)
          ·
            refine ⟨39100400797977120093536261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104267735461272320249430029 39100400797977120093536261)
            ·
              refine ⟨7331325149620710017538049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39100400797977120093536261 7331325149620710017538049)
              ·
                refine ⟨5498493862215532513153537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7331325149620710017538049 5498493862215532513153537)
                ·
                  refine ⟨4123870396661649384865153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5498493862215532513153537 4123870396661649384865153)
                  ·
                    refine ⟨3092902797496237038648865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4123870396661649384865153 3092902797496237038648865)
                    ·
                      refine ⟨2319677098122177778986649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3092902797496237038648865 2319677098122177778986649)
                      ·
                        rfl

theorem cell23_4517555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 2, 2].length) (baseStart_4517555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517555 prefixEnd_4517555 := by exact prefixLift 4517555
  have htrace : WordTrace (prefixWord ++ tailWord_4517555) baseStart_4517555 baseEnd_4517555 := by
    simpa [prefixWord, tailWord_4517555, baseEnd_4517555] using wordTrace_append hprefix tailTrace_4517555
  have hstable : (prefixWord ++ tailWord_4517555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517555).length < 2 ^ (prefixWord ++ tailWord_4517555).sum := by decide
  have hdescent : baseEnd_4517555 < baseStart_4517555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517584 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 5]
def baseStart_4517584 : Nat := 118140960795 + 4517584 * 2 ^ 59
def prefixEnd_4517584 : Nat := 4983230072969 + 3 ^ 40 * 4517584 * 2
def baseEnd_4517584 : Nat := 2319691989061158165524015

theorem tailTrace_4517584 : CollatzResearch.WordTrace tailWord_4517584 prefixEnd_4517584 2319691989061158165524015 := by
  unfold tailWord_4517584
  simp only [CollatzResearch.WordTrace]
  refine ⟨82384912432786092383359903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109846549910381456511146537 82384912432786092383359903)
  ·
    refine ⟨123577368649179138575039855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82384912432786092383359903 123577368649179138575039855)
    ·
      refine ⟨185366052973768707862559783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123577368649179138575039855 185366052973768707862559783)
      ·
        refine ⟨278049079460653061793839675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185366052973768707862559783 278049079460653061793839675)
        ·
          refine ⟨417073619190979592690759513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278049079460653061793839675 417073619190979592690759513)
          ·
            refine ⟨312805214393234694518069635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 417073619190979592690759513 312805214393234694518069635)
            ·
              refine ⟨469207821589852041777104453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312805214393234694518069635 469207821589852041777104453)
              ·
                refine ⟨87976466548097257833207085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 469207821589852041777104453 87976466548097257833207085)
                ·
                  refine ⟨32991174955536471687452657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87976466548097257833207085 32991174955536471687452657)
                  ·
                    refine ⟨24743381216652353765589493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32991174955536471687452657 24743381216652353765589493)
                    ·
                      refine ⟨2319691989061158165524015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24743381216652353765589493 2319691989061158165524015)
                      ·
                        rfl

theorem cell23_4517584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_4517584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517584 prefixEnd_4517584 := by exact prefixLift 4517584
  have htrace : WordTrace (prefixWord ++ tailWord_4517584) baseStart_4517584 baseEnd_4517584 := by
    simpa [prefixWord, tailWord_4517584, baseEnd_4517584] using wordTrace_append hprefix tailTrace_4517584
  have hstable : (prefixWord ++ tailWord_4517584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517584).length < 2 ^ (prefixWord ++ tailWord_4517584).sum := by decide
  have hdescent : baseEnd_4517584 < baseStart_4517584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517611 : List Nat := [1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 4]
def baseStart_4517611 : Nat := 118140960795 + 4517611 * 2 ^ 59
def prefixEnd_4517611 : Nat := 4983230072969 + 3 ^ 40 * 4517611 * 2
def baseEnd_4517611 : Nat := 2319705853038829559886391

theorem tailTrace_4517611 : CollatzResearch.WordTrace tailWord_4517611 prefixEnd_4517611 2319705853038829559886391 := by
  unfold tailWord_4517611
  simp only [CollatzResearch.WordTrace]
  refine ⟨164770809636474368377952687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109847206424316245585301791 164770809636474368377952687)
  ·
    refine ⟨247156214454711552566929031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164770809636474368377952687 247156214454711552566929031)
    ·
      refine ⟨370734321682067328850393547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247156214454711552566929031 370734321682067328850393547)
      ·
        refine ⟨556101482523100993275590321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370734321682067328850393547 556101482523100993275590321)
        ·
          refine ⟨417076111892325744956692741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 556101482523100993275590321 417076111892325744956692741)
          ·
            refine ⟨78201770979811077179379889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 417076111892325744956692741 78201770979811077179379889)
            ·
              refine ⟨58651328234858307884534917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78201770979811077179379889 58651328234858307884534917)
              ·
                refine ⟨10997124044035932728350297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58651328234858307884534917 10997124044035932728350297)
                ·
                  refine ⟨8247843033026949546262723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10997124044035932728350297 8247843033026949546262723)
                  ·
                    refine ⟨12371764549540424319394085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8247843033026949546262723 12371764549540424319394085)
                    ·
                      refine ⟨2319705853038829559886391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12371764549540424319394085 2319705853038829559886391)
                      ·
                        rfl

theorem cell23_4517611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 4].length) (baseStart_4517611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517611 prefixEnd_4517611 := by exact prefixLift 4517611
  have htrace : WordTrace (prefixWord ++ tailWord_4517611) baseStart_4517611 baseEnd_4517611 := by
    simpa [prefixWord, tailWord_4517611, baseEnd_4517611] using wordTrace_append hprefix tailTrace_4517611
  have hstable : (prefixWord ++ tailWord_4517611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517611).length < 2 ^ (prefixWord ++ tailWord_4517611).sum := by decide
  have hdescent : baseEnd_4517611 < baseStart_4517611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517628 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 2, 4, 2]
def baseStart_4517628 : Nat := 118140960795 + 4517628 * 2 ^ 59
def prefixEnd_4517628 : Nat := 4983230072969 + 3 ^ 40 * 4517628 * 2
def baseEnd_4517628 : Nat := 2319714582209955993373813

theorem tailTrace_4517628 : CollatzResearch.WordTrace tailWord_4517628 prefixEnd_4517628 2319714582209955993373813 := by
  unfold tailWord_4517628
  simp only [CollatzResearch.WordTrace]
  refine ⟨82385714838706390140660769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109847619784941853520881025 82385714838706390140660769)
  ·
    refine ⟨61789286129029792605495577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82385714838706390140660769 61789286129029792605495577)
    ·
      refine ⟨46341964596772344454121683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61789286129029792605495577 46341964596772344454121683)
      ·
        refine ⟨69512946895158516681182525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46341964596772344454121683 69512946895158516681182525)
        ·
          refine ⟨26067355085684443755443447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69512946895158516681182525 26067355085684443755443447)
          ·
            refine ⟨39101032628526665633165171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26067355085684443755443447 39101032628526665633165171)
            ·
              refine ⟨58651548942789998449747757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39101032628526665633165171 58651548942789998449747757)
              ·
                refine ⟨21994330853546249418655409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58651548942789998449747757 21994330853546249418655409)
                ·
                  refine ⟨16495748140159687063991557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21994330853546249418655409 16495748140159687063991557)
                  ·
                    refine ⟨3092952776279941324498417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16495748140159687063991557 3092952776279941324498417)
                    ·
                      refine ⟨2319714582209955993373813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3092952776279941324498417 2319714582209955993373813)
                      ·
                        rfl

theorem cell23_4517628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 2, 4, 2].length) (baseStart_4517628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517628 prefixEnd_4517628 := by exact prefixLift 4517628
  have htrace : WordTrace (prefixWord ++ tailWord_4517628) baseStart_4517628 baseEnd_4517628 := by
    simpa [prefixWord, tailWord_4517628, baseEnd_4517628] using wordTrace_append hprefix tailTrace_4517628
  have hstable : (prefixWord ++ tailWord_4517628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517628).length < 2 ^ (prefixWord ++ tailWord_4517628).sum := by decide
  have hdescent : baseEnd_4517628 < baseStart_4517628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517631 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 3]
def baseStart_4517631 : Nat := 118140960795 + 4517631 * 2 ^ 59
def prefixEnd_4517631 : Nat := 4983230072969 + 3 ^ 40 * 4517631 * 2
def baseEnd_4517631 : Nat := 2319716122651919481636299

theorem tailTrace_4517631 : CollatzResearch.WordTrace tailWord_4517631 prefixEnd_4517631 2319716122651919481636299 := by
  unfold tailWord_4517631
  simp only [CollatzResearch.WordTrace]
  refine ⟨164771539096401911793680747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109847692730934607862453831 164771539096401911793680747)
  ·
    refine ⟨247157308644602867690521121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164771539096401911793680747 247157308644602867690521121)
    ·
      refine ⟨185367981483452150767890841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247157308644602867690521121 185367981483452150767890841)
      ·
        refine ⟨139025986112589113075918131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185367981483452150767890841 139025986112589113075918131)
        ·
          refine ⟨208538979168883669613877197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139025986112589113075918131 208538979168883669613877197)
          ·
            refine ⟨78202117188331376105203949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208538979168883669613877197 78202117188331376105203949)
            ·
              refine ⟨29325793945624266039451481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78202117188331376105203949 29325793945624266039451481)
              ·
                refine ⟨21994345459218199529588611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29325793945624266039451481 21994345459218199529588611)
                ·
                  refine ⟨32991518188827299294382917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21994345459218199529588611 32991518188827299294382917)
                  ·
                    refine ⟨6185909660405118617696797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32991518188827299294382917 6185909660405118617696797)
                    ·
                      refine ⟨2319716122651919481636299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6185909660405118617696797 2319716122651919481636299)
                      ·
                        rfl

theorem cell23_4517631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 3].length) (baseStart_4517631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517631 prefixEnd_4517631 := by exact prefixLift 4517631
  have htrace : WordTrace (prefixWord ++ tailWord_4517631) baseStart_4517631 baseEnd_4517631 := by
    simpa [prefixWord, tailWord_4517631, baseEnd_4517631] using wordTrace_append hprefix tailTrace_4517631
  have hstable : (prefixWord ++ tailWord_4517631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517631).length < 2 ^ (prefixWord ++ tailWord_4517631).sum := by decide
  have hdescent : baseEnd_4517631 < baseStart_4517631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517705 : List Nat := [1, 2, 1, 1, 2, 4, 4, 1, 2, 3, 2]
def baseStart_4517705 : Nat := 118140960795 + 4517705 * 2 ^ 59
def prefixEnd_4517705 : Nat := 4983230072969 + 3 ^ 40 * 4517705 * 2
def baseEnd_4517705 : Nat := 2319754120220352192110959

theorem tailTrace_4517705 : CollatzResearch.WordTrace tailWord_4517705 prefixEnd_4517705 2319754120220352192110959 := by
  unfold tailWord_4517705
  simp only [CollatzResearch.WordTrace]
  refine ⟨164774238098133822431874569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109849492065422548287916379 164774238098133822431874569)
  ·
    refine ⟨123580678573600366823905927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164774238098133822431874569 123580678573600366823905927)
    ·
      refine ⟨185371017860400550235858891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123580678573600366823905927 185371017860400550235858891)
      ·
        refine ⟨278056526790600825353788337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185371017860400550235858891 278056526790600825353788337)
        ·
          refine ⟨208542395092950619015341253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278056526790600825353788337 208542395092950619015341253)
          ·
            refine ⟨39101699079928241065376485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 208542395092950619015341253 39101699079928241065376485)
            ·
              refine ⟨7331568577486545199758091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39101699079928241065376485 7331568577486545199758091)
              ·
                refine ⟨10997352866229817799637137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7331568577486545199758091 10997352866229817799637137)
                ·
                  refine ⟨8248014649672363349727853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10997352866229817799637137 8248014649672363349727853)
                  ·
                    refine ⟨3093005493627136256147945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8248014649672363349727853 3093005493627136256147945)
                    ·
                      refine ⟨2319754120220352192110959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3093005493627136256147945 2319754120220352192110959)
                      ·
                        rfl

theorem cell23_4517705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 3, 2].length) (baseStart_4517705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517705 prefixEnd_4517705 := by exact prefixLift 4517705
  have htrace : WordTrace (prefixWord ++ tailWord_4517705) baseStart_4517705 baseEnd_4517705 := by
    simpa [prefixWord, tailWord_4517705, baseEnd_4517705] using wordTrace_append hprefix tailTrace_4517705
  have hstable : (prefixWord ++ tailWord_4517705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517705).length < 2 ^ (prefixWord ++ tailWord_4517705).sum := by decide
  have hdescent : baseEnd_4517705 < baseStart_4517705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517769 : List Nat := [1, 2, 1, 1, 5, 1, 4, 3, 1, 2, 2]
def baseStart_4517769 : Nat := 118140960795 + 4517769 * 2 ^ 59
def prefixEnd_4517769 : Nat := 4983230072969 + 3 ^ 40 * 4517769 * 2
def baseEnd_4517769 : Nat := 2319786982982239941710665

theorem tailTrace_4517769 : CollatzResearch.WordTrace tailWord_4517769 prefixEnd_4517769 2319786982982239941710665 := by
  unfold tailWord_4517769
  simp only [CollatzResearch.WordTrace]
  refine ⟨164776572369901961362204361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109851048246601307574802907 164776572369901961362204361)
  ·
    refine ⟨123582429277426471021653271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164776572369901961362204361 123582429277426471021653271)
    ·
      refine ⟨185373643916139706532479907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123582429277426471021653271 185373643916139706532479907)
      ·
        refine ⟨278060465874209559798719861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185373643916139706532479907 278060465874209559798719861)
        ·
          refine ⟨26068168675707146231129987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 278060465874209559798719861 26068168675707146231129987)
          ·
            refine ⟨39102253013560719346694981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26068168675707146231129987 39102253013560719346694981)
            ·
              refine ⟨7331672440042634877505309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39102253013560719346694981 7331672440042634877505309)
              ·
                refine ⟨2749377165015988079064491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7331672440042634877505309 2749377165015988079064491)
                ·
                  refine ⟨4124065747523982118596737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2749377165015988079064491 4124065747523982118596737)
                  ·
                    refine ⟨3093049310642986588947553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4124065747523982118596737 3093049310642986588947553)
                    ·
                      refine ⟨2319786982982239941710665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3093049310642986588947553 2319786982982239941710665)
                      ·
                        rfl

theorem cell23_4517769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 1, 2, 2].length) (baseStart_4517769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517769 prefixEnd_4517769 := by exact prefixLift 4517769
  have htrace : WordTrace (prefixWord ++ tailWord_4517769) baseStart_4517769 baseEnd_4517769 := by
    simpa [prefixWord, tailWord_4517769, baseEnd_4517769] using wordTrace_append hprefix tailTrace_4517769
  have hstable : (prefixWord ++ tailWord_4517769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517769).length < 2 ^ (prefixWord ++ tailWord_4517769).sum := by decide
  have hdescent : baseEnd_4517769 < baseStart_4517769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517801 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 1, 8]
def baseStart_4517801 : Nat := 118140960795 + 4517801 * 2 ^ 59
def prefixEnd_4517801 : Nat := 4983230072969 + 3 ^ 40 * 4517801 * 2
def baseEnd_4517801 : Nat := 773267804787727938836839

theorem tailTrace_4517801 : CollatzResearch.WordTrace tailWord_4517801 prefixEnd_4517801 773267804787727938836839 := by
  unfold tailWord_4517801
  simp only [CollatzResearch.WordTrace]
  refine ⟨164777739505786030827369257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109851826337190687218246171 164777739505786030827369257)
  ·
    refine ⟨123583304629339523120526943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164777739505786030827369257 123583304629339523120526943)
    ·
      refine ⟨185374956944009284680790415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123583304629339523120526943 185374956944009284680790415)
      ·
        refine ⟨278062435416013927021185623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185374956944009284680790415 278062435416013927021185623)
        ·
          refine ⟨417093653124020890531778435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278062435416013927021185623 417093653124020890531778435)
          ·
            refine ⟨625640479686031335797667653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417093653124020890531778435 625640479686031335797667653)
            ·
              refine ⟨117307589941130875462062685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 625640479686031335797667653 117307589941130875462062685)
              ·
                refine ⟨43990346227924078298273507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117307589941130875462062685 43990346227924078298273507)
                ·
                  refine ⟨65985519341886117447410261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43990346227924078298273507 65985519341886117447410261)
                  ·
                    refine ⟨773267804787727938836839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65985519341886117447410261 773267804787727938836839)
                    ·
                      rfl

theorem cell23_4517801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 8].length) (baseStart_4517801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517801 prefixEnd_4517801 := by exact prefixLift 4517801
  have htrace : WordTrace (prefixWord ++ tailWord_4517801) baseStart_4517801 baseEnd_4517801 := by
    simpa [prefixWord, tailWord_4517801, baseEnd_4517801] using wordTrace_append hprefix tailTrace_4517801
  have hstable : (prefixWord ++ tailWord_4517801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517801).length < 2 ^ (prefixWord ++ tailWord_4517801).sum := by decide
  have hdescent : baseEnd_4517801 < baseStart_4517801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517820 : List Nat := [2, 2, 2, 5, 2, 1, 1, 3, 1, 2, 2]
def baseStart_4517820 : Nat := 118140960795 + 4517820 * 2 ^ 59
def prefixEnd_4517820 : Nat := 4983230072969 + 3 ^ 40 * 4517820 * 2
def baseEnd_4517820 : Nat := 2319813170495619242172931

theorem tailTrace_4517820 : CollatzResearch.WordTrace tailWord_4517820 prefixEnd_4517820 2319813170495619242172931 := by
  unfold tailWord_4517820
  simp only [CollatzResearch.WordTrace]
  refine ⟨82389216246358598536155457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109852288328478131381540609 82389216246358598536155457)
  ·
    refine ⟨61791912184768948902116593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82389216246358598536155457 61791912184768948902116593)
    ·
      refine ⟨46343934138576711676587445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61791912184768948902116593 46343934138576711676587445)
      ·
        refine ⟨4344743825491566719680073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46343934138576711676587445 4344743825491566719680073)
        ·
          refine ⟨3258557869118675039760055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4344743825491566719680073 3258557869118675039760055)
          ·
            refine ⟨4887836803678012559640083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3258557869118675039760055 4887836803678012559640083)
            ·
              refine ⟨7331755205517018839460125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4887836803678012559640083 7331755205517018839460125)
              ·
                refine ⟨2749408202068882064797547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7331755205517018839460125 2749408202068882064797547)
                ·
                  refine ⟨4124112303103323097196321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2749408202068882064797547 4124112303103323097196321)
                  ·
                    refine ⟨3093084227327492322897241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4124112303103323097196321 3093084227327492322897241)
                    ·
                      refine ⟨2319813170495619242172931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3093084227327492322897241 2319813170495619242172931)
                      ·
                        rfl

theorem cell23_4517820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_4517820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517820 prefixEnd_4517820 := by exact prefixLift 4517820
  have htrace : WordTrace (prefixWord ++ tailWord_4517820) baseStart_4517820 baseEnd_4517820 := by
    simpa [prefixWord, tailWord_4517820, baseEnd_4517820] using wordTrace_append hprefix tailTrace_4517820
  have hstable : (prefixWord ++ tailWord_4517820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517820).length < 2 ^ (prefixWord ++ tailWord_4517820).sum := by decide
  have hdescent : baseEnd_4517820 < baseStart_4517820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517853 : List Nat := [1, 4, 3, 1, 4, 1, 2, 1, 2, 1, 3]
def baseStart_4517853 : Nat := 118140960795 + 4517853 * 2 ^ 59
def prefixEnd_4517853 : Nat := 4983230072969 + 3 ^ 40 * 4517853 * 2
def baseEnd_4517853 : Nat := 2319830115357217613060279

theorem tailTrace_4517853 : CollatzResearch.WordTrace tailWord_4517853 prefixEnd_4517853 2319830115357217613060279 := by
  unfold tailWord_4517853
  simp only [CollatzResearch.WordTrace]
  refine ⟨164779636101597643708262213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109853090734398429138841475 164779636101597643708262213)
  ·
    refine ⟨30896181769049558195299165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164779636101597643708262213 30896181769049558195299165)
    ·
      refine ⟨11586068163393584323237187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30896181769049558195299165 11586068163393584323237187)
      ·
        refine ⟨17379102245090376484855781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11586068163393584323237187 17379102245090376484855781)
        ·
          refine ⟨3258581670954445590910459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17379102245090376484855781 3258581670954445590910459)
          ·
            refine ⟨4887872506431668386365689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3258581670954445590910459 4887872506431668386365689)
            ·
              refine ⟨3665904379823751289774267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4887872506431668386365689 3665904379823751289774267)
              ·
                refine ⟨5498856569735626934661401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3665904379823751289774267 5498856569735626934661401)
                ·
                  refine ⟨4124142427301720200996051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5498856569735626934661401 4124142427301720200996051)
                  ·
                    refine ⟨6186213640952580301494077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4124142427301720200996051 6186213640952580301494077)
                    ·
                      refine ⟨2319830115357217613060279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6186213640952580301494077 2319830115357217613060279)
                      ·
                        rfl

theorem cell23_4517853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_4517853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517853 prefixEnd_4517853 := by exact prefixLift 4517853
  have htrace : WordTrace (prefixWord ++ tailWord_4517853) baseStart_4517853 baseEnd_4517853 := by
    simpa [prefixWord, tailWord_4517853, baseEnd_4517853] using wordTrace_append hprefix tailTrace_4517853
  have hstable : (prefixWord ++ tailWord_4517853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517853).length < 2 ^ (prefixWord ++ tailWord_4517853).sum := by decide
  have hdescent : baseEnd_4517853 < baseStart_4517853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517859 : List Nat := [1, 1, 1, 6, 1, 3, 1, 3, 2, 2, 2]
def baseStart_4517859 : Nat := 118140960795 + 4517859 * 2 ^ 59
def prefixEnd_4517859 : Nat := 4983230072969 + 3 ^ 40 * 4517859 * 2
def baseEnd_4517859 : Nat := 2319833196241144589585251

theorem tailTrace_4517859 : CollatzResearch.WordTrace tailWord_4517859 prefixEnd_4517859 2319833196241144589585251 := by
  unfold tailWord_4517859
  simp only [CollatzResearch.WordTrace]
  refine ⟨164779854939575906732980631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109853236626383937821987087 164779854939575906732980631)
  ·
    refine ⟨247169782409363860099470947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164779854939575906732980631 247169782409363860099470947)
    ·
      refine ⟨370754673614045790149206421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247169782409363860099470947 370754673614045790149206421)
      ·
        refine ⟨17379125325658396413244051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 370754673614045790149206421 17379125325658396413244051)
        ·
          refine ⟨26068687988487594619866077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17379125325658396413244051 26068687988487594619866077)
          ·
            refine ⟨9775757995682847982449779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26068687988487594619866077 9775757995682847982449779)
            ·
              refine ⟨14663636993524271973674669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9775757995682847982449779 14663636993524271973674669)
              ·
                refine ⟨5498863872571601990128001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14663636993524271973674669 5498863872571601990128001)
                ·
                  refine ⟨4124147904428701492596001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5498863872571601990128001 4124147904428701492596001)
                  ·
                    refine ⟨3093110928321526119447001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4124147904428701492596001 3093110928321526119447001)
                    ·
                      refine ⟨2319833196241144589585251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3093110928321526119447001 2319833196241144589585251)
                      ·
                        rfl

theorem cell23_4517859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_4517859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517859 prefixEnd_4517859 := by exact prefixLift 4517859
  have htrace : WordTrace (prefixWord ++ tailWord_4517859) baseStart_4517859 baseEnd_4517859 := by
    simpa [prefixWord, tailWord_4517859, baseEnd_4517859] using wordTrace_append hprefix tailTrace_4517859
  have hstable : (prefixWord ++ tailWord_4517859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517859).length < 2 ^ (prefixWord ++ tailWord_4517859).sum := by decide
  have hdescent : baseEnd_4517859 < baseStart_4517859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517895 : List Nat := [1, 1, 4, 3, 1, 2, 2, 2, 2, 5]
def baseStart_4517895 : Nat := 118140960795 + 4517895 * 2 ^ 59
def prefixEnd_4517895 : Nat := 4983230072969 + 3 ^ 40 * 4517895 * 2
def baseEnd_4517895 : Nat := 773283893848235482911695

theorem tailTrace_4517895 : CollatzResearch.WordTrace tailWord_4517895 prefixEnd_4517895 773283893848235482911695 := by
  unfold tailWord_4517895
  simp only [CollatzResearch.WordTrace]
  refine ⟨164781167967445484881291139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109854111978296989920860759 164781167967445484881291139)
  ·
    refine ⟨247171751951168227321936709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164781167967445484881291139 247171751951168227321936709)
    ·
      refine ⟨46344703490844042622863133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 247171751951168227321936709 46344703490844042622863133)
      ·
        refine ⟨17379263809066515983573675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46344703490844042622863133 17379263809066515983573675)
        ·
          refine ⟨26068895713599773975360513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17379263809066515983573675 26068895713599773975360513)
          ·
            refine ⟨19551671785199830481520385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26068895713599773975360513 19551671785199830481520385)
            ·
              refine ⟨14663753838899872861140289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19551671785199830481520385 14663753838899872861140289)
              ·
                refine ⟨10997815379174904645855217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14663753838899872861140289 10997815379174904645855217)
                ·
                  refine ⟨8248361534381178484391413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10997815379174904645855217 8248361534381178484391413)
                  ·
                    refine ⟨773283893848235482911695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8248361534381178484391413 773283893848235482911695)
                    ·
                      rfl

theorem cell23_4517895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_4517895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517895 prefixEnd_4517895 := by exact prefixLift 4517895
  have htrace : WordTrace (prefixWord ++ tailWord_4517895) baseStart_4517895 baseEnd_4517895 := by
    simpa [prefixWord, tailWord_4517895, baseEnd_4517895] using wordTrace_append hprefix tailTrace_4517895
  have hstable : (prefixWord ++ tailWord_4517895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517895).length < 2 ^ (prefixWord ++ tailWord_4517895).sum := by decide
  have hdescent : baseEnd_4517895 < baseStart_4517895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517925 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 5, 4]
def baseStart_4517925 : Nat := 118140960795 + 4517925 * 2 ^ 59
def prefixEnd_4517925 : Nat := 4983230072969 + 3 ^ 40 * 4517925 * 2
def baseEnd_4517925 : Nat := 773289028654780443786649

theorem tailTrace_4517925 : CollatzResearch.WordTrace tailWord_4517925 prefixEnd_4517925 773289028654780443786649 := by
  unfold tailWord_4517925
  simp only [CollatzResearch.WordTrace]
  refine ⟨164782262157336800004883229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109854841438224533336588819 164782262157336800004883229)
  ·
    refine ⟨61793348309001300001831211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164782262157336800004883229 61793348309001300001831211)
    ·
      refine ⟨92690022463501950002746817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61793348309001300001831211 92690022463501950002746817)
      ·
        refine ⟨69517516847626462502060113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92690022463501950002746817 69517516847626462502060113)
        ·
          refine ⟨52138137635719846876545085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69517516847626462502060113 52138137635719846876545085)
          ·
            refine ⟨19551801613394942578704407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52138137635719846876545085 19551801613394942578704407)
            ·
              refine ⟨29327702420092413868056611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19551801613394942578704407 29327702420092413868056611)
              ·
                refine ⟨43991553630138620802084917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29327702420092413868056611 43991553630138620802084917)
                ·
                  refine ⟨4124208152825495700195461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43991553630138620802084917 4124208152825495700195461)
                  ·
                    refine ⟨773289028654780443786649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4124208152825495700195461 773289028654780443786649)
                    ·
                      rfl

theorem cell23_4517925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 4].length) (baseStart_4517925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517925 prefixEnd_4517925 := by exact prefixLift 4517925
  have htrace : WordTrace (prefixWord ++ tailWord_4517925) baseStart_4517925 baseEnd_4517925 := by
    simpa [prefixWord, tailWord_4517925, baseEnd_4517925] using wordTrace_append hprefix tailTrace_4517925
  have hstable : (prefixWord ++ tailWord_4517925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517925).length < 2 ^ (prefixWord ++ tailWord_4517925).sum := by decide
  have hdescent : baseEnd_4517925 < baseStart_4517925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517935 : List Nat := [1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 3]
def baseStart_4517935 : Nat := 118140960795 + 4517935 * 2 ^ 59
def prefixEnd_4517935 : Nat := 4983230072969 + 3 ^ 40 * 4517935 * 2
def baseEnd_4517935 : Nat := 2319872220770886292234901

theorem tailTrace_4517935 : CollatzResearch.WordTrace tailWord_4517935 prefixEnd_4517935 2319872220770886292234901 := by
  unfold tailWord_4517935
  simp only [CollatzResearch.WordTrace]
  refine ⟨164782626887300571712747259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109855084591533714475164839 164782626887300571712747259)
  ·
    refine ⟨247173940330950857569120889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164782626887300571712747259 247173940330950857569120889)
    ·
      refine ⟨185380455248213143176840667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247173940330950857569120889 185380455248213143176840667)
      ·
        refine ⟨278070682872319714765261001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185380455248213143176840667 278070682872319714765261001)
        ·
          refine ⟨208553012154239786073945751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278070682872319714765261001 208553012154239786073945751)
          ·
            refine ⟨312829518231359679110918627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208553012154239786073945751 312829518231359679110918627)
            ·
              refine ⟨469244277347039518666377941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312829518231359679110918627 469244277347039518666377941)
              ·
                refine ⟨10997912750321238718743233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 469244277347039518666377941 10997912750321238718743233)
                ·
                  refine ⟨8248434562740929039057425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10997912750321238718743233 8248434562740929039057425)
                  ·
                    refine ⟨6186325922055696779293069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8248434562740929039057425 6186325922055696779293069)
                    ·
                      refine ⟨2319872220770886292234901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6186325922055696779293069 2319872220770886292234901)
                      ·
                        rfl

theorem cell23_4517935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 3].length) (baseStart_4517935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517935 prefixEnd_4517935 := by exact prefixLift 4517935
  have htrace : WordTrace (prefixWord ++ tailWord_4517935) baseStart_4517935 baseEnd_4517935 := by
    simpa [prefixWord, tailWord_4517935, baseEnd_4517935] using wordTrace_append hprefix tailTrace_4517935
  have hstable : (prefixWord ++ tailWord_4517935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517935).length < 2 ^ (prefixWord ++ tailWord_4517935).sum := by decide
  have hdescent : baseEnd_4517935 < baseStart_4517935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4517942 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 5, 4]
def baseStart_4517942 : Nat := 118140960795 + 4517942 * 2 ^ 59
def prefixEnd_4517942 : Nat := 4983230072969 + 3 ^ 40 * 4517942 * 2
def baseEnd_4517942 : Nat := 773291938378489254949123

theorem tailTrace_4517942 : CollatzResearch.WordTrace tailWord_4517942 prefixEnd_4517942 773291938378489254949123 := by
  unfold tailWord_4517942
  simp only [CollatzResearch.WordTrace]
  refine ⟨10298930137392200744265755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109855254798850141272168053 10298930137392200744265755)
  ·
    refine ⟨15448395206088301116398633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10298930137392200744265755 15448395206088301116398633)
    ·
      refine ⟨11586296404566225837298975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15448395206088301116398633 11586296404566225837298975)
      ·
        refine ⟨17379444606849338755948463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11586296404566225837298975 17379444606849338755948463)
        ·
          refine ⟨26069166910274008133922695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17379444606849338755948463 26069166910274008133922695)
          ·
            refine ⟨39103750365411012200884043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26069166910274008133922695 39103750365411012200884043)
            ·
              refine ⟨58655625548116518301326065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39103750365411012200884043 58655625548116518301326065)
              ·
                refine ⟨43991719161087388725994549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58655625548116518301326065 43991719161087388725994549)
                ·
                  refine ⟨4124223671351942693061989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43991719161087388725994549 4124223671351942693061989)
                  ·
                    refine ⟨773291938378489254949123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4124223671351942693061989 773291938378489254949123)
                    ·
                      rfl

theorem cell23_4517942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_4517942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4517942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4517942 prefixEnd_4517942 := by exact prefixLift 4517942
  have htrace : WordTrace (prefixWord ++ tailWord_4517942) baseStart_4517942 baseEnd_4517942 := by
    simpa [prefixWord, tailWord_4517942, baseEnd_4517942] using wordTrace_append hprefix tailTrace_4517942
  have hstable : (prefixWord ++ tailWord_4517942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4517942).length < 2 ^ (prefixWord ++ tailWord_4517942).sum := by decide
  have hdescent : baseEnd_4517942 < baseStart_4517942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4517942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518002 : List Nat := [3, 2, 1, 2, 2, 2, 2, 3, 1, 5]
def baseStart_4518002 : Nat := 118140960795 + 4518002 * 2 ^ 59
def prefixEnd_4518002 : Nat := 4983230072969 + 3 ^ 40 * 4518002 * 2
def baseEnd_4518002 : Nat := 773302207991579176699031

theorem tailTrace_4518002 : CollatzResearch.WordTrace tailWord_4518002 prefixEnd_4518002 773302207991579176699031 := by
  unfold tailWord_4518002
  simp only [CollatzResearch.WordTrace]
  refine ⟨41196267644514460538859065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109856713718705228103624173 41196267644514460538859065)
  ·
    refine ⟨30897200733385845404144299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41196267644514460538859065 30897200733385845404144299)
    ·
      refine ⟨46345801100078768106216449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30897200733385845404144299 46345801100078768106216449)
      ·
        refine ⟨34759350825059076079662337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46345801100078768106216449 34759350825059076079662337)
        ·
          refine ⟨26069513118794307059746753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34759350825059076079662337 26069513118794307059746753)
          ·
            refine ⟨19552134839095730294810065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26069513118794307059746753 19552134839095730294810065)
            ·
              refine ⟨14664101129321797721107549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19552134839095730294810065 14664101129321797721107549)
              ·
                refine ⟨5499037923495674145415331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14664101129321797721107549 5499037923495674145415331)
                ·
                  refine ⟨8248556885243511218122997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5499037923495674145415331 8248556885243511218122997)
                  ·
                    refine ⟨773302207991579176699031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8248556885243511218122997 773302207991579176699031)
                    ·
                      rfl

theorem cell23_4518002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_4518002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518002 prefixEnd_4518002 := by exact prefixLift 4518002
  have htrace : WordTrace (prefixWord ++ tailWord_4518002) baseStart_4518002 baseEnd_4518002 := by
    simpa [prefixWord, tailWord_4518002, baseEnd_4518002] using wordTrace_append hprefix tailTrace_4518002
  have hstable : (prefixWord ++ tailWord_4518002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518002).length < 2 ^ (prefixWord ++ tailWord_4518002).sum := by decide
  have hdescent : baseEnd_4518002 < baseStart_4518002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518009 : List Nat := [1, 2, 1, 3, 4, 2, 1, 2, 2, 3, 2]
def baseStart_4518009 : Nat := 118140960795 + 4518009 * 2 ^ 59
def prefixEnd_4518009 : Nat := 4983230072969 + 3 ^ 40 * 4518009 * 2
def baseEnd_4518009 : Nat := 2319910218339319002709561

theorem tailTrace_4518009 : CollatzResearch.WordTrace tailWord_4518009 prefixEnd_4518009 2319910218339319002709561 := by
  unfold tailWord_4518009
  simp only [CollatzResearch.WordTrace]
  refine ⟨164785325889032482350941081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109856883926021654900627387 164785325889032482350941081)
  ·
    refine ⟨123588994416774361763205811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164785325889032482350941081 123588994416774361763205811)
    ·
      refine ⟨185383491625161542644808717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123588994416774361763205811 185383491625161542644808717)
      ·
        refine ⟨69518809359435578491803269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185383491625161542644808717 69518809359435578491803269)
        ·
          refine ⟨13034776754894170967213113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69518809359435578491803269 13034776754894170967213113)
          ·
            refine ⟨9776082566170628225409835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13034776754894170967213113 9776082566170628225409835)
            ·
              refine ⟨14664123849255942338114753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9776082566170628225409835 14664123849255942338114753)
              ·
                refine ⟨10998092886941956753586065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14664123849255942338114753 10998092886941956753586065)
                ·
                  refine ⟨8248569665206467565189549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10998092886941956753586065 8248569665206467565189549)
                  ·
                    refine ⟨3093213624452425336946081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8248569665206467565189549 3093213624452425336946081)
                    ·
                      refine ⟨2319910218339319002709561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3093213624452425336946081 2319910218339319002709561)
                      ·
                        rfl

theorem cell23_4518009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 3, 2].length) (baseStart_4518009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518009 prefixEnd_4518009 := by exact prefixLift 4518009
  have htrace : WordTrace (prefixWord ++ tailWord_4518009) baseStart_4518009 baseEnd_4518009 := by
    simpa [prefixWord, tailWord_4518009, baseEnd_4518009] using wordTrace_append hprefix tailTrace_4518009
  have hstable : (prefixWord ++ tailWord_4518009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518009).length < 2 ^ (prefixWord ++ tailWord_4518009).sum := by decide
  have hdescent : baseEnd_4518009 < baseStart_4518009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518025 : List Nat := [1, 2, 1, 1, 4, 2, 1, 4, 1, 1, 5]
def baseStart_4518025 : Nat := 118140960795 + 4518025 * 2 ^ 59
def prefixEnd_4518025 : Nat := 4983230072969 + 3 ^ 40 * 4518025 * 2
def baseEnd_4518025 : Nat := 2319918434029790940109487

theorem tailTrace_4518025 : CollatzResearch.WordTrace tailWord_4518025 prefixEnd_4518025 2319918434029790940109487 := by
  unfold tailWord_4518025
  simp only [CollatzResearch.WordTrace]
  refine ⟨164785909456974517083523529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109857272971316344722349019 164785909456974517083523529)
  ·
    refine ⟨123589432092730887812642647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164785909456974517083523529 123589432092730887812642647)
    ·
      refine ⟨185384148139096331718963971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123589432092730887812642647 185384148139096331718963971)
      ·
        refine ⟨278076222208644497578445957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185384148139096331718963971 278076222208644497578445957)
        ·
          refine ⟨52139291664120843295958617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 278076222208644497578445957 52139291664120843295958617)
          ·
            refine ⟨39104468748090632471968963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52139291664120843295958617 39104468748090632471968963)
            ·
              refine ⟨58656703122135948707953445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39104468748090632471968963 58656703122135948707953445)
              ·
                refine ⟨10998131835400490382741271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58656703122135948707953445 10998131835400490382741271)
                ·
                  refine ⟨16497197753100735574111907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10998131835400490382741271 16497197753100735574111907)
                  ·
                    refine ⟨24745796629651103361167861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16497197753100735574111907 24745796629651103361167861)
                    ·
                      refine ⟨2319918434029790940109487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24745796629651103361167861 2319918434029790940109487)
                      ·
                        rfl

theorem cell23_4518025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 1, 5].length) (baseStart_4518025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518025 prefixEnd_4518025 := by exact prefixLift 4518025
  have htrace : WordTrace (prefixWord ++ tailWord_4518025) baseStart_4518025 baseEnd_4518025 := by
    simpa [prefixWord, tailWord_4518025, baseEnd_4518025] using wordTrace_append hprefix tailTrace_4518025
  have hstable : (prefixWord ++ tailWord_4518025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518025).length < 2 ^ (prefixWord ++ tailWord_4518025).sum := by decide
  have hdescent : baseEnd_4518025 < baseStart_4518025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518032 : List Nat := [2, 1, 1, 1, 1, 1, 7, 3, 2, 4]
def baseStart_4518032 : Nat := 118140960795 + 4518032 * 2 ^ 59
def prefixEnd_4518032 : Nat := 4983230072969 + 3 ^ 40 * 4518032 * 2
def baseEnd_4518032 : Nat := 773307342798124137573985

theorem tailTrace_4518032 : CollatzResearch.WordTrace tailWord_4518032 prefixEnd_4518032 773307342798124137573985 := by
  unfold tailWord_4518032
  simp only [CollatzResearch.WordTrace]
  refine ⟨82393082383974578639514175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109857443178632771519352233 82393082383974578639514175)
  ·
    refine ⟨123589623575961867959271263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82393082383974578639514175 123589623575961867959271263)
    ·
      refine ⟨185384435363942801938906895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123589623575961867959271263 185384435363942801938906895)
      ·
        refine ⟨278076653045914202908360343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185384435363942801938906895 278076653045914202908360343)
        ·
          refine ⟨417114979568871304362540515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278076653045914202908360343 417114979568871304362540515)
          ·
            refine ⟨625672469353306956543810773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417114979568871304362540515 625672469353306956543810773)
            ·
              refine ⟨14664198500468131793995565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 625672469353306956543810773 14664198500468131793995565)
              ·
                refine ⟨5499074437675549422748337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14664198500468131793995565 5499074437675549422748337)
                ·
                  refine ⟨4124305828256662067061253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5499074437675549422748337 4124305828256662067061253)
                  ·
                    refine ⟨773307342798124137573985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4124305828256662067061253 773307342798124137573985)
                    ·
                      rfl

theorem cell23_4518032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 2, 4].length) (baseStart_4518032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518032 prefixEnd_4518032 := by exact prefixLift 4518032
  have htrace : WordTrace (prefixWord ++ tailWord_4518032) baseStart_4518032 baseEnd_4518032 := by
    simpa [prefixWord, tailWord_4518032, baseEnd_4518032] using wordTrace_append hprefix tailTrace_4518032
  have hstable : (prefixWord ++ tailWord_4518032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518032).length < 2 ^ (prefixWord ++ tailWord_4518032).sum := by decide
  have hdescent : baseEnd_4518032 < baseStart_4518032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518035 : List Nat := [1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 4]
def baseStart_4518035 : Nat := 118140960795 + 4518035 * 2 ^ 59
def prefixEnd_4518035 : Nat := 4983230072969 + 3 ^ 40 * 4518035 * 2
def baseEnd_4518035 : Nat := 2319923568836335900984441

theorem tailTrace_4518035 : CollatzResearch.WordTrace tailWord_4518035 prefixEnd_4518035 2319923568836335900984441 := by
  unfold tailWord_4518035
  simp only [CollatzResearch.WordTrace]
  refine ⟨164786274186938288791387559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109857516124625525860925039 164786274186938288791387559)
  ·
    refine ⟨247179411280407433187081339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164786274186938288791387559 247179411280407433187081339)
    ·
      refine ⟨370769116920611149780622009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247179411280407433187081339 370769116920611149780622009)
      ·
        refine ⟨278076837690458362335466507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 370769116920611149780622009 278076837690458362335466507)
        ·
          refine ⟨417115256535687543503199761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278076837690458362335466507 417115256535687543503199761)
          ·
            refine ⟨312836442401765657627399821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 417115256535687543503199761 312836442401765657627399821)
            ·
              refine ⟨117313665900662121610274933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 312836442401765657627399821 117313665900662121610274933)
              ·
                refine ⟨10998156178187073900963275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117313665900662121610274933 10998156178187073900963275)
                ·
                  refine ⟨16497234267280610851444913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10998156178187073900963275 16497234267280610851444913)
                  ·
                    refine ⟨12372925700460458138583685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16497234267280610851444913 12372925700460458138583685)
                    ·
                      refine ⟨2319923568836335900984441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12372925700460458138583685 2319923568836335900984441)
                      ·
                        rfl

theorem cell23_4518035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 4].length) (baseStart_4518035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518035 prefixEnd_4518035 := by exact prefixLift 4518035
  have htrace : WordTrace (prefixWord ++ tailWord_4518035) baseStart_4518035 baseEnd_4518035 := by
    simpa [prefixWord, tailWord_4518035, baseEnd_4518035] using wordTrace_append hprefix tailTrace_4518035
  have hstable : (prefixWord ++ tailWord_4518035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518035).length < 2 ^ (prefixWord ++ tailWord_4518035).sum := by decide
  have hdescent : baseEnd_4518035 < baseStart_4518035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518045 : List Nat := [1, 4, 2, 1, 1, 3, 2, 9]
def baseStart_4518045 : Nat := 118140960795 + 4518045 * 2 ^ 59
def prefixEnd_4518045 : Nat := 4983230072969 + 3 ^ 40 * 4518045 * 2
def baseEnd_4518045 : Nat := 85923285320106698587385

theorem tailTrace_4518045 : CollatzResearch.WordTrace tailWord_4518045 prefixEnd_4518045 85923285320106698587385 := by
  unfold tailWord_4518045
  simp only [CollatzResearch.WordTrace]
  refine ⟨164786638916902060499251589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109857759277934706999501059 164786638916902060499251589)
  ·
    refine ⟨30897494796919136343609673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164786638916902060499251589 30897494796919136343609673)
    ·
      refine ⟨23173121097689352257707255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30897494796919136343609673 23173121097689352257707255)
      ·
        refine ⟨34759681646534028386560883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23173121097689352257707255 34759681646534028386560883)
        ·
          refine ⟨52139522469801042579841325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34759681646534028386560883 52139522469801042579841325)
          ·
            refine ⟨19552320926175390967440497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52139522469801042579841325 19552320926175390967440497)
            ·
              refine ⟨14664240694631543225580373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19552320926175390967440497 14664240694631543225580373)
              ·
                refine ⟨85923285320106698587385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14664240694631543225580373 85923285320106698587385)
                ·
                  rfl

theorem cell23_4518045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 9].length) (baseStart_4518045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518045 prefixEnd_4518045 := by exact prefixLift 4518045
  have htrace : WordTrace (prefixWord ++ tailWord_4518045) baseStart_4518045 baseEnd_4518045 := by
    simpa [prefixWord, tailWord_4518045, baseEnd_4518045] using wordTrace_append hprefix tailTrace_4518045
  have hstable : (prefixWord ++ tailWord_4518045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518045).length < 2 ^ (prefixWord ++ tailWord_4518045).sum := by decide
  have hdescent : baseEnd_4518045 < baseStart_4518045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518062 : List Nat := [4, 1, 4, 2, 12]
def baseStart_4518062 : Nat := 118140960795 + 4518062 * 2 ^ 59
def prefixEnd_4518062 : Nat := 4983230072969 + 3 ^ 40 * 4518062 * 2
def baseEnd_4518062 : Nat := 3182355874916333738473

theorem tailTrace_4518062 : CollatzResearch.WordTrace tailWord_4518062 prefixEnd_4518062 3182355874916333738473 := by
  unfold tailWord_4518062
  simp only [CollatzResearch.WordTrace]
  refine ⟨20598407369730059050327555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109858172638560314935080293 20598407369730059050327555)
  ·
    refine ⟨30897611054595088575491333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20598407369730059050327555 30897611054595088575491333)
    ·
      refine ⟨5793302072736579107904625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30897611054595088575491333 5793302072736579107904625)
      ·
        refine ⟨4344976554552434330928469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5793302072736579107904625 4344976554552434330928469)
        ·
          refine ⟨3182355874916333738473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4344976554552434330928469 3182355874916333738473)
          ·
            rfl

theorem cell23_4518062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 12].length) (baseStart_4518062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518062 prefixEnd_4518062 := by exact prefixLift 4518062
  have htrace : WordTrace (prefixWord ++ tailWord_4518062) baseStart_4518062 baseEnd_4518062 := by
    simpa [prefixWord, tailWord_4518062, baseEnd_4518062] using wordTrace_append hprefix tailTrace_4518062
  have hstable : (prefixWord ++ tailWord_4518062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518062).length < 2 ^ (prefixWord ++ tailWord_4518062).sum := by decide
  have hdescent : baseEnd_4518062 < baseStart_4518062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518095 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 4]
def baseStart_4518095 : Nat := 118140960795 + 4518095 * 2 ^ 59
def prefixEnd_4518095 : Nat := 4983230072969 + 3 ^ 40 * 4518095 * 2
def baseEnd_4518095 : Nat := 2319954377675605666234165

theorem tailTrace_4518095 : CollatzResearch.WordTrace tailWord_4518095 prefixEnd_4518095 2319954377675605666234165 := by
  unfold tailWord_4518095
  simp only [CollatzResearch.WordTrace]
  refine ⟨164788462566720919038571739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109858975044480612692381159 164788462566720919038571739)
  ·
    refine ⟨247182693850081378557857609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164788462566720919038571739 247182693850081378557857609)
    ·
      refine ⟨185387020387561033918393207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247182693850081378557857609 185387020387561033918393207)
      ·
        refine ⟨278080530581341550877589811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185387020387561033918393207 278080530581341550877589811)
        ·
          refine ⟨417120795872012326316384717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278080530581341550877589811 417120795872012326316384717)
          ·
            refine ⟨156420298452004622368644269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 417120795872012326316384717 156420298452004622368644269)
            ·
              refine ⟨58657611919501733388241601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156420298452004622368644269 58657611919501733388241601)
              ·
                refine ⟨43993208939626300041181201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58657611919501733388241601 43993208939626300041181201)
                ·
                  refine ⟨32994906704719725030885901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43993208939626300041181201 32994906704719725030885901)
                  ·
                    refine ⟨12373090014269896886582213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32994906704719725030885901 12373090014269896886582213)
                    ·
                      refine ⟨2319954377675605666234165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12373090014269896886582213 2319954377675605666234165)
                      ·
                        rfl

theorem cell23_4518095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 4].length) (baseStart_4518095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518095 prefixEnd_4518095 := by exact prefixLift 4518095
  have htrace : WordTrace (prefixWord ++ tailWord_4518095) baseStart_4518095 baseEnd_4518095 := by
    simpa [prefixWord, tailWord_4518095, baseEnd_4518095] using wordTrace_append hprefix tailTrace_4518095
  have hstable : (prefixWord ++ tailWord_4518095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518095).length < 2 ^ (prefixWord ++ tailWord_4518095).sum := by decide
  have hdescent : baseEnd_4518095 < baseStart_4518095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518152 : List Nat := [2, 1, 3, 2, 3, 1, 2, 2, 7]
def baseStart_4518152 : Nat := 118140960795 + 4518152 * 2 ^ 59
def prefixEnd_4518152 : Nat := 4983230072969 + 3 ^ 40 * 4518152 * 2
def baseEnd_4518152 : Nat := 257775960674767993691267

theorem tailTrace_4518152 : CollatzResearch.WordTrace tailWord_4518152 prefixEnd_4518152 257775960674767993691267 := by
  unfold tailWord_4518152
  simp only [CollatzResearch.WordTrace]
  refine ⟨82395270763757208886698355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109860361018342945182264473 82395270763757208886698355)
  ·
    refine ⟨123592906145635813330047533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82395270763757208886698355 123592906145635813330047533)
    ·
      refine ⟨46347339804613429998767825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123592906145635813330047533 46347339804613429998767825)
      ·
        refine ⟨34760504853460072499075869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46347339804613429998767825 34760504853460072499075869)
        ·
          refine ⟨13035189320047527187153451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34760504853460072499075869 13035189320047527187153451)
          ·
            refine ⟨19552783980071290780730177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13035189320047527187153451 19552783980071290780730177)
            ·
              refine ⟨14664587985053468085547633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19552783980071290780730177 14664587985053468085547633)
              ·
                refine ⟨10998440988790101064160725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14664587985053468085547633 10998440988790101064160725)
                ·
                  refine ⟨257775960674767993691267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10998440988790101064160725 257775960674767993691267)
                  ·
                    rfl

theorem cell23_4518152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 7].length) (baseStart_4518152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518152 prefixEnd_4518152 := by exact prefixLift 4518152
  have htrace : WordTrace (prefixWord ++ tailWord_4518152) baseStart_4518152 baseEnd_4518152 := by
    simpa [prefixWord, tailWord_4518152, baseEnd_4518152] using wordTrace_append hprefix tailTrace_4518152
  have hstable : (prefixWord ++ tailWord_4518152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518152).length < 2 ^ (prefixWord ++ tailWord_4518152).sum := by decide
  have hdescent : baseEnd_4518152 < baseStart_4518152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518186 : List Nat := [3, 1, 4, 2, 2, 2, 1, 1, 7]
def baseStart_4518186 : Nat := 118140960795 + 4518186 * 2 ^ 59
def prefixEnd_4518186 : Nat := 4983230072969 + 3 ^ 40 * 4518186 * 2
def baseEnd_4518186 : Nat := 257777900490573867799583

theorem tailTrace_4518186 : CollatzResearch.WordTrace tailWord_4518186 prefixEnd_4518186 257777900490573867799583 := by
  unfold tailWord_4518186
  simp only [CollatzResearch.WordTrace]
  refine ⟨41197945402347810395033603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109861187739594161053422941 41197945402347810395033603)
  ·
    refine ⟨61796918103521715592550405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41197945402347810395033603 61796918103521715592550405)
    ·
      refine ⟨11586922144410321673603201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61796918103521715592550405 11586922144410321673603201)
      ·
        refine ⟨8690191608307741255202401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11586922144410321673603201 8690191608307741255202401)
        ·
          refine ⟨6517643706230805941401801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8690191608307741255202401 6517643706230805941401801)
          ·
            refine ⟨4888232779673104456051351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6517643706230805941401801 4888232779673104456051351)
            ·
              refine ⟨7332349169509656684077027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4888232779673104456051351 7332349169509656684077027)
              ·
                refine ⟨10998523754264485026115541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7332349169509656684077027 10998523754264485026115541)
                ·
                  refine ⟨257777900490573867799583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10998523754264485026115541 257777900490573867799583)
                  ·
                    rfl

theorem cell23_4518186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 7].length) (baseStart_4518186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4518186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4518186 prefixEnd_4518186 := by exact prefixLift 4518186
  have htrace : WordTrace (prefixWord ++ tailWord_4518186) baseStart_4518186 baseEnd_4518186 := by
    simpa [prefixWord, tailWord_4518186, baseEnd_4518186] using wordTrace_append hprefix tailTrace_4518186
  have hstable : (prefixWord ++ tailWord_4518186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518186).length < 2 ^ (prefixWord ++ tailWord_4518186).sum := by decide
  have hdescent : baseEnd_4518186 < baseStart_4518186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
