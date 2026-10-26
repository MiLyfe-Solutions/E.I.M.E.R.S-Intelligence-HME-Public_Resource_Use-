import V185TrunkScan22Chunk009

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_89180 : List Nat := [2, 2, 4, 1, 1, 1, 4, 7]
def baseStart_89180 : Nat := 118140960795 + 89180 * 2 ^ 59
def prefixEnd_89180 : Nat := 4983230072969 + 3 ^ 40 * 89180 * 2
def baseEnd_89180 : Nat := 3392015168004912336287

theorem tailTrace_89180 : CollatzResearch.WordTrace tailWord_89180 prefixEnd_89180 3392015168004912336287 := by
  unfold tailWord_89180
  simp only [CollatzResearch.WordTrace]
  refine ⟨1626330908461782788264497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2168441211282377051019329 1626330908461782788264497)
  ·
    refine ⟨1219748181346337091198373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1626330908461782788264497 1219748181346337091198373)
    ·
      refine ⟨228702784002438204599695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1219748181346337091198373 228702784002438204599695)
      ·
        refine ⟨343054176003657306899543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228702784002438204599695 343054176003657306899543)
        ·
          refine ⟨514581264005485960349315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343054176003657306899543 514581264005485960349315)
          ·
            refine ⟨771871896008228940523973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514581264005485960349315 771871896008228940523973)
            ·
              refine ⟨144725980501542926348245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 771871896008228940523973 144725980501542926348245)
              ·
                refine ⟨3392015168004912336287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 144725980501542926348245 3392015168004912336287)
                ·
                  rfl

theorem cell22_89180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 7].length) (baseStart_89180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89180 prefixEnd_89180 := by exact prefixLift 89180
  have htrace : WordTrace (prefixWord ++ tailWord_89180) baseStart_89180 baseEnd_89180 := by
    simpa [prefixWord, tailWord_89180, baseEnd_89180] using wordTrace_append hprefix tailTrace_89180
  have hstable : (prefixWord ++ tailWord_89180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89180).length < 2 ^ (prefixWord ++ tailWord_89180).sum := by decide
  have hdescent : baseEnd_89180 < baseStart_89180 := by decide
  rcases family_descends (prefixWord ++ tailWord_89180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89208 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 9]
def baseStart_89208 : Nat := 118140960795 + 89208 * 2 ^ 59
def prefixEnd_89208 : Nat := 4983230072969 + 3 ^ 40 * 89208 * 2
def baseEnd_89208 : Nat := 10179240494753823775499

theorem tailTrace_89208 : CollatzResearch.WordTrace tailWord_89208 prefixEnd_89208 10179240494753823775499 := by
  unfold tailWord_89208
  simp only [CollatzResearch.WordTrace]
  refine ⟨1626841530411063179274139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2169122040548084239032185 1626841530411063179274139)
  ·
    refine ⟨2440262295616594768911209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1626841530411063179274139 2440262295616594768911209)
    ·
      refine ⟨1830196721712446076683407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2440262295616594768911209 1830196721712446076683407)
      ·
        refine ⟨2745295082568669115025111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1830196721712446076683407 2745295082568669115025111)
        ·
          refine ⟨4117942623853003672537667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2745295082568669115025111 4117942623853003672537667)
          ·
            refine ⟨6176913935779505508806501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4117942623853003672537667 6176913935779505508806501)
            ·
              refine ⟨1158171362958657282901219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6176913935779505508806501 1158171362958657282901219)
              ·
                refine ⟨1737257044437985924351829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1158171362958657282901219 1737257044437985924351829)
                ·
                  refine ⟨10179240494753823775499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1737257044437985924351829 10179240494753823775499)
                  ·
                    rfl

theorem cell22_89208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 9].length) (baseStart_89208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89208 prefixEnd_89208 := by exact prefixLift 89208
  have htrace : WordTrace (prefixWord ++ tailWord_89208) baseStart_89208 baseEnd_89208 := by
    simpa [prefixWord, tailWord_89208, baseEnd_89208] using wordTrace_append hprefix tailTrace_89208
  have hstable : (prefixWord ++ tailWord_89208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89208).length < 2 ^ (prefixWord ++ tailWord_89208).sum := by decide
  have hdescent : baseEnd_89208 < baseStart_89208 := by decide
  rcases family_descends (prefixWord ++ tailWord_89208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89214 : List Nat := [4, 2, 4, 1, 1, 10]
def baseStart_89214 : Nat := 118140960795 + 89214 * 2 ^ 59
def prefixEnd_89214 : Nat := 4983230072969 + 3 ^ 40 * 89214 * 2
def baseEnd_89214 : Nat := 377034264282462415759

theorem tailTrace_89214 : CollatzResearch.WordTrace tailWord_89214 prefixEnd_89214 377034264282462415759 := by
  unfold tailWord_89214
  simp only [CollatzResearch.WordTrace]
  refine ⟨406737737350048672908337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2169267932533592922177797 406737737350048672908337)
  ·
    refine ⟨305053303012536504681253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 406737737350048672908337 305053303012536504681253)
    ·
      refine ⟨57197494314850594627735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 305053303012536504681253 57197494314850594627735)
      ·
        refine ⟨85796241472275891941603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57197494314850594627735 85796241472275891941603)
        ·
          refine ⟨128694362208413837912405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85796241472275891941603 128694362208413837912405)
          ·
            refine ⟨377034264282462415759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 128694362208413837912405 377034264282462415759)
            ·
              rfl

theorem cell22_89214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 10].length) (baseStart_89214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89214 prefixEnd_89214 := by exact prefixLift 89214
  have htrace : WordTrace (prefixWord ++ tailWord_89214) baseStart_89214 baseEnd_89214 := by
    simpa [prefixWord, tailWord_89214, baseEnd_89214] using wordTrace_append hprefix tailTrace_89214
  have hstable : (prefixWord ++ tailWord_89214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89214).length < 2 ^ (prefixWord ++ tailWord_89214).sum := by decide
  have hdescent : baseEnd_89214 < baseStart_89214 := by decide
  rcases family_descends (prefixWord ++ tailWord_89214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89225 : List Nat := [1, 2, 1, 1, 4, 3, 1, 4, 5]
def baseStart_89225 : Nat := 118140960795 + 89225 * 2 ^ 59
def prefixEnd_89225 : Nat := 4983230072969 + 3 ^ 40 * 89225 * 2
def baseEnd_89225 : Nat := 10181180310559697883815

theorem tailTrace_89225 : CollatzResearch.WordTrace tailWord_89225 prefixEnd_89225 10181180310559697883815 := by
  unfold tailWord_89225
  simp only [CollatzResearch.WordTrace]
  refine ⟨3254303101760538261917129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2169535401173692174611419 3254303101760538261917129)
  ·
    refine ⟨2440727326320403696437847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3254303101760538261917129 2440727326320403696437847)
    ·
      refine ⟨3661090989480605544656771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2440727326320403696437847 3661090989480605544656771)
      ·
        refine ⟨5491636484220908316985157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3661090989480605544656771 5491636484220908316985157)
        ·
          refine ⟨1029681840791420309434717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5491636484220908316985157 1029681840791420309434717)
          ·
            refine ⟨386130690296782616038019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1029681840791420309434717 386130690296782616038019)
            ·
              refine ⟨579196035445173924057029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386130690296782616038019 579196035445173924057029)
              ·
                refine ⟨108599256645970110760693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 579196035445173924057029 108599256645970110760693)
                ·
                  refine ⟨10181180310559697883815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108599256645970110760693 10181180310559697883815)
                  ·
                    rfl

theorem cell22_89225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 5].length) (baseStart_89225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89225 prefixEnd_89225 := by exact prefixLift 89225
  have htrace : WordTrace (prefixWord ++ tailWord_89225) baseStart_89225 baseEnd_89225 := by
    simpa [prefixWord, tailWord_89225, baseEnd_89225] using wordTrace_append hprefix tailTrace_89225
  have hstable : (prefixWord ++ tailWord_89225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89225).length < 2 ^ (prefixWord ++ tailWord_89225).sum := by decide
  have hdescent : baseEnd_89225 < baseStart_89225 := by decide
  rcases family_descends (prefixWord ++ tailWord_89225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89240 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 1, 7]
def baseStart_89240 : Nat := 118140960795 + 89240 * 2 ^ 59
def prefixEnd_89240 : Nat := 4983230072969 + 3 ^ 40 * 89240 * 2
def baseEnd_89240 : Nat := 30548675738224054526399

theorem tailTrace_89240 : CollatzResearch.WordTrace tailWord_89240 prefixEnd_89240 30548675738224054526399 := by
  unfold tailWord_89240
  simp only [CollatzResearch.WordTrace]
  refine ⟨1627425098353097911856587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2169900131137463882475449 1627425098353097911856587)
  ·
    refine ⟨2441137647529646867784881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1627425098353097911856587 2441137647529646867784881)
    ·
      refine ⟨1830853235647235150838661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2441137647529646867784881 1830853235647235150838661)
      ·
        refine ⟨343284981683856590782249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1830853235647235150838661 343284981683856590782249)
        ·
          refine ⟨257463736262892443086687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343284981683856590782249 257463736262892443086687)
          ·
            refine ⟨386195604394338664630031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257463736262892443086687 386195604394338664630031)
            ·
              refine ⟨579293406591507996945047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386195604394338664630031 579293406591507996945047)
              ·
                refine ⟨868940109887261995417571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 579293406591507996945047 868940109887261995417571)
                ·
                  refine ⟨1303410164830892993126357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 868940109887261995417571 1303410164830892993126357)
                  ·
                    refine ⟨30548675738224054526399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1303410164830892993126357 30548675738224054526399)
                    ·
                      rfl

theorem cell22_89240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_89240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89240 prefixEnd_89240 := by exact prefixLift 89240
  have htrace : WordTrace (prefixWord ++ tailWord_89240) baseStart_89240 baseEnd_89240 := by
    simpa [prefixWord, tailWord_89240, baseEnd_89240] using wordTrace_append hprefix tailTrace_89240
  have hstable : (prefixWord ++ tailWord_89240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89240).length < 2 ^ (prefixWord ++ tailWord_89240).sum := by decide
  have hdescent : baseEnd_89240 < baseStart_89240 := by decide
  rcases family_descends (prefixWord ++ tailWord_89240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89242 : List Nat := [3, 1, 1, 5, 1, 1, 2, 3, 5]
def baseStart_89242 : Nat := 118140960795 + 89242 * 2 ^ 59
def prefixEnd_89242 : Nat := 4983230072969 + 3 ^ 40 * 89242 * 2
def baseEnd_89242 : Nat := 10183120126365571992131

theorem tailTrace_89242 : CollatzResearch.WordTrace tailWord_89242 prefixEnd_89242 10183120126365571992131 := by
  unfold tailWord_89242
  simp only [CollatzResearch.WordTrace]
  refine ⟨813730785674737541321495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2169948761799300110190653 813730785674737541321495)
  ·
    refine ⟨1220596178512106311982243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 813730785674737541321495 1220596178512106311982243)
    ·
      refine ⟨1830894267768159467973365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1220596178512106311982243 1830894267768159467973365)
      ·
        refine ⟨171646337603264950122503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1830894267768159467973365 171646337603264950122503)
        ·
          refine ⟨257469506404897425183755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171646337603264950122503 257469506404897425183755)
          ·
            refine ⟨386204259607346137775633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257469506404897425183755 386204259607346137775633)
            ·
              refine ⟨289653194705509603331725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386204259607346137775633 289653194705509603331725)
              ·
                refine ⟨108619948014566101249397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289653194705509603331725 108619948014566101249397)
                ·
                  refine ⟨10183120126365571992131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108619948014566101249397 10183120126365571992131)
                  ·
                    rfl

theorem cell22_89242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_89242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89242 prefixEnd_89242 := by exact prefixLift 89242
  have htrace : WordTrace (prefixWord ++ tailWord_89242) baseStart_89242 baseEnd_89242 := by
    simpa [prefixWord, tailWord_89242, baseEnd_89242] using wordTrace_append hprefix tailTrace_89242
  have hstable : (prefixWord ++ tailWord_89242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89242).length < 2 ^ (prefixWord ++ tailWord_89242).sum := by decide
  have hdescent : baseEnd_89242 < baseStart_89242 := by decide
  rcases family_descends (prefixWord ++ tailWord_89242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89293 : List Nat := [1, 6, 2, 2, 1, 1, 3, 1, 5]
def baseStart_89293 : Nat := 118140960795 + 89293 * 2 ^ 59
def prefixEnd_89293 : Nat := 4983230072969 + 3 ^ 40 * 89293 * 2
def baseEnd_89293 : Nat := 10188939573783194317079

theorem tailTrace_89293 : CollatzResearch.WordTrace tailWord_89293 prefixEnd_89293 10188939573783194317079 := by
  unfold tailWord_89293
  simp only [CollatzResearch.WordTrace]
  refine ⟨3256783265514185875392533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2171188843676123916928355 3256783265514185875392533)
  ·
    refine ⟨152661715570977462909025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3256783265514185875392533 152661715570977462909025)
    ·
      refine ⟨114496286678233097181769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152661715570977462909025 114496286678233097181769)
      ·
        refine ⟨85872215008674822886327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114496286678233097181769 85872215008674822886327)
        ·
          refine ⟨128808322513012234329491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85872215008674822886327 128808322513012234329491)
          ·
            refine ⟨193212483769518351494237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128808322513012234329491 193212483769518351494237)
            ·
              refine ⟨72454681413569381810339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193212483769518351494237 72454681413569381810339)
              ·
                refine ⟨108682022120354072715509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72454681413569381810339 108682022120354072715509)
                ·
                  refine ⟨10188939573783194317079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108682022120354072715509 10188939573783194317079)
                  ·
                    rfl

theorem cell22_89293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_89293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89293 prefixEnd_89293 := by exact prefixLift 89293
  have htrace : WordTrace (prefixWord ++ tailWord_89293) baseStart_89293 baseEnd_89293 := by
    simpa [prefixWord, tailWord_89293, baseEnd_89293] using wordTrace_append hprefix tailTrace_89293
  have hstable : (prefixWord ++ tailWord_89293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89293).length < 2 ^ (prefixWord ++ tailWord_89293).sum := by decide
  have hdescent : baseEnd_89293 < baseStart_89293 := by decide
  rcases family_descends (prefixWord ++ tailWord_89293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89394 : List Nat := [3, 2, 1, 1, 4, 2, 2, 2, 5]
def baseStart_89394 : Nat := 118140960795 + 89394 * 2 ^ 59
def prefixEnd_89394 : Nat := 4983230072969 + 3 ^ 40 * 89394 * 2
def baseEnd_89394 : Nat := 10200464361806328725309

theorem tailTrace_89394 : CollatzResearch.WordTrace tailWord_89394 prefixEnd_89394 10200464361806328725309 := by
  unfold tailWord_89394
  simp only [CollatzResearch.WordTrace]
  refine ⟨815116759537070031204809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2173644692098853416546157 815116759537070031204809)
  ·
    refine ⟨611337569652802523403607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 815116759537070031204809 611337569652802523403607)
    ·
      refine ⟨917006354479203785105411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 611337569652802523403607 917006354479203785105411)
      ·
        refine ⟨1375509531718805677658117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 917006354479203785105411 1375509531718805677658117)
        ·
          refine ⟨257908037197276064560897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1375509531718805677658117 257908037197276064560897)
          ·
            refine ⟨193431027897957048420673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257908037197276064560897 193431027897957048420673)
            ·
              refine ⟨145073270923467786315505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193431027897957048420673 145073270923467786315505)
              ·
                refine ⟨108804953192600839736629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145073270923467786315505 108804953192600839736629)
                ·
                  refine ⟨10200464361806328725309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108804953192600839736629 10200464361806328725309)
                  ·
                    rfl

theorem cell22_89394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_89394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89394 prefixEnd_89394 := by exact prefixLift 89394
  have htrace : WordTrace (prefixWord ++ tailWord_89394) baseStart_89394 baseEnd_89394 := by
    simpa [prefixWord, tailWord_89394, baseEnd_89394] using wordTrace_append hprefix tailTrace_89394
  have hstable : (prefixWord ++ tailWord_89394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89394).length < 2 ^ (prefixWord ++ tailWord_89394).sum := by decide
  have hdescent : baseEnd_89394 < baseStart_89394 := by decide
  rcases family_descends (prefixWord ++ tailWord_89394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89407 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 3, 4]
def baseStart_89407 : Nat := 118140960795 + 89407 * 2 ^ 59
def prefixEnd_89407 : Nat := 4983230072969 + 3 ^ 40 * 89407 * 2
def baseEnd_89407 : Nat := 30605843251091285600887

theorem tailTrace_89407 : CollatzResearch.WordTrace tailWord_89407 prefixEnd_89407 30605843251091285600887 := by
  unfold tailWord_89407
  simp only [CollatzResearch.WordTrace]
  refine ⟨3260941187101183345042475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2173960791400788896694983 3260941187101183345042475)
  ·
    refine ⟨4891411780651775017563713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3260941187101183345042475 4891411780651775017563713)
    ·
      refine ⟨3668558835488831263172785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4891411780651775017563713 3668558835488831263172785)
      ·
        refine ⟨2751419126616623447379589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3668558835488831263172785 2751419126616623447379589)
        ·
          refine ⟨515891086240616896383673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2751419126616623447379589 515891086240616896383673)
          ·
            refine ⟨386918314680462672287755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 515891086240616896383673 386918314680462672287755)
            ·
              refine ⟨580377472020694008431633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386918314680462672287755 580377472020694008431633)
              ·
                refine ⟨435283104015520506323725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 580377472020694008431633 435283104015520506323725)
                ·
                  refine ⟨163231164005820189871397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 435283104015520506323725 163231164005820189871397)
                  ·
                    refine ⟨30605843251091285600887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 163231164005820189871397 30605843251091285600887)
                    ·
                      rfl

theorem cell22_89407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 4].length) (baseStart_89407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89407 prefixEnd_89407 := by exact prefixLift 89407
  have htrace : WordTrace (prefixWord ++ tailWord_89407) baseStart_89407 baseEnd_89407 := by
    simpa [prefixWord, tailWord_89407, baseEnd_89407] using wordTrace_append hprefix tailTrace_89407
  have hstable : (prefixWord ++ tailWord_89407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89407).length < 2 ^ (prefixWord ++ tailWord_89407).sum := by decide
  have hdescent : baseEnd_89407 < baseStart_89407 := by decide
  rcases family_descends (prefixWord ++ tailWord_89407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89409 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 2, 5]
def baseStart_89409 : Nat := 118140960795 + 89409 * 2 ^ 59
def prefixEnd_89409 : Nat := 4983230072969 + 3 ^ 40 * 89409 * 2
def baseEnd_89409 : Nat := 30606527891963947050881

theorem tailTrace_89409 : CollatzResearch.WordTrace tailWord_89409 prefixEnd_89409 30606527891963947050881 := by
  unfold tailWord_89409
  simp only [CollatzResearch.WordTrace]
  refine ⟨3261014133093937686615281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2174009422062625124410187 3261014133093937686615281)
  ·
    refine ⟨2445760599820453264961461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3261014133093937686615281 2445760599820453264961461)
    ·
      refine ⟨229290056233167493590137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2445760599820453264961461 229290056233167493590137)
      ·
        refine ⟨171967542174875620192603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229290056233167493590137 171967542174875620192603)
        ·
          refine ⟨257951313262313430288905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171967542174875620192603 257951313262313430288905)
          ·
            refine ⟨193463484946735072716679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257951313262313430288905 193463484946735072716679)
            ·
              refine ⟨290195227420102609075019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193463484946735072716679 290195227420102609075019)
              ·
                refine ⟨435292841130153913612529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290195227420102609075019 435292841130153913612529)
                ·
                  refine ⟨326469630847615435209397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435292841130153913612529 326469630847615435209397)
                  ·
                    refine ⟨30606527891963947050881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 326469630847615435209397 30606527891963947050881)
                    ·
                      rfl

theorem cell22_89409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_89409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89409 prefixEnd_89409 := by exact prefixLift 89409
  have htrace : WordTrace (prefixWord ++ tailWord_89409) baseStart_89409 baseEnd_89409 := by
    simpa [prefixWord, tailWord_89409, baseEnd_89409] using wordTrace_append hprefix tailTrace_89409
  have hstable : (prefixWord ++ tailWord_89409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89409).length < 2 ^ (prefixWord ++ tailWord_89409).sum := by decide
  have hdescent : baseEnd_89409 < baseStart_89409 := by decide
  rcases family_descends (prefixWord ++ tailWord_89409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89422 : List Nat := [4, 1, 1, 1, 1, 1, 5, 2, 6]
def baseStart_89422 : Nat := 118140960795 + 89422 * 2 ^ 59
def prefixEnd_89422 : Nat := 4983230072969 + 3 ^ 40 * 89422 * 2
def baseEnd_89422 : Nat := 10203659352545415491947

theorem tailTrace_89422 : CollatzResearch.WordTrace tailWord_89422 prefixEnd_89422 10203659352545415491947 := by
  unfold tailWord_89422
  simp only [CollatzResearch.WordTrace]
  refine ⟨407686035255855113354815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2174325521364560604559013 407686035255855113354815)
  ·
    refine ⟨611529052883782670032223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 407686035255855113354815 611529052883782670032223)
    ·
      refine ⟨917293579325674005048335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 611529052883782670032223 917293579325674005048335)
      ·
        refine ⟨1375940368988511007572503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 917293579325674005048335 1375940368988511007572503)
        ·
          refine ⟨2063910553482766511358755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1375940368988511007572503 2063910553482766511358755)
          ·
            refine ⟨3095865830224149767038133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2063910553482766511358755 3095865830224149767038133)
            ·
              refine ⟨290237421583514040659825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3095865830224149767038133 290237421583514040659825)
              ·
                refine ⟨217678066187635530494869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290237421583514040659825 217678066187635530494869)
                ·
                  refine ⟨10203659352545415491947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 217678066187635530494869 10203659352545415491947)
                  ·
                    rfl

theorem cell22_89422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_89422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89422 prefixEnd_89422 := by exact prefixLift 89422
  have htrace : WordTrace (prefixWord ++ tailWord_89422) baseStart_89422 baseEnd_89422 := by
    simpa [prefixWord, tailWord_89422, baseEnd_89422] using wordTrace_append hprefix tailTrace_89422
  have hstable : (prefixWord ++ tailWord_89422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89422).length < 2 ^ (prefixWord ++ tailWord_89422).sum := by decide
  have hdescent : baseEnd_89422 < baseStart_89422 := by decide
  rcases family_descends (prefixWord ++ tailWord_89422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89490 : List Nat := [3, 2, 3, 3, 1, 2, 1, 3, 4]
def baseStart_89490 : Nat := 118140960795 + 89490 * 2 ^ 59
def prefixEnd_89490 : Nat := 4983230072969 + 3 ^ 40 * 89490 * 2
def baseEnd_89490 : Nat := 10211418615768911925211

theorem tailTrace_89490 : CollatzResearch.WordTrace tailWord_89490 prefixEnd_89490 10211418615768911925211 := by
  unfold tailWord_89490
  simp only [CollatzResearch.WordTrace]
  refine ⟨815992111450122130078481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2175978963866992346875949 815992111450122130078481)
  ·
    refine ⟨611994083587591597558861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 815992111450122130078481 611994083587591597558861)
    ·
      refine ⟨229497781345346849084573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 611994083587591597558861 229497781345346849084573)
      ·
        refine ⟨86061668004505068406715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229497781345346849084573 86061668004505068406715)
        ·
          refine ⟨129092502006757602610073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86061668004505068406715 129092502006757602610073)
          ·
            refine ⟨96819376505068201957555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129092502006757602610073 96819376505068201957555)
            ·
              refine ⟨145229064757602302936333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96819376505068201957555 145229064757602302936333)
              ·
                refine ⟨54460899284100863601125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145229064757602302936333 54460899284100863601125)
                ·
                  refine ⟨10211418615768911925211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54460899284100863601125 10211418615768911925211)
                  ·
                    rfl

theorem cell22_89490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_89490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89490 prefixEnd_89490 := by exact prefixLift 89490
  have htrace : WordTrace (prefixWord ++ tailWord_89490) baseStart_89490 baseEnd_89490 := by
    simpa [prefixWord, tailWord_89490, baseEnd_89490] using wordTrace_append hprefix tailTrace_89490
  have hstable : (prefixWord ++ tailWord_89490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89490).length < 2 ^ (prefixWord ++ tailWord_89490).sum := by decide
  have hdescent : baseEnd_89490 < baseStart_89490 := by decide
  rcases family_descends (prefixWord ++ tailWord_89490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89516 : List Nat := [2, 2, 1, 1, 1, 1, 4, 6, 1, 3]
def baseStart_89516 : Nat := 118140960795 + 89516 * 2 ^ 59
def prefixEnd_89516 : Nat := 4983230072969 + 3 ^ 40 * 89516 * 2
def baseEnd_89516 : Nat := 30643156178651334625553

theorem tailTrace_89516 : CollatzResearch.WordTrace tailWord_89516 prefixEnd_89516 30643156178651334625553 := by
  unfold tailWord_89516
  simp only [CollatzResearch.WordTrace]
  refine ⟨1632458371853147480380201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2176611162470863307173601 1632458371853147480380201)
  ·
    refine ⟨1224343778889860610285151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1632458371853147480380201 1224343778889860610285151)
    ·
      refine ⟨1836515668334790915427727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1224343778889860610285151 1836515668334790915427727)
      ·
        refine ⟨2754773502502186373141591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1836515668334790915427727 2754773502502186373141591)
        ·
          refine ⟨4132160253753279559712387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2754773502502186373141591 4132160253753279559712387)
          ·
            refine ⟨6198240380629919339568581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4132160253753279559712387 6198240380629919339568581)
            ·
              refine ⟨1162170071368109876169109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6198240380629919339568581 1162170071368109876169109)
              ·
                refine ⟨54476722095380150445427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1162170071368109876169109 54476722095380150445427)
                ·
                  refine ⟨81715083143070225668141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54476722095380150445427 81715083143070225668141)
                  ·
                    refine ⟨30643156178651334625553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81715083143070225668141 30643156178651334625553)
                    ·
                      rfl

theorem cell22_89516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 1, 3].length) (baseStart_89516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89516 prefixEnd_89516 := by exact prefixLift 89516
  have htrace : WordTrace (prefixWord ++ tailWord_89516) baseStart_89516 baseEnd_89516 := by
    simpa [prefixWord, tailWord_89516, baseEnd_89516] using wordTrace_append hprefix tailTrace_89516
  have hstable : (prefixWord ++ tailWord_89516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89516).length < 2 ^ (prefixWord ++ tailWord_89516).sum := by decide
  have hdescent : baseEnd_89516 < baseStart_89516 := by decide
  rcases family_descends (prefixWord ++ tailWord_89516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89527 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 1, 7]
def baseStart_89527 : Nat := 118140960795 + 89527 * 2 ^ 59
def prefixEnd_89527 : Nat := 4983230072969 + 3 ^ 40 * 89527 * 2
def baseEnd_89527 : Nat := 30646921703450972600519

theorem tailTrace_89527 : CollatzResearch.WordTrace tailWord_89527 prefixEnd_89527 30646921703450972600519 := by
  unfold tailWord_89527
  simp only [CollatzResearch.WordTrace]
  refine ⟨3265317946666443839410835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2176878631110962559607223 3265317946666443839410835)
  ·
    refine ⟨4897976919999665759116253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3265317946666443839410835 4897976919999665759116253)
    ·
      refine ⟨1836741344999874659668595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4897976919999665759116253 1836741344999874659668595)
      ·
        refine ⟨2755112017499811989502893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1836741344999874659668595 2755112017499811989502893)
        ·
          refine ⟨1033167006562429496063585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2755112017499811989502893 1033167006562429496063585)
          ·
            refine ⟨774875254921822122047689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1033167006562429496063585 774875254921822122047689)
            ·
              refine ⟨581156441191366591535767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 774875254921822122047689 581156441191366591535767)
              ·
                refine ⟨871734661787049887303651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 581156441191366591535767 871734661787049887303651)
                ·
                  refine ⟨1307601992680574830955477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 871734661787049887303651 1307601992680574830955477)
                  ·
                    refine ⟨30646921703450972600519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1307601992680574830955477 30646921703450972600519)
                    ·
                      rfl

theorem cell22_89527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_89527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89527 prefixEnd_89527 := by exact prefixLift 89527
  have htrace : WordTrace (prefixWord ++ tailWord_89527) baseStart_89527 baseEnd_89527 := by
    simpa [prefixWord, tailWord_89527, baseEnd_89527] using wordTrace_append hprefix tailTrace_89527
  have hstable : (prefixWord ++ tailWord_89527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89527).length < 2 ^ (prefixWord ++ tailWord_89527).sum := by decide
  have hdescent : baseEnd_89527 < baseStart_89527 := by decide
  rcases family_descends (prefixWord ++ tailWord_89527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89559 : List Nat := [1, 1, 3, 2, 1, 1, 1, 7, 1, 4]
def baseStart_89559 : Nat := 118140960795 + 89559 * 2 ^ 59
def prefixEnd_89559 : Nat := 4983230072969 + 3 ^ 40 * 89559 * 2
def baseEnd_89559 : Nat := 30657875957413555800421

theorem tailTrace_89559 : CollatzResearch.WordTrace tailWord_89559 prefixEnd_89559 30657875957413555800421 := by
  unfold tailWord_89559
  simp only [CollatzResearch.WordTrace]
  refine ⟨3266485082550513304575731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2177656721700342203050487 3266485082550513304575731)
  ·
    refine ⟨4899727623825769956863597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3266485082550513304575731 4899727623825769956863597)
    ·
      refine ⟨1837397858934663733823849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4899727623825769956863597 1837397858934663733823849)
      ·
        refine ⟨1378048394200997800367887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1837397858934663733823849 1378048394200997800367887)
        ·
          refine ⟨2067072591301496700551831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1378048394200997800367887 2067072591301496700551831)
          ·
            refine ⟨3100608886952245050827747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2067072591301496700551831 3100608886952245050827747)
            ·
              refine ⟨4650913330428367576241621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3100608886952245050827747 4650913330428367576241621)
              ·
                refine ⟨109005781181914865068163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4650913330428367576241621 109005781181914865068163)
                ·
                  refine ⟨163508671772872297602245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109005781181914865068163 163508671772872297602245)
                  ·
                    refine ⟨30657875957413555800421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 163508671772872297602245 30657875957413555800421)
                    ·
                      rfl

theorem cell22_89559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_89559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89559 prefixEnd_89559 := by exact prefixLift 89559
  have htrace : WordTrace (prefixWord ++ tailWord_89559) baseStart_89559 baseEnd_89559 := by
    simpa [prefixWord, tailWord_89559, baseEnd_89559] using wordTrace_append hprefix tailTrace_89559
  have hstable : (prefixWord ++ tailWord_89559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89559).length < 2 ^ (prefixWord ++ tailWord_89559).sum := by decide
  have hdescent : baseEnd_89559 < baseStart_89559 := by decide
  rcases family_descends (prefixWord ++ tailWord_89559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89640 : List Nat := [2, 1, 5, 2, 3, 1, 1, 1, 1, 5]
def baseStart_89640 : Nat := 118140960795 + 89640 * 2 ^ 59
def prefixEnd_89640 : Nat := 4983230072969 + 3 ^ 40 * 89640 * 2
def baseEnd_89640 : Nat := 30685603912756344525173

theorem tailTrace_89640 : CollatzResearch.WordTrace tailWord_89640 prefixEnd_89640 30685603912756344525173 := by
  unfold tailWord_89640
  simp only [CollatzResearch.WordTrace]
  refine ⟨1634719697628532069137187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2179626263504709425516249 1634719697628532069137187)
  ·
    refine ⟨2452079546442798103705781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1634719697628532069137187 2452079546442798103705781)
    ·
      refine ⟨229882457479012322222417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2452079546442798103705781 229882457479012322222417)
      ·
        refine ⟨172411843109259241666813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229882457479012322222417 172411843109259241666813)
        ·
          refine ⟨64654441165972215625055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172411843109259241666813 64654441165972215625055)
          ·
            refine ⟨96981661748958323437583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64654441165972215625055 96981661748958323437583)
            ·
              refine ⟨145472492623437485156375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96981661748958323437583 145472492623437485156375)
              ·
                refine ⟨218208738935156227734563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145472492623437485156375 218208738935156227734563)
                ·
                  refine ⟨327313108402734341601845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218208738935156227734563 327313108402734341601845)
                  ·
                    refine ⟨30685603912756344525173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 327313108402734341601845 30685603912756344525173)
                    ·
                      rfl

theorem cell22_89640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_89640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89640 prefixEnd_89640 := by exact prefixLift 89640
  have htrace : WordTrace (prefixWord ++ tailWord_89640) baseStart_89640 baseEnd_89640 := by
    simpa [prefixWord, tailWord_89640, baseEnd_89640] using wordTrace_append hprefix tailTrace_89640
  have hstable : (prefixWord ++ tailWord_89640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89640).length < 2 ^ (prefixWord ++ tailWord_89640).sum := by decide
  have hdescent : baseEnd_89640 < baseStart_89640 := by decide
  rcases family_descends (prefixWord ++ tailWord_89640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89651 : List Nat := [1, 1, 1, 2, 4, 3, 2, 2, 3, 3]
def baseStart_89651 : Nat := 118140960795 + 89651 * 2 ^ 59
def prefixEnd_89651 : Nat := 4983230072969 + 3 ^ 40 * 89651 * 2
def baseEnd_89651 : Nat := 30689369437555982500139

theorem tailTrace_89651 : CollatzResearch.WordTrace tailWord_89651 prefixEnd_89651 30689369437555982500139 := by
  unfold tailWord_89651
  simp only [CollatzResearch.WordTrace]
  refine ⟨3269840598217213016924807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2179893732144808677949871 3269840598217213016924807)
  ·
    refine ⟨4904760897325819525387211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3269840598217213016924807 4904760897325819525387211)
    ·
      refine ⟨7357141345988729288080817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4904760897325819525387211 7357141345988729288080817)
      ·
        refine ⟨5517856009491546966060613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7357141345988729288080817 5517856009491546966060613)
        ·
          refine ⟨1034598001779665056136365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5517856009491546966060613 1034598001779665056136365)
          ·
            refine ⟨387974250667374396051137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1034598001779665056136365 387974250667374396051137)
            ·
              refine ⟨290980688000530797038353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387974250667374396051137 290980688000530797038353)
              ·
                refine ⟨218235516000398097778765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290980688000530797038353 218235516000398097778765)
                ·
                  refine ⟨81838318500149286667037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218235516000398097778765 81838318500149286667037)
                  ·
                    refine ⟨30689369437555982500139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81838318500149286667037 30689369437555982500139)
                    ·
                      rfl

theorem cell22_89651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 3].length) (baseStart_89651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89651 prefixEnd_89651 := by exact prefixLift 89651
  have htrace : WordTrace (prefixWord ++ tailWord_89651) baseStart_89651 baseEnd_89651 := by
    simpa [prefixWord, tailWord_89651, baseEnd_89651] using wordTrace_append hprefix tailTrace_89651
  have hstable : (prefixWord ++ tailWord_89651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89651).length < 2 ^ (prefixWord ++ tailWord_89651).sum := by decide
  have hdescent : baseEnd_89651 < baseStart_89651 := by decide
  rcases family_descends (prefixWord ++ tailWord_89651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89670 : List Nat := [6, 1, 1, 1, 4, 1, 8]
def baseStart_89670 : Nat := 118140960795 + 89670 * 2 ^ 59
def prefixEnd_89670 : Nat := 4983230072969 + 3 ^ 40 * 89670 * 2
def baseEnd_89670 : Nat := 1136884204660972825003

theorem tailTrace_89670 : CollatzResearch.WordTrace tailWord_89670 prefixEnd_89670 1136884204660972825003 := by
  unfold tailWord_89670
  simp only [CollatzResearch.WordTrace]
  refine ⟨102204174535886851933327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2180355723432252841244309 102204174535886851933327)
  ·
    refine ⟨153306261803830277899991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102204174535886851933327 153306261803830277899991)
    ·
      refine ⟨229959392705745416849987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153306261803830277899991 229959392705745416849987)
      ·
        refine ⟨344939089058618125274981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229959392705745416849987 344939089058618125274981)
        ·
          refine ⟨64676079198490898489059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 344939089058618125274981 64676079198490898489059)
          ·
            refine ⟨97014118797736347733589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64676079198490898489059 97014118797736347733589)
            ·
              refine ⟨1136884204660972825003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 97014118797736347733589 1136884204660972825003)
              ·
                rfl

theorem cell22_89670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 8].length) (baseStart_89670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89670 prefixEnd_89670 := by exact prefixLift 89670
  have htrace : WordTrace (prefixWord ++ tailWord_89670) baseStart_89670 baseEnd_89670 := by
    simpa [prefixWord, tailWord_89670, baseEnd_89670] using wordTrace_append hprefix tailTrace_89670
  have hstable : (prefixWord ++ tailWord_89670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89670).length < 2 ^ (prefixWord ++ tailWord_89670).sum := by decide
  have hdescent : baseEnd_89670 < baseStart_89670 := by decide
  rcases family_descends (prefixWord ++ tailWord_89670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89728 : List Nat := [2, 1, 1, 2, 1, 4, 5, 1, 1, 4]
def baseStart_89728 : Nat := 118140960795 + 89728 * 2 ^ 59
def prefixEnd_89728 : Nat := 4983230072969 + 3 ^ 40 * 89728 * 2
def baseEnd_89728 : Nat := 30715728111153448324903

theorem tailTrace_89728 : CollatzResearch.WordTrace tailWord_89728 prefixEnd_89728 30715728111153448324903 := by
  unfold tailWord_89728
  simp only [CollatzResearch.WordTrace]
  refine ⟨1636324509469127583738919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2181766012625503444985225 1636324509469127583738919)
  ·
    refine ⟨2454486764203691375608379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1636324509469127583738919 2454486764203691375608379)
    ·
      refine ⟨3681730146305537063412569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2454486764203691375608379 3681730146305537063412569)
      ·
        refine ⟨2761297609729152797559427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3681730146305537063412569 2761297609729152797559427)
        ·
          refine ⟨4141946414593729196339141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2761297609729152797559427 4141946414593729196339141)
          ·
            refine ⟨776614952736324224313589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4141946414593729196339141 776614952736324224313589)
            ·
              refine ⟨72807651819030396029399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 776614952736324224313589 72807651819030396029399)
              ·
                refine ⟨109211477728545594044099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72807651819030396029399 109211477728545594044099)
                ·
                  refine ⟨163817216592818391066149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109211477728545594044099 163817216592818391066149)
                  ·
                    refine ⟨30715728111153448324903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 163817216592818391066149 30715728111153448324903)
                    ·
                      rfl

theorem cell22_89728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 1, 4].length) (baseStart_89728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89728 prefixEnd_89728 := by exact prefixLift 89728
  have htrace : WordTrace (prefixWord ++ tailWord_89728) baseStart_89728 baseEnd_89728 := by
    simpa [prefixWord, tailWord_89728, baseEnd_89728] using wordTrace_append hprefix tailTrace_89728
  have hstable : (prefixWord ++ tailWord_89728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89728).length < 2 ^ (prefixWord ++ tailWord_89728).sum := by decide
  have hdescent : baseEnd_89728 < baseStart_89728 := by decide
  rcases family_descends (prefixWord ++ tailWord_89728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89736 : List Nat := [2, 1, 3, 5, 2, 1, 2, 2, 1, 3]
def baseStart_89736 : Nat := 118140960795 + 89736 * 2 ^ 59
def prefixEnd_89736 : Nat := 4983230072969 + 3 ^ 40 * 89736 * 2
def baseEnd_89736 : Nat := 30718466674644094124879

theorem tailTrace_89736 : CollatzResearch.WordTrace tailWord_89736 prefixEnd_89736 30718466674644094124879 := by
  unfold tailWord_89736
  simp only [CollatzResearch.WordTrace]
  refine ⟨1636470401454636266884531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2181960535272848355846041 1636470401454636266884531)
  ·
    refine ⟨2454705602181954400326797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1636470401454636266884531 2454705602181954400326797)
    ·
      refine ⟨920514600818232900122549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2454705602181954400326797 920514600818232900122549)
      ·
        refine ⟨86298243826709334386489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 920514600818232900122549 86298243826709334386489)
        ·
          refine ⟨64723682870032000789867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86298243826709334386489 64723682870032000789867)
          ·
            refine ⟨97085524305048001184801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64723682870032000789867 97085524305048001184801)
            ·
              refine ⟨72814143228786000888601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97085524305048001184801 72814143228786000888601)
              ·
                refine ⟨54610607421589500666451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72814143228786000888601 54610607421589500666451)
                ·
                  refine ⟨81915911132384250999677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54610607421589500666451 81915911132384250999677)
                  ·
                    refine ⟨30718466674644094124879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81915911132384250999677 30718466674644094124879)
                    ·
                      rfl

theorem cell22_89736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_89736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89736 prefixEnd_89736 := by exact prefixLift 89736
  have htrace : WordTrace (prefixWord ++ tailWord_89736) baseStart_89736 baseEnd_89736 := by
    simpa [prefixWord, tailWord_89736, baseEnd_89736] using wordTrace_append hprefix tailTrace_89736
  have hstable : (prefixWord ++ tailWord_89736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89736).length < 2 ^ (prefixWord ++ tailWord_89736).sum := by decide
  have hdescent : baseEnd_89736 < baseStart_89736 := by decide
  rcases family_descends (prefixWord ++ tailWord_89736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89758 : List Nat := [4, 3, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_89758 : Nat := 118140960795 + 89758 * 2 ^ 59
def prefixEnd_89758 : Nat := 4983230072969 + 3 ^ 40 * 89758 * 2
def baseEnd_89758 : Nat := 30725997724243370074811

theorem tailTrace_89758 : CollatzResearch.WordTrace tailWord_89758 prefixEnd_89758 30725997724243370074811 := by
  unfold tailWord_89758
  simp only [CollatzResearch.WordTrace]
  refine ⟨409217901103696286383741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2182495472553046860713285 409217901103696286383741)
  ·
    refine ⟨153456712913886107393903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 409217901103696286383741 153456712913886107393903)
    ·
      refine ⟨230185069370829161090855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153456712913886107393903 230185069370829161090855)
      ·
        refine ⟨345277604056243741636283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230185069370829161090855 345277604056243741636283)
        ·
          refine ⟨517916406084365612454425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345277604056243741636283 517916406084365612454425)
          ·
            refine ⟨388437304563274209340819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 517916406084365612454425 388437304563274209340819)
            ·
              refine ⟨582655956844911314011229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388437304563274209340819 582655956844911314011229)
              ·
                refine ⟨218495983816841742754211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 582655956844911314011229 218495983816841742754211)
                ·
                  refine ⟨327743975725262614131317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218495983816841742754211 327743975725262614131317)
                  ·
                    refine ⟨30725997724243370074811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 327743975725262614131317 30725997724243370074811)
                    ·
                      rfl

theorem cell22_89758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_89758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89758 prefixEnd_89758 := by exact prefixLift 89758
  have htrace : WordTrace (prefixWord ++ tailWord_89758) baseStart_89758 baseEnd_89758 := by
    simpa [prefixWord, tailWord_89758, baseEnd_89758] using wordTrace_append hprefix tailTrace_89758
  have hstable : (prefixWord ++ tailWord_89758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89758).length < 2 ^ (prefixWord ++ tailWord_89758).sum := by decide
  have hdescent : baseEnd_89758 < baseStart_89758 := by decide
  rcases family_descends (prefixWord ++ tailWord_89758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89837 : List Nat := [1, 5, 1, 2, 1, 2, 3, 3, 1, 3]
def baseStart_89837 : Nat := 118140960795 + 89837 * 2 ^ 59
def prefixEnd_89837 : Nat := 4983230072969 + 3 ^ 40 * 89837 * 2
def baseEnd_89837 : Nat := 30753041038713497349569

theorem tailTrace_89837 : CollatzResearch.WordTrace tailWord_89837 prefixEnd_89837 30753041038713497349569 := by
  unfold tailWord_89837
  simp only [CollatzResearch.WordTrace]
  refine ⟨3276624575543366783195765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2184416383695577855463843 3276624575543366783195765)
  ·
    refine ⟨307183553957190635924603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3276624575543366783195765 307183553957190635924603)
    ·
      refine ⟨460775330935785953886905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307183553957190635924603 460775330935785953886905)
      ·
        refine ⟨345581498201839465415179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 460775330935785953886905 345581498201839465415179)
        ·
          refine ⟨518372247302759198122769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345581498201839465415179 518372247302759198122769)
          ·
            refine ⟨388779185477069398592077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 518372247302759198122769 388779185477069398592077)
            ·
              refine ⟨145792194553901024472029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 388779185477069398592077 145792194553901024472029)
              ·
                refine ⟨54672072957712884177011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145792194553901024472029 54672072957712884177011)
                ·
                  refine ⟨82008109436569326265517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54672072957712884177011 82008109436569326265517)
                  ·
                    refine ⟨30753041038713497349569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82008109436569326265517 30753041038713497349569)
                    ·
                      rfl

theorem cell22_89837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_89837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89837 prefixEnd_89837 := by exact prefixLift 89837
  have htrace : WordTrace (prefixWord ++ tailWord_89837) baseStart_89837 baseEnd_89837 := by
    simpa [prefixWord, tailWord_89837, baseEnd_89837] using wordTrace_append hprefix tailTrace_89837
  have hstable : (prefixWord ++ tailWord_89837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89837).length < 2 ^ (prefixWord ++ tailWord_89837).sum := by decide
  have hdescent : baseEnd_89837 < baseStart_89837 := by decide
  rcases family_descends (prefixWord ++ tailWord_89837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89854 : List Nat := [4, 2, 2, 1, 4, 1, 1, 1, 3, 3]
def baseStart_89854 : Nat := 118140960795 + 89854 * 2 ^ 59
def prefixEnd_89854 : Nat := 4983230072969 + 3 ^ 40 * 89854 * 2
def baseEnd_89854 : Nat := 30758860486131119674517

theorem tailTrace_89854 : CollatzResearch.WordTrace tailWord_89854 prefixEnd_89854 30758860486131119674517 := by
  unfold tailWord_89854
  simp only [CollatzResearch.WordTrace]
  refine ⟨409655577060222335820577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2184829744321185791043077 409655577060222335820577)
  ·
    refine ⟨307241682795166751865433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 409655577060222335820577 307241682795166751865433)
    ·
      refine ⟨230431262096375063899075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307241682795166751865433 230431262096375063899075)
      ·
        refine ⟨345646893144562595848613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230431262096375063899075 345646893144562595848613)
        ·
          refine ⟨64808792464605486721615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 345646893144562595848613 64808792464605486721615)
          ·
            refine ⟨97213188696908230082423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64808792464605486721615 97213188696908230082423)
            ·
              refine ⟨145819783045362345123635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97213188696908230082423 145819783045362345123635)
              ·
                refine ⟨218729674568043517685453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145819783045362345123635 218729674568043517685453)
                ·
                  refine ⟨82023627963016319132045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218729674568043517685453 82023627963016319132045)
                  ·
                    refine ⟨30758860486131119674517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82023627963016319132045 30758860486131119674517)
                    ·
                      rfl

theorem cell22_89854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_89854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89854 prefixEnd_89854 := by exact prefixLift 89854
  have htrace : WordTrace (prefixWord ++ tailWord_89854) baseStart_89854 baseEnd_89854 := by
    simpa [prefixWord, tailWord_89854, baseEnd_89854] using wordTrace_append hprefix tailTrace_89854
  have hstable : (prefixWord ++ tailWord_89854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89854).length < 2 ^ (prefixWord ++ tailWord_89854).sum := by decide
  have hdescent : baseEnd_89854 < baseStart_89854 := by decide
  rcases family_descends (prefixWord ++ tailWord_89854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89891 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 1, 6]
def baseStart_89891 : Nat := 118140960795 + 89891 * 2 ^ 59
def prefixEnd_89891 : Nat := 4983230072969 + 3 ^ 40 * 89891 * 2
def baseEnd_89891 : Nat := 30771526342275356499403

theorem tailTrace_89891 : CollatzResearch.WordTrace tailWord_89891 prefixEnd_89891 30771526342275356499403 := by
  unfold tailWord_89891
  simp only [CollatzResearch.WordTrace]
  refine ⟨3278594117347734005661527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2185729411565156003774351 3278594117347734005661527)
  ·
    refine ⟨4917891176021601008492291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3278594117347734005661527 4917891176021601008492291)
    ·
      refine ⟨7376836764032401512738437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4917891176021601008492291 7376836764032401512738437)
      ·
        refine ⟨1383156893256075283638457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7376836764032401512738437 1383156893256075283638457)
        ·
          refine ⟨1037367669942056462728843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1383156893256075283638457 1037367669942056462728843)
          ·
            refine ⟨1556051504913084694093265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037367669942056462728843 1556051504913084694093265)
            ·
              refine ⟨1167038628684813520569949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1556051504913084694093265 1167038628684813520569949)
              ·
                refine ⟨437639485756805070213731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1167038628684813520569949 437639485756805070213731)
                ·
                  refine ⟨656459228635207605320597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 437639485756805070213731 656459228635207605320597)
                  ·
                    refine ⟨30771526342275356499403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 656459228635207605320597 30771526342275356499403)
                    ·
                      rfl

theorem cell22_89891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 6].length) (baseStart_89891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89891 prefixEnd_89891 := by exact prefixLift 89891
  have htrace : WordTrace (prefixWord ++ tailWord_89891) baseStart_89891 baseEnd_89891 := by
    simpa [prefixWord, tailWord_89891, baseEnd_89891] using wordTrace_append hprefix tailTrace_89891
  have hstable : (prefixWord ++ tailWord_89891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89891).length < 2 ^ (prefixWord ++ tailWord_89891).sum := by decide
  have hdescent : baseEnd_89891 < baseStart_89891 := by decide
  rcases family_descends (prefixWord ++ tailWord_89891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89893 : List Nat := [1, 3, 1, 2, 3, 3, 1, 2, 1, 5]
def baseStart_89893 : Nat := 118140960795 + 89893 * 2 ^ 59
def prefixEnd_89893 : Nat := 4983230072969 + 3 ^ 40 * 89893 * 2
def baseEnd_89893 : Nat := 30772210983148017949397

theorem tailTrace_89893 : CollatzResearch.WordTrace tailWord_89893 prefixEnd_89893 30772210983148017949397 := by
  unfold tailWord_89893
  simp only [CollatzResearch.WordTrace]
  refine ⟨3278667063340488347234333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2185778042226992231489555 3278667063340488347234333)
  ·
    refine ⟨1229500148752683130212875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3278667063340488347234333 1229500148752683130212875)
    ·
      refine ⟨1844250223129024695319313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1229500148752683130212875 1844250223129024695319313)
      ·
        refine ⟨1383187667346768521489485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1844250223129024695319313 1383187667346768521489485)
        ·
          refine ⟨518695375255038195558557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1383187667346768521489485 518695375255038195558557)
          ·
            refine ⟨194510765720639323334459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 518695375255038195558557 194510765720639323334459)
            ·
              refine ⟨291766148580958985001689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194510765720639323334459 291766148580958985001689)
              ·
                refine ⟨218824611435719238751267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291766148580958985001689 218824611435719238751267)
                ·
                  refine ⟨328236917153578858126901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218824611435719238751267 328236917153578858126901)
                  ·
                    refine ⟨30772210983148017949397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 328236917153578858126901 30772210983148017949397)
                    ·
                      rfl

theorem cell22_89893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_89893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89893 prefixEnd_89893 := by exact prefixLift 89893
  have htrace : WordTrace (prefixWord ++ tailWord_89893) baseStart_89893 baseEnd_89893 := by
    simpa [prefixWord, tailWord_89893, baseEnd_89893] using wordTrace_append hprefix tailTrace_89893
  have hstable : (prefixWord ++ tailWord_89893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89893).length < 2 ^ (prefixWord ++ tailWord_89893).sum := by decide
  have hdescent : baseEnd_89893 < baseStart_89893 := by decide
  rcases family_descends (prefixWord ++ tailWord_89893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89906 : List Nat := [3, 2, 1, 1, 3, 12]
def baseStart_89906 : Nat := 118140960795 + 89906 * 2 ^ 59
def prefixEnd_89906 : Nat := 4983230072969 + 3 ^ 40 * 89906 * 2
def baseEnd_89906 : Nat := 379958779615065646597

theorem tailTrace_89906 : CollatzResearch.WordTrace tailWord_89906 prefixEnd_89906 379958779615065646597 := by
  unfold tailWord_89906
  simp only [CollatzResearch.WordTrace]
  refine ⟨819785303073347891864393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2186094141528927711638381 819785303073347891864393)
  ·
    refine ⟨614838977305010918898295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 819785303073347891864393 614838977305010918898295)
    ·
      refine ⟨922258465957516378347443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 614838977305010918898295 922258465957516378347443)
      ·
        refine ⟨1383387698936274567521165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 922258465957516378347443 1383387698936274567521165)
        ·
          refine ⟨518770387101102962820437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1383387698936274567521165 518770387101102962820437)
          ·
            refine ⟨379958779615065646597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 518770387101102962820437 379958779615065646597)
            ·
              rfl

theorem cell22_89906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 12].length) (baseStart_89906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89906 prefixEnd_89906 := by exact prefixLift 89906
  have htrace : WordTrace (prefixWord ++ tailWord_89906) baseStart_89906 baseEnd_89906 := by
    simpa [prefixWord, tailWord_89906, baseEnd_89906] using wordTrace_append hprefix tailTrace_89906
  have hstable : (prefixWord ++ tailWord_89906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89906).length < 2 ^ (prefixWord ++ tailWord_89906).sum := by decide
  have hdescent : baseEnd_89906 < baseStart_89906 := by decide
  rcases family_descends (prefixWord ++ tailWord_89906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89912 : List Nat := [2, 1, 2, 1, 3, 5, 2, 2, 4]
def baseStart_89912 : Nat := 118140960795 + 89912 * 2 ^ 59
def prefixEnd_89912 : Nat := 4983230072969 + 3 ^ 40 * 89912 * 2
def baseEnd_89912 : Nat := 10259571690479433908113

theorem tailTrace_89912 : CollatzResearch.WordTrace tailWord_89912 prefixEnd_89912 10259571690479433908113 := by
  unfold tailWord_89912
  simp only [CollatzResearch.WordTrace]
  refine ⟨1639680025135827296087995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2186240033514436394783993 1639680025135827296087995)
  ·
    refine ⟨2459520037703740944131993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1639680025135827296087995 2459520037703740944131993)
    ·
      refine ⟨1844640028277805708098995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2459520037703740944131993 1844640028277805708098995)
      ·
        refine ⟨2766960042416708562148493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1844640028277805708098995 2766960042416708562148493)
        ·
          refine ⟨1037610015906265710805685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2766960042416708562148493 1037610015906265710805685)
          ·
            refine ⟨97275938991212410388033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1037610015906265710805685 97275938991212410388033)
            ·
              refine ⟨72956954243409307791025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97275938991212410388033 72956954243409307791025)
              ·
                refine ⟨54717715682556980843269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72956954243409307791025 54717715682556980843269)
                ·
                  refine ⟨10259571690479433908113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54717715682556980843269 10259571690479433908113)
                  ·
                    rfl

theorem cell22_89912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 4].length) (baseStart_89912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89912 prefixEnd_89912 := by exact prefixLift 89912
  have htrace : WordTrace (prefixWord ++ tailWord_89912) baseStart_89912 baseEnd_89912 := by
    simpa [prefixWord, tailWord_89912, baseEnd_89912] using wordTrace_append hprefix tailTrace_89912
  have hstable : (prefixWord ++ tailWord_89912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89912).length < 2 ^ (prefixWord ++ tailWord_89912).sum := by decide
  have hdescent : baseEnd_89912 < baseStart_89912 := by decide
  rcases family_descends (prefixWord ++ tailWord_89912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89923 : List Nat := [1, 1, 1, 3, 1, 7, 1, 7]
def baseStart_89923 : Nat := 118140960795 + 89923 * 2 ^ 59
def prefixEnd_89923 : Nat := 4983230072969 + 3 ^ 40 * 89923 * 2
def baseEnd_89923 : Nat := 3420275621804215522145

theorem tailTrace_89923 : CollatzResearch.WordTrace tailWord_89923 prefixEnd_89923 3420275621804215522145 := by
  unfold tailWord_89923
  simp only [CollatzResearch.WordTrace]
  refine ⟨3279761253231803470826423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2186507502154535647217615 3279761253231803470826423)
  ·
    refine ⟨4919641879847705206239635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3279761253231803470826423 4919641879847705206239635)
    ·
      refine ⟨7379462819771557809359453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4919641879847705206239635 7379462819771557809359453)
      ·
        refine ⟨2767298557414334178509795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7379462819771557809359453 2767298557414334178509795)
        ·
          refine ⟨4150947836121501267764693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2767298557414334178509795 4150947836121501267764693)
          ·
            refine ⟨97287839909097685963235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 4150947836121501267764693 97287839909097685963235)
            ·
              refine ⟨145931759863646528944853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97287839909097685963235 145931759863646528944853)
              ·
                refine ⟨3420275621804215522145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 145931759863646528944853 3420275621804215522145)
                ·
                  rfl

theorem cell22_89923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 7].length) (baseStart_89923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89923 prefixEnd_89923 := by exact prefixLift 89923
  have htrace : WordTrace (prefixWord ++ tailWord_89923) baseStart_89923 baseEnd_89923 := by
    simpa [prefixWord, tailWord_89923, baseEnd_89923] using wordTrace_append hprefix tailTrace_89923
  have hstable : (prefixWord ++ tailWord_89923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89923).length < 2 ^ (prefixWord ++ tailWord_89923).sum := by decide
  have hdescent : baseEnd_89923 < baseStart_89923 := by decide
  rcases family_descends (prefixWord ++ tailWord_89923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89936 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 4, 6]
def baseStart_89936 : Nat := 118140960795 + 89936 * 2 ^ 59
def prefixEnd_89936 : Nat := 4983230072969 + 3 ^ 40 * 89936 * 2
def baseEnd_89936 : Nat := 30786930761910239124265

theorem tailTrace_89936 : CollatzResearch.WordTrace tailWord_89936 prefixEnd_89936 30786930761910239124265 := by
  unfold tailWord_89936
  simp only [CollatzResearch.WordTrace]
  refine ⟨1640117701092353345524831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2186823601456471127366441 1640117701092353345524831)
  ·
    refine ⟨2460176551638530018287247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1640117701092353345524831 2460176551638530018287247)
    ·
      refine ⟨3690264827457795027430871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2460176551638530018287247 3690264827457795027430871)
      ·
        refine ⟨5535397241186692541146307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3690264827457795027430871 5535397241186692541146307)
        ·
          refine ⟨8303095861780038811719461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5535397241186692541146307 8303095861780038811719461)
          ·
            refine ⟨1556830474083757277197399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8303095861780038811719461 1556830474083757277197399)
            ·
              refine ⟨2335245711125635915796099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1556830474083757277197399 2335245711125635915796099)
              ·
                refine ⟨3502868566688453873694149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2335245711125635915796099 3502868566688453873694149)
                ·
                  refine ⟨656787856254085101317653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3502868566688453873694149 656787856254085101317653)
                  ·
                    refine ⟨30786930761910239124265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 656787856254085101317653 30786930761910239124265)
                    ·
                      rfl

theorem cell22_89936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_89936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89936 prefixEnd_89936 := by exact prefixLift 89936
  have htrace : WordTrace (prefixWord ++ tailWord_89936) baseStart_89936 baseEnd_89936 := by
    simpa [prefixWord, tailWord_89936, baseEnd_89936] using wordTrace_append hprefix tailTrace_89936
  have hstable : (prefixWord ++ tailWord_89936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89936).length < 2 ^ (prefixWord ++ tailWord_89936).sum := by decide
  have hdescent : baseEnd_89936 < baseStart_89936 := by decide
  rcases family_descends (prefixWord ++ tailWord_89936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89940 : List Nat := [2, 4, 1, 1, 3, 2, 3, 6]
def baseStart_89940 : Nat := 118140960795 + 89940 * 2 ^ 59
def prefixEnd_89940 : Nat := 4983230072969 + 3 ^ 40 * 89940 * 2
def baseEnd_89940 : Nat := 3420922227072840224917

theorem tailTrace_89940 : CollatzResearch.WordTrace tailWord_89940 prefixEnd_89940 3420922227072840224917 := by
  unfold tailWord_89940
  simp only [CollatzResearch.WordTrace]
  refine ⟨1640190647085107687097637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2186920862780143582796849 1640190647085107687097637)
  ·
    refine ⟨307535746328457691330807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1640190647085107687097637 307535746328457691330807)
    ·
      refine ⟨461303619492686536996211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307535746328457691330807 461303619492686536996211)
      ·
        refine ⟨691955429239029805494317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461303619492686536996211 691955429239029805494317)
        ·
          refine ⟨259483285964636177060369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 691955429239029805494317 259483285964636177060369)
          ·
            refine ⟨194612464473477132795277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259483285964636177060369 194612464473477132795277)
            ·
              refine ⟨72979674177553924798229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194612464473477132795277 72979674177553924798229)
              ·
                refine ⟨3420922227072840224917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72979674177553924798229 3420922227072840224917)
                ·
                  rfl

theorem cell22_89940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 6].length) (baseStart_89940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89940 prefixEnd_89940 := by exact prefixLift 89940
  have htrace : WordTrace (prefixWord ++ tailWord_89940) baseStart_89940 baseEnd_89940 := by
    simpa [prefixWord, tailWord_89940, baseEnd_89940] using wordTrace_append hprefix tailTrace_89940
  have hstable : (prefixWord ++ tailWord_89940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89940).length < 2 ^ (prefixWord ++ tailWord_89940).sum := by decide
  have hdescent : baseEnd_89940 < baseStart_89940 := by decide
  rcases family_descends (prefixWord ++ tailWord_89940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90036 : List Nat := [2, 5, 2, 1, 2, 2, 2, 1, 5]
def baseStart_90036 : Nat := 118140960795 + 90036 * 2 ^ 59
def prefixEnd_90036 : Nat := 4983230072969 + 3 ^ 40 * 90036 * 2
def baseEnd_90036 : Nat := 10273720935181103874653

theorem tailTrace_90036 : CollatzResearch.WordTrace tailWord_90036 prefixEnd_90036 10273720935181103874653 := by
  unfold tailWord_90036
  simp only [CollatzResearch.WordTrace]
  refine ⟨1641941350911211884844981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2189255134548282513126641 1641941350911211884844981)
  ·
    refine ⟨153932001647926114204217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1641941350911211884844981 153932001647926114204217)
    ·
      refine ⟨115449001235944585653163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153932001647926114204217 115449001235944585653163)
      ·
        refine ⟨173173501853916878479745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115449001235944585653163 173173501853916878479745)
        ·
          refine ⟨129880126390437658859809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173173501853916878479745 129880126390437658859809)
          ·
            refine ⟨97410094792828244144857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129880126390437658859809 97410094792828244144857)
            ·
              refine ⟨73057571094621183108643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97410094792828244144857 73057571094621183108643)
              ·
                refine ⟨109586356641931774662965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73057571094621183108643 109586356641931774662965)
                ·
                  refine ⟨10273720935181103874653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109586356641931774662965 10273720935181103874653)
                  ·
                    rfl

theorem cell22_90036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_90036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90036 prefixEnd_90036 := by exact prefixLift 90036
  have htrace : WordTrace (prefixWord ++ tailWord_90036) baseStart_90036 baseEnd_90036 := by
    simpa [prefixWord, tailWord_90036, baseEnd_90036] using wordTrace_append hprefix tailTrace_90036
  have hstable : (prefixWord ++ tailWord_90036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90036).length < 2 ^ (prefixWord ++ tailWord_90036).sum := by decide
  have hdescent : baseEnd_90036 < baseStart_90036 := by decide
  rcases family_descends (prefixWord ++ tailWord_90036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90058 : List Nat := [3, 1, 2, 1, 2, 1, 4, 8]
def baseStart_90058 : Nat := 118140960795 + 90058 * 2 ^ 59
def prefixEnd_90058 : Nat := 4983230072969 + 3 ^ 40 * 90058 * 2
def baseEnd_90058 : Nat := 3425410428349176397099

theorem tailTrace_90058 : CollatzResearch.WordTrace tailWord_90058 prefixEnd_90058 3425410428349176397099 := by
  unfold tailWord_90058
  simp only [CollatzResearch.WordTrace]
  refine ⟨821171276935680381747707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2189790071828481017993885 821171276935680381747707)
  ·
    refine ⟨1231756915403520572621561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 821171276935680381747707 1231756915403520572621561)
    ·
      refine ⟨923817686552640429466171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1231756915403520572621561 923817686552640429466171)
      ·
        refine ⟨1385726529828960644199257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 923817686552640429466171 1385726529828960644199257)
        ·
          refine ⟨1039294897371720483149443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1385726529828960644199257 1039294897371720483149443)
          ·
            refine ⟨1558942346057580724724165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1039294897371720483149443 1558942346057580724724165)
            ·
              refine ⟨292301689885796385885781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1558942346057580724724165 292301689885796385885781)
              ·
                refine ⟨3425410428349176397099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 292301689885796385885781 3425410428349176397099)
                ·
                  rfl

theorem cell22_90058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 8].length) (baseStart_90058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90058 prefixEnd_90058 := by exact prefixLift 90058
  have htrace : WordTrace (prefixWord ++ tailWord_90058) baseStart_90058 baseEnd_90058 := by
    simpa [prefixWord, tailWord_90058, baseEnd_90058] using wordTrace_append hprefix tailTrace_90058
  have hstable : (prefixWord ++ tailWord_90058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90058).length < 2 ^ (prefixWord ++ tailWord_90058).sum := by decide
  have hdescent : baseEnd_90058 < baseStart_90058 := by decide
  rcases family_descends (prefixWord ++ tailWord_90058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90060 : List Nat := [2, 2, 1, 4, 1, 2, 1, 3, 2, 4]
def baseStart_90060 : Nat := 118140960795 + 90060 * 2 ^ 59
def prefixEnd_90060 : Nat := 4983230072969 + 3 ^ 40 * 90060 * 2
def baseEnd_90060 : Nat := 30829378496015249023885

theorem tailTrace_90060 : CollatzResearch.WordTrace tailWord_90060 prefixEnd_90060 30829378496015249023885 := by
  unfold tailWord_90060
  simp only [CollatzResearch.WordTrace]
  refine ⟨1642379026867737934281817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2189838702490317245709089 1642379026867737934281817)
  ·
    refine ⟨1231784270150803450711363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1642379026867737934281817 1231784270150803450711363)
    ·
      refine ⟨1847676405226205176067045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1231784270150803450711363 1847676405226205176067045)
      ·
        refine ⟨346439325979913470512571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1847676405226205176067045 346439325979913470512571)
        ·
          refine ⟨519658988969870205768857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346439325979913470512571 519658988969870205768857)
          ·
            refine ⟨389744241727402654326643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 519658988969870205768857 389744241727402654326643)
            ·
              refine ⟨584616362591103981489965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389744241727402654326643 584616362591103981489965)
              ·
                refine ⟨219231135971663993058737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 584616362591103981489965 219231135971663993058737)
                ·
                  refine ⟨164423351978747994794053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219231135971663993058737 164423351978747994794053)
                  ·
                    refine ⟨30829378496015249023885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 164423351978747994794053 30829378496015249023885)
                    ·
                      rfl

theorem cell22_90060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_90060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90060 prefixEnd_90060 := by exact prefixLift 90060
  have htrace : WordTrace (prefixWord ++ tailWord_90060) baseStart_90060 baseEnd_90060 := by
    simpa [prefixWord, tailWord_90060, baseEnd_90060] using wordTrace_append hprefix tailTrace_90060
  have hstable : (prefixWord ++ tailWord_90060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90060).length < 2 ^ (prefixWord ++ tailWord_90060).sum := by decide
  have hdescent : baseEnd_90060 < baseStart_90060 := by decide
  rcases family_descends (prefixWord ++ tailWord_90060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90124 : List Nat := [2, 2, 1, 2, 3, 1, 4, 3, 1, 3]
def baseStart_90124 : Nat := 118140960795 + 90124 * 2 ^ 59
def prefixEnd_90124 : Nat := 4983230072969 + 3 ^ 40 * 90124 * 2
def baseEnd_90124 : Nat := 30851287003940415423689

theorem tailTrace_90124 : CollatzResearch.WordTrace tailWord_90124 prefixEnd_90124 30851287003940415423689 := by
  unfold tailWord_90124
  simp only [CollatzResearch.WordTrace]
  refine ⟨1643546162751807399446713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2191394883669076532595617 1643546162751807399446713)
  ·
    refine ⟨1232659622063855549585035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1643546162751807399446713 1232659622063855549585035)
    ·
      refine ⟨1848989433095783324377553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1232659622063855549585035 1848989433095783324377553)
      ·
        refine ⟨1386742074821837493283165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1848989433095783324377553 1386742074821837493283165)
        ·
          refine ⟨520028278058189059981187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1386742074821837493283165 520028278058189059981187)
          ·
            refine ⟨780042417087283589971781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520028278058189059981187 780042417087283589971781)
            ·
              refine ⟨146257953203865673119709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 780042417087283589971781 146257953203865673119709)
              ·
                refine ⟨54846732451449627419891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146257953203865673119709 54846732451449627419891)
                ·
                  refine ⟨82270098677174441129837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54846732451449627419891 82270098677174441129837)
                  ·
                    refine ⟨30851287003940415423689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82270098677174441129837 30851287003940415423689)
                    ·
                      rfl

theorem cell22_90124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 1, 3].length) (baseStart_90124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90124 prefixEnd_90124 := by exact prefixLift 90124
  have htrace : WordTrace (prefixWord ++ tailWord_90124) baseStart_90124 baseEnd_90124 := by
    simpa [prefixWord, tailWord_90124, baseEnd_90124] using wordTrace_append hprefix tailTrace_90124
  have hstable : (prefixWord ++ tailWord_90124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90124).length < 2 ^ (prefixWord ++ tailWord_90124).sum := by decide
  have hdescent : baseEnd_90124 < baseStart_90124 := by decide
  rcases family_descends (prefixWord ++ tailWord_90124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90154 : List Nat := [3, 1, 4, 1, 2, 2, 3, 1, 5]
def baseStart_90154 : Nat := 118140960795 + 90154 * 2 ^ 59
def prefixEnd_90154 : Nat := 4983230072969 + 3 ^ 40 * 90154 * 2
def baseEnd_90154 : Nat := 10287185539010112391199

theorem tailTrace_90154 : CollatzResearch.WordTrace tailWord_90154 prefixEnd_90154 10287185539010112391199 := by
  unfold tailWord_90154
  simp only [CollatzResearch.WordTrace]
  refine ⟨822046628848732480621379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2192124343596619948323677 822046628848732480621379)
  ·
    refine ⟨1233069943273098720932069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 822046628848732480621379 1233069943273098720932069)
    ·
      refine ⟨231200614363706010174763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1233069943273098720932069 231200614363706010174763)
      ·
        refine ⟨346800921545559015262145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231200614363706010174763 346800921545559015262145)
        ·
          refine ⟨260100691159169261446609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346800921545559015262145 260100691159169261446609)
          ·
            refine ⟨195075518369376946084957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260100691159169261446609 195075518369376946084957)
            ·
              refine ⟨73153319388516354781859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195075518369376946084957 73153319388516354781859)
              ·
                refine ⟨109729979082774532172789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73153319388516354781859 109729979082774532172789)
                ·
                  refine ⟨10287185539010112391199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109729979082774532172789 10287185539010112391199)
                  ·
                    rfl

theorem cell22_90154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 5].length) (baseStart_90154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90154 prefixEnd_90154 := by exact prefixLift 90154
  have htrace : WordTrace (prefixWord ++ tailWord_90154) baseStart_90154 baseEnd_90154 := by
    simpa [prefixWord, tailWord_90154, baseEnd_90154] using wordTrace_append hprefix tailTrace_90154
  have hstable : (prefixWord ++ tailWord_90154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90154).length < 2 ^ (prefixWord ++ tailWord_90154).sum := by decide
  have hdescent : baseEnd_90154 < baseStart_90154 := by decide
  rcases family_descends (prefixWord ++ tailWord_90154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90165 : List Nat := [1, 3, 3, 1, 1, 1, 4, 2, 6]
def baseStart_90165 : Nat := 118140960795 + 90165 * 2 ^ 59
def prefixEnd_90165 : Nat := 4983230072969 + 3 ^ 40 * 90165 * 2
def baseEnd_90165 : Nat := 10288440713943325049521

theorem tailTrace_90165 : CollatzResearch.WordTrace tailWord_90165 prefixEnd_90165 10288440713943325049521 := by
  unfold tailWord_90165
  simp only [CollatzResearch.WordTrace]
  refine ⟨3288587718355078801135949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2192391812236719200757299 3288587718355078801135949)
  ·
    refine ⟨1233220394383154550425981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3288587718355078801135949 1233220394383154550425981)
    ·
      refine ⟨462457647893682956409743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1233220394383154550425981 462457647893682956409743)
      ·
        refine ⟨693686471840524434614615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462457647893682956409743 693686471840524434614615)
        ·
          refine ⟨1040529707760786651921923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 693686471840524434614615 1040529707760786651921923)
          ·
            refine ⟨1560794561641179977882885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040529707760786651921923 1560794561641179977882885)
            ·
              refine ⟨292648980307721245853041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1560794561641179977882885 292648980307721245853041)
              ·
                refine ⟨219486735230790934389781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292648980307721245853041 219486735230790934389781)
                ·
                  refine ⟨10288440713943325049521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 219486735230790934389781 10288440713943325049521)
                  ·
                    rfl

theorem cell22_90165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_90165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90165 prefixEnd_90165 := by exact prefixLift 90165
  have htrace : WordTrace (prefixWord ++ tailWord_90165) baseStart_90165 baseEnd_90165 := by
    simpa [prefixWord, tailWord_90165, baseEnd_90165] using wordTrace_append hprefix tailTrace_90165
  have hstable : (prefixWord ++ tailWord_90165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90165).length < 2 ^ (prefixWord ++ tailWord_90165).sum := by decide
  have hdescent : baseEnd_90165 < baseStart_90165 := by decide
  rcases family_descends (prefixWord ++ tailWord_90165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90197 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 4, 3]
def baseStart_90197 : Nat := 118140960795 + 90197 * 2 ^ 59
def prefixEnd_90197 : Nat := 4983230072969 + 3 ^ 40 * 90197 * 2
def baseEnd_90197 : Nat := 30876276395792558348465

theorem tailTrace_90197 : CollatzResearch.WordTrace tailWord_90197 prefixEnd_90197 30876276395792558348465 := by
  unfold tailWord_90197
  simp only [CollatzResearch.WordTrace]
  refine ⟨3289754854239148266300845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2193169902826098844200563 3289754854239148266300845)
  ·
    refine ⟨1233658070339680599862817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3289754854239148266300845 1233658070339680599862817)
    ·
      refine ⟨925243552754760449897113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1233658070339680599862817 925243552754760449897113)
      ·
        refine ⟨693932664566070337422835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 925243552754760449897113 693932664566070337422835)
        ·
          refine ⟨1040898996849105506134253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 693932664566070337422835 1040898996849105506134253)
          ·
            refine ⟨390337123818414564800345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1040898996849105506134253 390337123818414564800345)
            ·
              refine ⟨292752842863810923600259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390337123818414564800345 292752842863810923600259)
              ·
                refine ⟨439129264295716385400389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292752842863810923600259 439129264295716385400389)
                ·
                  refine ⟨82336737055446822262573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 439129264295716385400389 82336737055446822262573)
                  ·
                    refine ⟨30876276395792558348465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82336737055446822262573 30876276395792558348465)
                    ·
                      rfl

theorem cell22_90197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_90197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90197 prefixEnd_90197 := by exact prefixLift 90197
  have htrace : WordTrace (prefixWord ++ tailWord_90197) baseStart_90197 baseEnd_90197 := by
    simpa [prefixWord, tailWord_90197, baseEnd_90197] using wordTrace_append hprefix tailTrace_90197
  have hstable : (prefixWord ++ tailWord_90197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90197).length < 2 ^ (prefixWord ++ tailWord_90197).sum := by decide
  have hdescent : baseEnd_90197 < baseStart_90197 := by decide
  rcases family_descends (prefixWord ++ tailWord_90197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90272 : List Nat := [2, 1, 1, 4, 2, 2, 2, 3, 5]
def baseStart_90272 : Nat := 118140960795 + 90272 * 2 ^ 59
def prefixEnd_90272 : Nat := 4983230072969 + 3 ^ 40 * 90272 * 2
def baseEnd_90272 : Nat := 10300650142839120907745

theorem tailTrace_90272 : CollatzResearch.WordTrace tailWord_90272 prefixEnd_90272 10300650142839120907745 := by
  unfold tailWord_90272
  simp only [CollatzResearch.WordTrace]
  refine ⟨1646245164483718037640535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2194993552644957383520713 1646245164483718037640535)
  ·
    refine ⟨2469367746725577056460803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1646245164483718037640535 2469367746725577056460803)
    ·
      refine ⟨3704051620088365584691205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2469367746725577056460803 3704051620088365584691205)
      ·
        refine ⟨694509678766568547129601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3704051620088365584691205 694509678766568547129601)
        ·
          refine ⟨520882259074926410347201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 694509678766568547129601 520882259074926410347201)
          ·
            refine ⟨390661694306194807760401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 520882259074926410347201 390661694306194807760401)
            ·
              refine ⟨292996270729646105820301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390661694306194807760401 292996270729646105820301)
              ·
                refine ⟨109873601523617289682613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292996270729646105820301 109873601523617289682613)
                ·
                  refine ⟨10300650142839120907745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109873601523617289682613 10300650142839120907745)
                  ·
                    rfl

theorem cell22_90272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 5].length) (baseStart_90272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90272 prefixEnd_90272 := by exact prefixLift 90272
  have htrace : WordTrace (prefixWord ++ tailWord_90272) baseStart_90272 baseEnd_90272 := by
    simpa [prefixWord, tailWord_90272, baseEnd_90272] using wordTrace_append hprefix tailTrace_90272
  have hstable : (prefixWord ++ tailWord_90272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90272).length < 2 ^ (prefixWord ++ tailWord_90272).sum := by decide
  have hdescent : baseEnd_90272 < baseStart_90272 := by decide
  rcases family_descends (prefixWord ++ tailWord_90272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90306 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 7]
def baseStart_90306 : Nat := 118140960795 + 90306 * 2 ^ 59
def prefixEnd_90306 : Nat := 4983230072969 + 3 ^ 40 * 90306 * 2
def baseEnd_90306 : Nat := 10304529774450869124377

theorem tailTrace_90306 : CollatzResearch.WordTrace tailWord_90306 prefixEnd_90306 10304529774450869124377 := by
  unfold tailWord_90306
  simp only [CollatzResearch.WordTrace]
  refine ⟨823432602711064970504693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2195820273896173254679181 823432602711064970504693)
  ·
    refine ⟨77196806504162340984815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 823432602711064970504693 77196806504162340984815)
    ·
      refine ⟨115795209756243511477223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77196806504162340984815 115795209756243511477223)
      ·
        refine ⟨173692814634365267215835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115795209756243511477223 173692814634365267215835)
        ·
          refine ⟨260539221951547900823753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173692814634365267215835 260539221951547900823753)
          ·
            refine ⟨195404416463660925617815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260539221951547900823753 195404416463660925617815)
            ·
              refine ⟨293106624695491388426723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195404416463660925617815 293106624695491388426723)
              ·
                refine ⟨439659937043237082640085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 293106624695491388426723 439659937043237082640085)
                ·
                  refine ⟨10304529774450869124377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 439659937043237082640085 10304529774450869124377)
                  ·
                    rfl

theorem cell22_90306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_90306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90306 prefixEnd_90306 := by exact prefixLift 90306
  have htrace : WordTrace (prefixWord ++ tailWord_90306) baseStart_90306 baseEnd_90306 := by
    simpa [prefixWord, tailWord_90306, baseEnd_90306] using wordTrace_append hprefix tailTrace_90306
  have hstable : (prefixWord ++ tailWord_90306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90306).length < 2 ^ (prefixWord ++ tailWord_90306).sum := by decide
  have hdescent : baseEnd_90306 < baseStart_90306 := by decide
  rcases family_descends (prefixWord ++ tailWord_90306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90345 : List Nat := [1, 2, 1, 1, 1, 2, 2, 12]
def baseStart_90345 : Nat := 118140960795 + 90345 * 2 ^ 59
def prefixEnd_90345 : Nat := 4983230072969 + 3 ^ 40 * 90345 * 2
def baseEnd_90345 : Nat := 3436326646707722849779

theorem tailTrace_90345 : CollatzResearch.WordTrace tailWord_90345 prefixEnd_90345 3436326646707722849779 := by
  unfold tailWord_90345
  simp only [CollatzResearch.WordTrace]
  refine ⟨3295152857702969542688489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2196768571801979695125659 3295152857702969542688489)
  ·
    refine ⟨2471364643277227157016367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3295152857702969542688489 2471364643277227157016367)
    ·
      refine ⟨3707046964915840735524551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2471364643277227157016367 3707046964915840735524551)
      ·
        refine ⟨5560570447373761103286827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3707046964915840735524551 5560570447373761103286827)
        ·
          refine ⟨8340855671060641654930241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5560570447373761103286827 8340855671060641654930241)
          ·
            refine ⟨6255641753295481241197681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8340855671060641654930241 6255641753295481241197681)
            ·
              refine ⟨4691731314971610930898261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6255641753295481241197681 4691731314971610930898261)
              ·
                refine ⟨3436326646707722849779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 4691731314971610930898261 3436326646707722849779)
                ·
                  rfl

theorem cell22_90345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 12].length) (baseStart_90345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90345 prefixEnd_90345 := by exact prefixLift 90345
  have htrace : WordTrace (prefixWord ++ tailWord_90345) baseStart_90345 baseEnd_90345 := by
    simpa [prefixWord, tailWord_90345, baseEnd_90345] using wordTrace_append hprefix tailTrace_90345
  have hstable : (prefixWord ++ tailWord_90345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90345).length < 2 ^ (prefixWord ++ tailWord_90345).sum := by decide
  have hdescent : baseEnd_90345 < baseStart_90345 := by decide
  rcases family_descends (prefixWord ++ tailWord_90345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90347 : List Nat := [1, 1, 1, 1, 2, 5, 2, 3, 2, 4]
def baseStart_90347 : Nat := 118140960795 + 90347 * 2 ^ 59
def prefixEnd_90347 : Nat := 4983230072969 + 3 ^ 40 * 90347 * 2
def baseEnd_90347 : Nat := 30927624461242167098005

theorem tailTrace_90347 : CollatzResearch.WordTrace tailWord_90347 prefixEnd_90347 30927624461242167098005 := by
  unfold tailWord_90347
  simp only [CollatzResearch.WordTrace]
  refine ⟨3295225803695723884261295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2196817202463815922840863 3295225803695723884261295)
  ·
    refine ⟨4942838705543585826391943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3295225803695723884261295 4942838705543585826391943)
    ·
      refine ⟨7414258058315378739587915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4942838705543585826391943 7414258058315378739587915)
      ·
        refine ⟨11121387087473068109381873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7414258058315378739587915 11121387087473068109381873)
        ·
          refine ⟨8341040315604801082036405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11121387087473068109381873 8341040315604801082036405)
          ·
            refine ⟨781972529587950101440913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8341040315604801082036405 781972529587950101440913)
            ·
              refine ⟨586479397190962576080685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 781972529587950101440913 586479397190962576080685)
              ·
                refine ⟨219929773946610966030257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 586479397190962576080685 219929773946610966030257)
                ·
                  refine ⟨164947330459958224522693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219929773946610966030257 164947330459958224522693)
                  ·
                    refine ⟨30927624461242167098005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 164947330459958224522693 30927624461242167098005)
                    ·
                      rfl

theorem cell22_90347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 4].length) (baseStart_90347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90347 prefixEnd_90347 := by exact prefixLift 90347
  have htrace : WordTrace (prefixWord ++ tailWord_90347) baseStart_90347 baseEnd_90347 := by
    simpa [prefixWord, tailWord_90347, baseEnd_90347] using wordTrace_append hprefix tailTrace_90347
  have hstable : (prefixWord ++ tailWord_90347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90347).length < 2 ^ (prefixWord ++ tailWord_90347).sum := by decide
  have hdescent : baseEnd_90347 < baseStart_90347 := by decide
  rcases family_descends (prefixWord ++ tailWord_90347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90351 : List Nat := [1, 1, 2, 1, 6, 3, 1, 3, 4]
def baseStart_90351 : Nat := 118140960795 + 90351 * 2 ^ 59
def prefixEnd_90351 : Nat := 4983230072969 + 3 ^ 40 * 90351 * 2
def baseEnd_90351 : Nat := 10309664580995829999331

theorem tailTrace_90351 : CollatzResearch.WordTrace tailWord_90351 prefixEnd_90351 10309664580995829999331 := by
  unfold tailWord_90351
  simp only [CollatzResearch.WordTrace]
  refine ⟨3295371695681232567406907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2196914463787488378271271 3295371695681232567406907)
  ·
    refine ⟨4943057543521848851110361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3295371695681232567406907 4943057543521848851110361)
    ·
      refine ⟨3707293157641386638332771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4943057543521848851110361 3707293157641386638332771)
      ·
        refine ⟨5560939736462079957499157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3707293157641386638332771 5560939736462079957499157)
        ·
          refine ⟨260669050146659998007773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5560939736462079957499157 260669050146659998007773)
          ·
            refine ⟨97750893804997499252915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260669050146659998007773 97750893804997499252915)
            ·
              refine ⟨146626340707496248879373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97750893804997499252915 146626340707496248879373)
              ·
                refine ⟨54984877765311093329765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146626340707496248879373 54984877765311093329765)
                ·
                  refine ⟨10309664580995829999331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54984877765311093329765 10309664580995829999331)
                  ·
                    rfl

theorem cell22_90351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 4].length) (baseStart_90351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90351 prefixEnd_90351 := by exact prefixLift 90351
  have htrace : WordTrace (prefixWord ++ tailWord_90351) baseStart_90351 baseEnd_90351 := by
    simpa [prefixWord, tailWord_90351, baseEnd_90351] using wordTrace_append hprefix tailTrace_90351
  have hstable : (prefixWord ++ tailWord_90351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90351).length < 2 ^ (prefixWord ++ tailWord_90351).sum := by decide
  have hdescent : baseEnd_90351 < baseStart_90351 := by decide
  rcases family_descends (prefixWord ++ tailWord_90351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90362 : List Nat := [3, 1, 1, 1, 1, 7, 8]
def baseStart_90362 : Nat := 118140960795 + 90362 * 2 ^ 59
def prefixEnd_90362 : Nat := 4983230072969 + 3 ^ 40 * 90362 * 2
def baseEnd_90362 : Nat := 1145657750658782517517

theorem tailTrace_90362 : CollatzResearch.WordTrace tailWord_90362 prefixEnd_90362 1145657750658782517517 := by
  unfold tailWord_90362
  simp only [CollatzResearch.WordTrace]
  refine ⟨823943224660345361514335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2197181932427587630704893 823943224660345361514335)
  ·
    refine ⟨1235914836990518042271503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 823943224660345361514335 1235914836990518042271503)
    ·
      refine ⟨1853872255485777063407255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1235914836990518042271503 1853872255485777063407255)
      ·
        refine ⟨2780808383228665595110883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1853872255485777063407255 2780808383228665595110883)
        ·
          refine ⟨4171212574842998392666325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2780808383228665595110883 4171212574842998392666325)
          ·
            refine ⟨97762794722882774828117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 4171212574842998392666325 97762794722882774828117)
            ·
              refine ⟨1145657750658782517517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 97762794722882774828117 1145657750658782517517)
              ·
                rfl

theorem cell22_90362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 8].length) (baseStart_90362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90362 prefixEnd_90362 := by exact prefixLift 90362
  have htrace : WordTrace (prefixWord ++ tailWord_90362) baseStart_90362 baseEnd_90362 := by
    simpa [prefixWord, tailWord_90362, baseEnd_90362] using wordTrace_append hprefix tailTrace_90362
  have hstable : (prefixWord ++ tailWord_90362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90362).length < 2 ^ (prefixWord ++ tailWord_90362).sum := by decide
  have hdescent : baseEnd_90362 < baseStart_90362 := by decide
  rcases family_descends (prefixWord ++ tailWord_90362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90364 : List Nat := [2, 2, 2, 1, 4, 2, 1, 2, 2, 4]
def baseStart_90364 : Nat := 118140960795 + 90364 * 2 ^ 59
def prefixEnd_90364 : Nat := 4983230072969 + 3 ^ 40 * 90364 * 2
def baseEnd_90364 : Nat := 30933443908659789422953

theorem tailTrace_90364 : CollatzResearch.WordTrace tailWord_90364 prefixEnd_90364 30933443908659789422953 := by
  unfold tailWord_90364
  simp only [CollatzResearch.WordTrace]
  refine ⟨1647922922317067893815073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2197230563089423858420097 1647922922317067893815073)
  ·
    refine ⟨1235942191737800920361305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1647922922317067893815073 1235942191737800920361305)
    ·
      refine ⟨926956643803350690270979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1235942191737800920361305 926956643803350690270979)
      ·
        refine ⟨1390434965705026035406469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 926956643803350690270979 1390434965705026035406469)
        ·
          refine ⟨260706556069692381638713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1390434965705026035406469 260706556069692381638713)
          ·
            refine ⟨195529917052269286229035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260706556069692381638713 195529917052269286229035)
            ·
              refine ⟨293294875578403929343553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195529917052269286229035 293294875578403929343553)
              ·
                refine ⟨219971156683802947007665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 293294875578403929343553 219971156683802947007665)
                ·
                  refine ⟨164978367512852210255749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219971156683802947007665 164978367512852210255749)
                  ·
                    refine ⟨30933443908659789422953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 164978367512852210255749 30933443908659789422953)
                    ·
                      rfl

theorem cell22_90364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_90364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90364 prefixEnd_90364 := by exact prefixLift 90364
  have htrace : WordTrace (prefixWord ++ tailWord_90364) baseStart_90364 baseEnd_90364 := by
    simpa [prefixWord, tailWord_90364, baseEnd_90364] using wordTrace_append hprefix tailTrace_90364
  have hstable : (prefixWord ++ tailWord_90364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90364).length < 2 ^ (prefixWord ++ tailWord_90364).sum := by decide
  have hdescent : baseEnd_90364 < baseStart_90364 := by decide
  rcases family_descends (prefixWord ++ tailWord_90364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90366 : List Nat := [4, 2, 2, 1, 1, 1, 2, 4, 2, 3]
def baseStart_90366 : Nat := 118140960795 + 90366 * 2 ^ 59
def prefixEnd_90366 : Nat := 4983230072969 + 3 ^ 40 * 90366 * 2
def baseEnd_90366 : Nat := 30934128549532450872947

theorem tailTrace_90366 : CollatzResearch.WordTrace tailWord_90366 prefixEnd_90366 30934128549532450872947 := by
  unfold tailWord_90366
  simp only [CollatzResearch.WordTrace]
  refine ⟨411989848828361266150369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2197279193751260086135301 411989848828361266150369)
  ·
    refine ⟨308992386621270949612777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 411989848828361266150369 308992386621270949612777)
    ·
      refine ⟨231744289965953212209583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308992386621270949612777 231744289965953212209583)
      ·
        refine ⟨347616434948929818314375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231744289965953212209583 347616434948929818314375)
        ·
          refine ⟨521424652423394727471563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347616434948929818314375 521424652423394727471563)
          ·
            refine ⟨782136978635092091207345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521424652423394727471563 782136978635092091207345)
            ·
              refine ⟨586602733976319068405509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 782136978635092091207345 586602733976319068405509)
              ·
                refine ⟨109988012620559825326033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 586602733976319068405509 109988012620559825326033)
                ·
                  refine ⟨82491009465419868994525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109988012620559825326033 82491009465419868994525)
                  ·
                    refine ⟨30934128549532450872947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82491009465419868994525 30934128549532450872947)
                    ·
                      rfl

theorem cell22_90366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_90366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90366 prefixEnd_90366 := by exact prefixLift 90366
  have htrace : WordTrace (prefixWord ++ tailWord_90366) baseStart_90366 baseEnd_90366 := by
    simpa [prefixWord, tailWord_90366, baseEnd_90366] using wordTrace_append hprefix tailTrace_90366
  have hstable : (prefixWord ++ tailWord_90366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90366).length < 2 ^ (prefixWord ++ tailWord_90366).sum := by decide
  have hdescent : baseEnd_90366 < baseStart_90366 := by decide
  rcases family_descends (prefixWord ++ tailWord_90366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90398 : List Nat := [4, 3, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_90398 : Nat := 118140960795 + 90398 * 2 ^ 59
def prefixEnd_90398 : Nat := 4983230072969 + 3 ^ 40 * 90398 * 2
def baseEnd_90398 : Nat := 30945082803495034072849

theorem tailTrace_90398 : CollatzResearch.WordTrace tailWord_90398 prefixEnd_90398 30945082803495034072849 := by
  unfold tailWord_90398
  simp only [CollatzResearch.WordTrace]
  refine ⟨412135740813869949295981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2198057284340639729578565 412135740813869949295981)
  ·
    refine ⟨154550902805201230985993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 412135740813869949295981 154550902805201230985993)
    ·
      refine ⟨115913177103900923239495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154550902805201230985993 115913177103900923239495)
      ·
        refine ⟨173869765655851384859243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115913177103900923239495 173869765655851384859243)
        ·
          refine ⟨260804648483777077288865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173869765655851384859243 260804648483777077288865)
          ·
            refine ⟨195603486362832807966649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260804648483777077288865 195603486362832807966649)
            ·
              refine ⟨146702614772124605974987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195603486362832807966649 146702614772124605974987)
              ·
                refine ⟨220053922158186908962481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146702614772124605974987 220053922158186908962481)
                ·
                  refine ⟨165040441618640181721861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220053922158186908962481 165040441618640181721861)
                  ·
                    refine ⟨30945082803495034072849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 165040441618640181721861 30945082803495034072849)
                    ·
                      rfl

theorem cell22_90398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_90398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90398 prefixEnd_90398 := by exact prefixLift 90398
  have htrace : WordTrace (prefixWord ++ tailWord_90398) baseStart_90398 baseEnd_90398 := by
    simpa [prefixWord, tailWord_90398, baseEnd_90398] using wordTrace_append hprefix tailTrace_90398
  have hstable : (prefixWord ++ tailWord_90398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90398).length < 2 ^ (prefixWord ++ tailWord_90398).sum := by decide
  have hdescent : baseEnd_90398 < baseStart_90398 := by decide
  rcases family_descends (prefixWord ++ tailWord_90398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90471 : List Nat := [1, 1, 5, 1, 3, 2, 1, 3, 1, 4]
def baseStart_90471 : Nat := 118140960795 + 90471 * 2 ^ 59
def prefixEnd_90471 : Nat := 4983230072969 + 3 ^ 40 * 90471 * 2
def baseEnd_90471 : Nat := 30970072195347176997625

theorem tailTrace_90471 : CollatzResearch.WordTrace tailWord_90471 prefixEnd_90471 30970072195347176997625 := by
  unfold tailWord_90471
  simp only [CollatzResearch.WordTrace]
  refine ⟨3299748455246493061775267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2199832303497662041183511 3299748455246493061775267)
  ·
    refine ⟨4949622682869739592662901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3299748455246493061775267 4949622682869739592662901)
    ·
      refine ⟨464027126519038086812147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4949622682869739592662901 464027126519038086812147)
      ·
        refine ⟨696040689778557130218221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464027126519038086812147 696040689778557130218221)
        ·
          refine ⟨261015258666958923831833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 696040689778557130218221 261015258666958923831833)
          ·
            refine ⟨195761444000219192873875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261015258666958923831833 195761444000219192873875)
            ·
              refine ⟨293642166000328789310813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195761444000219192873875 293642166000328789310813)
              ·
                refine ⟨110115812250123295991555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293642166000328789310813 110115812250123295991555)
                ·
                  refine ⟨165173718375184943987333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110115812250123295991555 165173718375184943987333)
                  ·
                    refine ⟨30970072195347176997625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 165173718375184943987333 30970072195347176997625)
                    ·
                      rfl

theorem cell22_90471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_90471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90471 prefixEnd_90471 := by exact prefixLift 90471
  have htrace : WordTrace (prefixWord ++ tailWord_90471) baseStart_90471 baseEnd_90471 := by
    simpa [prefixWord, tailWord_90471, baseEnd_90471] using wordTrace_append hprefix tailTrace_90471
  have hstable : (prefixWord ++ tailWord_90471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90471).length < 2 ^ (prefixWord ++ tailWord_90471).sum := by decide
  have hdescent : baseEnd_90471 < baseStart_90471 := by decide
  rcases family_descends (prefixWord ++ tailWord_90471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90574 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 4, 5]
def baseStart_90574 : Nat := 118140960795 + 90574 * 2 ^ 59
def prefixEnd_90574 : Nat := 4983230072969 + 3 ^ 40 * 90574 * 2
def baseEnd_90574 : Nat := 31005331200289241672309

theorem tailTrace_90574 : CollatzResearch.WordTrace tailWord_90574 prefixEnd_90574 31005331200289241672309 := by
  unfold tailWord_90574
  simp only [CollatzResearch.WordTrace]
  refine ⟨412938146734167706596847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2202336782582227768516517 412938146734167706596847)
  ·
    refine ⟨619407220101251559895271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 412938146734167706596847 619407220101251559895271)
    ·
      refine ⟨929110830151877339842907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 619407220101251559895271 929110830151877339842907)
      ·
        refine ⟨1393666245227816009764361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 929110830151877339842907 1393666245227816009764361)
        ·
          refine ⟨1045249683920862007323271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1393666245227816009764361 1045249683920862007323271)
          ·
            refine ⟨1567874525881293010984907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045249683920862007323271 1567874525881293010984907)
            ·
              refine ⟨2351811788821939516477361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1567874525881293010984907 2351811788821939516477361)
              ·
                refine ⟨1763858841616454637358021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2351811788821939516477361 1763858841616454637358021)
                ·
                  refine ⟨330723532803085244504629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1763858841616454637358021 330723532803085244504629)
                  ·
                    refine ⟨31005331200289241672309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 330723532803085244504629 31005331200289241672309)
                    ·
                      rfl

theorem cell22_90574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_90574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90574 prefixEnd_90574 := by exact prefixLift 90574
  have htrace : WordTrace (prefixWord ++ tailWord_90574) baseStart_90574 baseEnd_90574 := by
    simpa [prefixWord, tailWord_90574, baseEnd_90574] using wordTrace_append hprefix tailTrace_90574
  have hstable : (prefixWord ++ tailWord_90574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90574).length < 2 ^ (prefixWord ++ tailWord_90574).sum := by decide
  have hdescent : baseEnd_90574 < baseStart_90574 := by decide
  rcases family_descends (prefixWord ++ tailWord_90574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90604 : List Nat := [2, 2, 1, 1, 2, 1, 4, 3, 6]
def baseStart_90604 : Nat := 118140960795 + 90604 * 2 ^ 59
def prefixEnd_90604 : Nat := 4983230072969 + 3 ^ 40 * 90604 * 2
def baseEnd_90604 : Nat := 10338533604459721140739

theorem tailTrace_90604 : CollatzResearch.WordTrace tailWord_90604 prefixEnd_90604 10338533604459721140739 := by
  unfold tailWord_90604
  simp only [CollatzResearch.WordTrace]
  refine ⟨1652299681882328388183433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2203066242509771184244577 1652299681882328388183433)
  ·
    refine ⟨1239224761411746291137575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1652299681882328388183433 1239224761411746291137575)
    ·
      refine ⟨1858837142117619436706363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1239224761411746291137575 1858837142117619436706363)
      ·
        refine ⟨2788255713176429155059545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1858837142117619436706363 2788255713176429155059545)
        ·
          refine ⟨2091191784882321866294659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2788255713176429155059545 2091191784882321866294659)
          ·
            refine ⟨3136787677323482799441989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2091191784882321866294659 3136787677323482799441989)
            ·
              refine ⟨588147689498153024895373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3136787677323482799441989 588147689498153024895373)
              ·
                refine ⟨220555383561807384335765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 588147689498153024895373 220555383561807384335765)
                ·
                  refine ⟨10338533604459721140739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 220555383561807384335765 10338533604459721140739)
                  ·
                    rfl

theorem cell22_90604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_90604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90604 prefixEnd_90604 := by exact prefixLift 90604
  have htrace : WordTrace (prefixWord ++ tailWord_90604) baseStart_90604 baseEnd_90604 := by
    simpa [prefixWord, tailWord_90604, baseEnd_90604] using wordTrace_append hprefix tailTrace_90604
  have hstable : (prefixWord ++ tailWord_90604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90604).length < 2 ^ (prefixWord ++ tailWord_90604).sum := by decide
  have hdescent : baseEnd_90604 < baseStart_90604 := by decide
  rcases family_descends (prefixWord ++ tailWord_90604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90606 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 3, 4]
def baseStart_90606 : Nat := 118140960795 + 90606 * 2 ^ 59
def prefixEnd_90606 : Nat := 4983230072969 + 3 ^ 40 * 90606 * 2
def baseEnd_90606 : Nat := 31016285454251824872211

theorem tailTrace_90606 : CollatzResearch.WordTrace tailWord_90606 prefixEnd_90606 31016285454251824872211 := by
  unfold tailWord_90606
  simp only [CollatzResearch.WordTrace]
  refine ⟨413084038719676389742459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2203114873171607411959781 413084038719676389742459)
  ·
    refine ⟨619626058079514584613689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 413084038719676389742459 619626058079514584613689)
    ·
      refine ⟨464719543559635938460267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 619626058079514584613689 464719543559635938460267)
      ·
        refine ⟨697079315339453907690401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464719543559635938460267 697079315339453907690401)
        ·
          refine ⟨522809486504590430767801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 697079315339453907690401 522809486504590430767801)
          ·
            refine ⟨392107114878442823075851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 522809486504590430767801 392107114878442823075851)
            ·
              refine ⟨588160672317664234613777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392107114878442823075851 588160672317664234613777)
              ·
                refine ⟨441120504238248175960333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588160672317664234613777 441120504238248175960333)
                ·
                  refine ⟨165420189089343065985125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 441120504238248175960333 165420189089343065985125)
                  ·
                    refine ⟨31016285454251824872211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 165420189089343065985125 31016285454251824872211)
                    ·
                      rfl

theorem cell22_90606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_90606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90606 prefixEnd_90606 := by exact prefixLift 90606
  have htrace : WordTrace (prefixWord ++ tailWord_90606) baseStart_90606 baseEnd_90606 := by
    simpa [prefixWord, tailWord_90606, baseEnd_90606] using wordTrace_append hprefix tailTrace_90606
  have hstable : (prefixWord ++ tailWord_90606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90606).length < 2 ^ (prefixWord ++ tailWord_90606).sum := by decide
  have hdescent : baseEnd_90606 < baseStart_90606 := by decide
  rcases family_descends (prefixWord ++ tailWord_90606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90636 : List Nat := [2, 2, 1, 2, 4, 1, 2, 2, 1, 5]
def baseStart_90636 : Nat := 118140960795 + 90636 * 2 ^ 59
def prefixEnd_90636 : Nat := 4983230072969 + 3 ^ 40 * 90636 * 2
def baseEnd_90636 : Nat := 31026555067341746622119

theorem tailTrace_90636 : CollatzResearch.WordTrace tailWord_90636 prefixEnd_90636 31026555067341746622119 := by
  unfold tailWord_90636
  simp only [CollatzResearch.WordTrace]
  refine ⟨1652883249824363120765881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2203844333099150827687841 1652883249824363120765881)
  ·
    refine ⟨1239662437368272340574411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1652883249824363120765881 1239662437368272340574411)
    ·
      refine ⟨1859493656052408510861617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1239662437368272340574411 1859493656052408510861617)
      ·
        refine ⟨1394620242039306383146213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1859493656052408510861617 1394620242039306383146213)
        ·
          refine ⟨261491295382369946839915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1394620242039306383146213 261491295382369946839915)
          ·
            refine ⟨392236943073554920259873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261491295382369946839915 392236943073554920259873)
            ·
              refine ⟨294177707305166190194905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 392236943073554920259873 294177707305166190194905)
              ·
                refine ⟨220633280478874642646179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294177707305166190194905 220633280478874642646179)
                ·
                  refine ⟨330949920718311963969269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220633280478874642646179 330949920718311963969269)
                  ·
                    refine ⟨31026555067341746622119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 330949920718311963969269 31026555067341746622119)
                    ·
                      rfl

theorem cell22_90636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_90636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90636 prefixEnd_90636 := by exact prefixLift 90636
  have htrace : WordTrace (prefixWord ++ tailWord_90636) baseStart_90636 baseEnd_90636 := by
    simpa [prefixWord, tailWord_90636, baseEnd_90636] using wordTrace_append hprefix tailTrace_90636
  have hstable : (prefixWord ++ tailWord_90636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90636).length < 2 ^ (prefixWord ++ tailWord_90636).sum := by decide
  have hdescent : baseEnd_90636 < baseStart_90636 := by decide
  rcases family_descends (prefixWord ++ tailWord_90636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90638 : List Nat := [4, 1, 1, 2, 3, 1, 1, 5, 4]
def baseStart_90638 : Nat := 118140960795 + 90638 * 2 ^ 59
def prefixEnd_90638 : Nat := 4983230072969 + 3 ^ 40 * 90638 * 2
def baseEnd_90638 : Nat := 10342413236071469357371

theorem tailTrace_90638 : CollatzResearch.WordTrace tailWord_90638 prefixEnd_90638 10342413236071469357371 := by
  unfold tailWord_90638
  simp only [CollatzResearch.WordTrace]
  refine ⟨413229930705185072888071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2203892963760987055403045 413229930705185072888071)
  ·
    refine ⟨619844896057777609332107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 413229930705185072888071 619844896057777609332107)
    ·
      refine ⟨929767344086666413998161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 619844896057777609332107 929767344086666413998161)
      ·
        refine ⟨697325508064999810498621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 929767344086666413998161 697325508064999810498621)
        ·
          refine ⟨261497065524374928936983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 697325508064999810498621 261497065524374928936983)
          ·
            refine ⟨392245598286562393405475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261497065524374928936983 392245598286562393405475)
            ·
              refine ⟨588368397429843590108213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392245598286562393405475 588368397429843590108213)
              ·
                refine ⟨55159537259047836572645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 588368397429843590108213 55159537259047836572645)
                ·
                  refine ⟨10342413236071469357371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55159537259047836572645 10342413236071469357371)
                  ·
                    rfl

theorem cell22_90638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_90638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90638 prefixEnd_90638 := by exact prefixLift 90638
  have htrace : WordTrace (prefixWord ++ tailWord_90638) baseStart_90638 baseEnd_90638 := by
    simpa [prefixWord, tailWord_90638, baseEnd_90638] using wordTrace_append hprefix tailTrace_90638
  have hstable : (prefixWord ++ tailWord_90638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90638).length < 2 ^ (prefixWord ++ tailWord_90638).sum := by decide
  have hdescent : baseEnd_90638 < baseStart_90638 := by decide
  rcases family_descends (prefixWord ++ tailWord_90638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90653 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 4, 3]
def baseStart_90653 : Nat := 118140960795 + 90653 * 2 ^ 59
def prefixEnd_90653 : Nat := 4983230072969 + 3 ^ 40 * 90653 * 2
def baseEnd_90653 : Nat := 31032374514759368947067

theorem tailTrace_90653 : CollatzResearch.WordTrace tailWord_90653 prefixEnd_90653 31032374514759368947067 := by
  unfold tailWord_90653
  simp only [CollatzResearch.WordTrace]
  refine ⟨3306386540587138144900613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2204257693724758763267075 3306386540587138144900613)
  ·
    refine ⟨619947476360088402168865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3306386540587138144900613 619947476360088402168865)
    ·
      refine ⟨464960607270066301626649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 619947476360088402168865 464960607270066301626649)
      ·
        refine ⟨348720455452549726219987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 464960607270066301626649 348720455452549726219987)
        ·
          refine ⟨523080683178824589329981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348720455452549726219987 523080683178824589329981)
          ·
            refine ⟨196155256192059220998743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 523080683178824589329981 196155256192059220998743)
            ·
              refine ⟨294232884288088831498115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196155256192059220998743 294232884288088831498115)
              ·
                refine ⟨441349326432133247247173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294232884288088831498115 441349326432133247247173)
                ·
                  refine ⟨82752998706024983858845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 441349326432133247247173 82752998706024983858845)
                  ·
                    refine ⟨31032374514759368947067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82752998706024983858845 31032374514759368947067)
                    ·
                      rfl

theorem cell22_90653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_90653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90653 prefixEnd_90653 := by exact prefixLift 90653
  have htrace : WordTrace (prefixWord ++ tailWord_90653) baseStart_90653 baseEnd_90653 := by
    simpa [prefixWord, tailWord_90653, baseEnd_90653] using wordTrace_append hprefix tailTrace_90653
  have hstable : (prefixWord ++ tailWord_90653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90653).length < 2 ^ (prefixWord ++ tailWord_90653).sum := by decide
  have hdescent : baseEnd_90653 < baseStart_90653 := by decide
  rcases family_descends (prefixWord ++ tailWord_90653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90670 : List Nat := [4, 1, 3, 1, 3, 2, 1, 1, 1, 5]
def baseStart_90670 : Nat := 118140960795 + 90670 * 2 ^ 59
def prefixEnd_90670 : Nat := 4983230072969 + 3 ^ 40 * 90670 * 2
def baseEnd_90670 : Nat := 31038193962176991272015

theorem tailTrace_90670 : CollatzResearch.WordTrace tailWord_90670 prefixEnd_90670 31038193962176991272015 := by
  unfold tailWord_90670
  simp only [CollatzResearch.WordTrace]
  refine ⟨413375822690693756033683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2204671054350366698846309 413375822690693756033683)
  ·
    refine ⟨620063734036040634050525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 413375822690693756033683 620063734036040634050525)
    ·
      refine ⟨232523900263515237768947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 620063734036040634050525 232523900263515237768947)
      ·
        refine ⟨348785850395272856653421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232523900263515237768947 348785850395272856653421)
        ·
          refine ⟨130794693898227321245033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 348785850395272856653421 130794693898227321245033)
          ·
            refine ⟨98096020423670490933775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130794693898227321245033 98096020423670490933775)
            ·
              refine ⟨147144030635505736400663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98096020423670490933775 147144030635505736400663)
              ·
                refine ⟨220716045953258604600995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147144030635505736400663 220716045953258604600995)
                ·
                  refine ⟨331074068929887906901493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220716045953258604600995 331074068929887906901493)
                  ·
                    refine ⟨31038193962176991272015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 331074068929887906901493 31038193962176991272015)
                    ·
                      rfl

theorem cell22_90670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_90670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90670 prefixEnd_90670 := by exact prefixLift 90670
  have htrace : WordTrace (prefixWord ++ tailWord_90670) baseStart_90670 baseEnd_90670 := by
    simpa [prefixWord, tailWord_90670, baseEnd_90670] using wordTrace_append hprefix tailTrace_90670
  have hstable : (prefixWord ++ tailWord_90670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90670).length < 2 ^ (prefixWord ++ tailWord_90670).sum := by decide
  have hdescent : baseEnd_90670 < baseStart_90670 := by decide
  rcases family_descends (prefixWord ++ tailWord_90670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90711 : List Nat := [1, 1, 3, 2, 2, 2, 2, 4, 5]
def baseStart_90711 : Nat := 118140960795 + 90711 * 2 ^ 59
def prefixEnd_90711 : Nat := 4983230072969 + 3 ^ 40 * 90711 * 2
def baseEnd_90711 : Nat := 10350743033355516998963

theorem tailTrace_90711 : CollatzResearch.WordTrace tailWord_90711 prefixEnd_90711 10350743033355516998963 := by
  unfold tailWord_90711
  simp only [CollatzResearch.WordTrace]
  refine ⟨3308501974377014050511987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2205667982918009367007991 3308501974377014050511987)
  ·
    refine ⟨4962752961565521075767981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3308501974377014050511987 4962752961565521075767981)
    ·
      refine ⟨1861032360587070403412993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4962752961565521075767981 1861032360587070403412993)
      ·
        refine ⟨1395774270440302802559745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1861032360587070403412993 1395774270440302802559745)
        ·
          refine ⟨1046830702830227101919809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1395774270440302802559745 1046830702830227101919809)
          ·
            refine ⟨785123027122670326439857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1046830702830227101919809 785123027122670326439857)
            ·
              refine ⟨588842270342002744829893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 785123027122670326439857 588842270342002744829893)
              ·
                refine ⟨110407925689125514655605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 588842270342002744829893 110407925689125514655605)
                ·
                  refine ⟨10350743033355516998963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110407925689125514655605 10350743033355516998963)
                  ·
                    rfl

theorem cell22_90711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 5].length) (baseStart_90711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90711 prefixEnd_90711 := by exact prefixLift 90711
  have htrace : WordTrace (prefixWord ++ tailWord_90711) baseStart_90711 baseEnd_90711 := by
    simpa [prefixWord, tailWord_90711, baseEnd_90711] using wordTrace_append hprefix tailTrace_90711
  have hstable : (prefixWord ++ tailWord_90711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90711).length < 2 ^ (prefixWord ++ tailWord_90711).sum := by decide
  have hdescent : baseEnd_90711 < baseStart_90711 := by decide
  rcases family_descends (prefixWord ++ tailWord_90711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90788 : List Nat := [2, 3, 1, 2, 2, 1, 4, 1, 1, 5]
def baseStart_90788 : Nat := 118140960795 + 90788 * 2 ^ 59
def prefixEnd_90788 : Nat := 4983230072969 + 3 ^ 40 * 90788 * 2
def baseEnd_90788 : Nat := 31078587773664016821653

theorem tailTrace_90788 : CollatzResearch.WordTrace tailWord_90788 prefixEnd_90788 31078587773664016821653 := by
  unfold tailWord_90788
  simp only [CollatzResearch.WordTrace]
  refine ⟨1655655197549028100532509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2207540263398704134043345 1655655197549028100532509)
  ·
    refine ⟨620870699080885537699691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1655655197549028100532509 620870699080885537699691)
    ·
      refine ⟨931306048621328306549537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 620870699080885537699691 931306048621328306549537)
      ·
        refine ⟨698479536465996229912153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 931306048621328306549537 698479536465996229912153)
        ·
          refine ⟨523859652349497172434115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 698479536465996229912153 523859652349497172434115)
          ·
            refine ⟨785789478524245758651173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523859652349497172434115 785789478524245758651173)
            ·
              refine ⟨147335527223296079747095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 785789478524245758651173 147335527223296079747095)
              ·
                refine ⟨221003290834944119620643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147335527223296079747095 221003290834944119620643)
                ·
                  refine ⟨331504936252416179430965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221003290834944119620643 331504936252416179430965)
                  ·
                    refine ⟨31078587773664016821653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 331504936252416179430965 31078587773664016821653)
                    ·
                      rfl

theorem cell22_90788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_90788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90788 prefixEnd_90788 := by exact prefixLift 90788
  have htrace : WordTrace (prefixWord ++ tailWord_90788) baseStart_90788 baseEnd_90788 := by
    simpa [prefixWord, tailWord_90788, baseEnd_90788] using wordTrace_append hprefix tailTrace_90788
  have hstable : (prefixWord ++ tailWord_90788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90788).length < 2 ^ (prefixWord ++ tailWord_90788).sum := by decide
  have hdescent : baseEnd_90788 < baseStart_90788 := by decide
  rcases family_descends (prefixWord ++ tailWord_90788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90803 : List Nat := [1, 1, 1, 2, 3, 4, 3, 1, 2, 4]
def baseStart_90803 : Nat := 118140960795 + 90803 * 2 ^ 59
def prefixEnd_90803 : Nat := 4983230072969 + 3 ^ 40 * 90803 * 2
def baseEnd_90803 : Nat := 31083722580208977696607

theorem tailTrace_90803 : CollatzResearch.WordTrace tailWord_90803 prefixEnd_90803 31083722580208977696607 := by
  unfold tailWord_90803
  simp only [CollatzResearch.WordTrace]
  refine ⟨3311857490043713762861063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2207904993362475841907375 3311857490043713762861063)
  ·
    refine ⟨4967786235065570644291595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3311857490043713762861063 4967786235065570644291595)
    ·
      refine ⟨7451679352598355966437393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4967786235065570644291595 7451679352598355966437393)
      ·
        refine ⟨5588759514448766974828045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7451679352598355966437393 5588759514448766974828045)
        ·
          refine ⟨2095784817918287615560517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5588759514448766974828045 2095784817918287615560517)
          ·
            refine ⟨392959653359678927917597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2095784817918287615560517 392959653359678927917597)
            ·
              refine ⟨147359870009879597969099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 392959653359678927917597 147359870009879597969099)
              ·
                refine ⟨221039805014819396953649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147359870009879597969099 221039805014819396953649)
                ·
                  refine ⟨165779853761114547715237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221039805014819396953649 165779853761114547715237)
                  ·
                    refine ⟨31083722580208977696607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 165779853761114547715237 31083722580208977696607)
                    ·
                      rfl

theorem cell22_90803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 4].length) (baseStart_90803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90803 prefixEnd_90803 := by exact prefixLift 90803
  have htrace : WordTrace (prefixWord ++ tailWord_90803) baseStart_90803 baseEnd_90803 := by
    simpa [prefixWord, tailWord_90803, baseEnd_90803] using wordTrace_append hprefix tailTrace_90803
  have hstable : (prefixWord ++ tailWord_90803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90803).length < 2 ^ (prefixWord ++ tailWord_90803).sum := by decide
  have hdescent : baseEnd_90803 < baseStart_90803 := by decide
  rcases family_descends (prefixWord ++ tailWord_90803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90869 : List Nat := [1, 3, 6, 1, 2, 1, 8]
def baseStart_90869 : Nat := 118140960795 + 90869 * 2 ^ 59
def prefixEnd_90869 : Nat := 4983230072969 + 3 ^ 40 * 90869 * 2
def baseEnd_90869 : Nat := 1152085767740992798015

theorem tailTrace_90869 : CollatzResearch.WordTrace tailWord_90869 prefixEnd_90869 1152085767740992798015 := by
  unfold tailWord_90869
  simp only [CollatzResearch.WordTrace]
  refine ⟨3314264707804607034763661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2209509805203071356509107 3314264707804607034763661)
  ·
    refine ⟨1242849265426727638036373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3314264707804607034763661 1242849265426727638036373)
    ·
      refine ⟨58258559316877858032955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1242849265426727638036373 58258559316877858032955)
      ·
        refine ⟨87387838975316787049433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58258559316877858032955 87387838975316787049433)
        ·
          refine ⟨65540879231487590287075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87387838975316787049433 65540879231487590287075)
          ·
            refine ⟨98311318847231385430613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65540879231487590287075 98311318847231385430613)
            ·
              refine ⟨1152085767740992798015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 98311318847231385430613 1152085767740992798015)
              ·
                rfl

theorem cell22_90869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 8].length) (baseStart_90869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90869 prefixEnd_90869 := by exact prefixLift 90869
  have htrace : WordTrace (prefixWord ++ tailWord_90869) baseStart_90869 baseEnd_90869 := by
    simpa [prefixWord, tailWord_90869, baseEnd_90869] using wordTrace_append hprefix tailTrace_90869
  have hstable : (prefixWord ++ tailWord_90869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90869).length < 2 ^ (prefixWord ++ tailWord_90869).sum := by decide
  have hdescent : baseEnd_90869 < baseStart_90869 := by decide
  rcases family_descends (prefixWord ++ tailWord_90869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90884 : List Nat := [2, 3, 2, 2, 1, 1, 5, 2, 1, 3]
def baseStart_90884 : Nat := 118140960795 + 90884 * 2 ^ 59
def prefixEnd_90884 : Nat := 4983230072969 + 3 ^ 40 * 90884 * 2
def baseEnd_90884 : Nat := 31111450535551766421359

theorem tailTrace_90884 : CollatzResearch.WordTrace tailWord_90884 prefixEnd_90884 31111450535551766421359 := by
  unfold tailWord_90884
  simp only [CollatzResearch.WordTrace]
  refine ⟨1657405901375132298279853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2209874535166843064373137 1657405901375132298279853)
  ·
    refine ⟨621527213015674611854945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1657405901375132298279853 621527213015674611854945)
    ·
      refine ⟨466145409761755958891209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 621527213015674611854945 466145409761755958891209)
      ·
        refine ⟨349609057321316969168407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466145409761755958891209 349609057321316969168407)
        ·
          refine ⟨524413585981975453752611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349609057321316969168407 524413585981975453752611)
          ·
            refine ⟨786620378972963180628917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524413585981975453752611 786620378972963180628917)
            ·
              refine ⟨73745660528715298183961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 786620378972963180628917 73745660528715298183961)
              ·
                refine ⟨55309245396536473637971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73745660528715298183961 55309245396536473637971)
                ·
                  refine ⟨82963868094804710456957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55309245396536473637971 82963868094804710456957)
                  ·
                    refine ⟨31111450535551766421359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82963868094804710456957 31111450535551766421359)
                    ·
                      rfl

theorem cell22_90884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_90884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90884 prefixEnd_90884 := by exact prefixLift 90884
  have htrace : WordTrace (prefixWord ++ tailWord_90884) baseStart_90884 baseEnd_90884 := by
    simpa [prefixWord, tailWord_90884, baseEnd_90884] using wordTrace_append hprefix tailTrace_90884
  have hstable : (prefixWord ++ tailWord_90884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90884).length < 2 ^ (prefixWord ++ tailWord_90884).sum := by decide
  have hdescent : baseEnd_90884 < baseStart_90884 := by decide
  rcases family_descends (prefixWord ++ tailWord_90884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90953 : List Nat := [1, 2, 1, 1, 2, 5, 3, 7]
def baseStart_90953 : Nat := 118140960795 + 90953 * 2 ^ 59
def prefixEnd_90953 : Nat := 4983230072969 + 3 ^ 40 * 90953 * 2
def baseEnd_90953 : Nat := 3459452293962065160683

theorem tailTrace_90953 : CollatzResearch.WordTrace tailWord_90953 prefixEnd_90953 3459452293962065160683 := by
  unfold tailWord_90953
  simp only [CollatzResearch.WordTrace]
  refine ⟨3317328439500289380821513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2211552293000192920547675 3317328439500289380821513)
  ·
    refine ⟨2487996329625217035616135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3317328439500289380821513 2487996329625217035616135)
    ·
      refine ⟨3731994494437825553424203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2487996329625217035616135 3731994494437825553424203)
      ·
        refine ⟨5597991741656738330136305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3731994494437825553424203 5597991741656738330136305)
        ·
          refine ⟨4198493806242553747602229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5597991741656738330136305 4198493806242553747602229)
          ·
            refine ⟨393608794335239413837709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4198493806242553747602229 393608794335239413837709)
            ·
              refine ⟨147603297875714780189141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 393608794335239413837709 147603297875714780189141)
              ·
                refine ⟨3459452293962065160683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 147603297875714780189141 3459452293962065160683)
                ·
                  rfl

theorem cell22_90953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 7].length) (baseStart_90953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90953 prefixEnd_90953 := by exact prefixLift 90953
  have htrace : WordTrace (prefixWord ++ tailWord_90953) baseStart_90953 baseEnd_90953 := by
    simpa [prefixWord, tailWord_90953, baseEnd_90953] using wordTrace_append hprefix tailTrace_90953
  have hstable : (prefixWord ++ tailWord_90953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90953).length < 2 ^ (prefixWord ++ tailWord_90953).sum := by decide
  have hdescent : baseEnd_90953 < baseStart_90953 := by decide
  rcases family_descends (prefixWord ++ tailWord_90953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90970 : List Nat := [3, 1, 1, 2, 1, 5, 3, 6]
def baseStart_90970 : Nat := 118140960795 + 90970 * 2 ^ 59
def prefixEnd_90970 : Nat := 4983230072969 + 3 ^ 40 * 90970 * 2
def baseEnd_90970 : Nat := 3460098899230689863455

theorem tailTrace_90970 : CollatzResearch.WordTrace tailWord_90970 prefixEnd_90970 3460098899230689863455 := by
  unfold tailWord_90970
  simp only [CollatzResearch.WordTrace]
  refine ⟨829487120109675321047591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2211965653625800856126909 829487120109675321047591)
  ·
    refine ⟨1244230680164512981571387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 829487120109675321047591 1244230680164512981571387)
    ·
      refine ⟨1866346020246769472357081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1244230680164512981571387 1866346020246769472357081)
      ·
        refine ⟨1399759515185077104267811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1866346020246769472357081 1399759515185077104267811)
        ·
          refine ⟨2099639272777615656401717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1399759515185077104267811 2099639272777615656401717)
          ·
            refine ⟨196841181822901467787661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2099639272777615656401717 196841181822901467787661)
            ·
              refine ⟨73815443183588050420373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196841181822901467787661 73815443183588050420373)
              ·
                refine ⟨3460098899230689863455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73815443183588050420373 3460098899230689863455)
                ·
                  rfl

theorem cell22_90970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 6].length) (baseStart_90970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90970 prefixEnd_90970 := by exact prefixLift 90970
  have htrace : WordTrace (prefixWord ++ tailWord_90970) baseStart_90970 baseEnd_90970 := by
    simpa [prefixWord, tailWord_90970, baseEnd_90970] using wordTrace_append hprefix tailTrace_90970
  have hstable : (prefixWord ++ tailWord_90970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90970).length < 2 ^ (prefixWord ++ tailWord_90970).sum := by decide
  have hdescent : baseEnd_90970 < baseStart_90970 := by decide
  rcases family_descends (prefixWord ++ tailWord_90970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90972 : List Nat := [2, 2, 4, 2, 1, 1, 3, 1, 2, 4]
def baseStart_90972 : Nat := 118140960795 + 90972 * 2 ^ 59
def prefixEnd_90972 : Nat := 4983230072969 + 3 ^ 40 * 90972 * 2
def baseEnd_90972 : Nat := 31141574733948870221089

theorem tailTrace_90972 : CollatzResearch.WordTrace tailWord_90972 prefixEnd_90972 31141574733948870221089 := by
  unfold tailWord_90972
  simp only [CollatzResearch.WordTrace]
  refine ⟨1659010713215727812881585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2212014284287637083842113 1659010713215727812881585)
  ·
    refine ⟨1244258034911795859661189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1659010713215727812881585 1244258034911795859661189)
    ·
      refine ⟨233298381545961723686473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1244258034911795859661189 233298381545961723686473)
      ·
        refine ⟨174973786159471292764855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233298381545961723686473 174973786159471292764855)
        ·
          refine ⟨262460679239206939147283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174973786159471292764855 262460679239206939147283)
          ·
            refine ⟨393691018858810408720925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262460679239206939147283 393691018858810408720925)
            ·
              refine ⟨147634132072053903270347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 393691018858810408720925 147634132072053903270347)
              ·
                refine ⟨221451198108080854905521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147634132072053903270347 221451198108080854905521)
                ·
                  refine ⟨166088398581060641179141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221451198108080854905521 166088398581060641179141)
                  ·
                    refine ⟨31141574733948870221089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 166088398581060641179141 31141574733948870221089)
                    ·
                      rfl

theorem cell22_90972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_90972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_90972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_90972 prefixEnd_90972 := by exact prefixLift 90972
  have htrace : WordTrace (prefixWord ++ tailWord_90972) baseStart_90972 baseEnd_90972 := by
    simpa [prefixWord, tailWord_90972, baseEnd_90972] using wordTrace_append hprefix tailTrace_90972
  have hstable : (prefixWord ++ tailWord_90972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90972).length < 2 ^ (prefixWord ++ tailWord_90972).sum := by decide
  have hdescent : baseEnd_90972 < baseStart_90972 := by decide
  rcases family_descends (prefixWord ++ tailWord_90972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91043 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 8]
def baseStart_91043 : Nat := 118140960795 + 91043 * 2 ^ 59
def prefixEnd_91043 : Nat := 4983230072969 + 3 ^ 40 * 91043 * 2
def baseEnd_91043 : Nat := 10388626494976117231957

theorem tailTrace_91043 : CollatzResearch.WordTrace tailWord_91043 prefixEnd_91043 10388626494976117231957 := by
  unfold tailWord_91043
  simp only [CollatzResearch.WordTrace]
  refine ⟨3320611009174234751597783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2213740672782823167731855 3320611009174234751597783)
  ·
    refine ⟨4980916513761352127396675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3320611009174234751597783 4980916513761352127396675)
    ·
      refine ⟨7471374770642028191095013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4980916513761352127396675 7471374770642028191095013)
      ·
        refine ⟨1400882769495380285830315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7471374770642028191095013 1400882769495380285830315)
        ·
          refine ⟨2101324154243070428745473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1400882769495380285830315 2101324154243070428745473)
          ·
            refine ⟨1575993115682302821559105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2101324154243070428745473 1575993115682302821559105)
            ·
              refine ⟨1181994836761727116169329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1575993115682302821559105 1181994836761727116169329)
              ·
                refine ⟨886496127571295337126997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1181994836761727116169329 886496127571295337126997)
                ·
                  refine ⟨10388626494976117231957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 886496127571295337126997 10388626494976117231957)
                  ·
                    rfl

theorem cell22_91043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 8].length) (baseStart_91043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91043 prefixEnd_91043 := by exact prefixLift 91043
  have htrace : WordTrace (prefixWord ++ tailWord_91043) baseStart_91043 baseEnd_91043 := by
    simpa [prefixWord, tailWord_91043, baseEnd_91043] using wordTrace_append hprefix tailTrace_91043
  have hstable : (prefixWord ++ tailWord_91043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91043).length < 2 ^ (prefixWord ++ tailWord_91043).sum := by decide
  have hdescent : baseEnd_91043 < baseStart_91043 := by decide
  rcases family_descends (prefixWord ++ tailWord_91043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91053 : List Nat := [1, 5, 2, 3, 2, 1, 1, 1, 3, 3]
def baseStart_91053 : Nat := 118140960795 + 91053 * 2 ^ 59
def prefixEnd_91053 : Nat := 4983230072969 + 3 ^ 40 * 91053 * 2
def baseEnd_91053 : Nat := 31169302689291658945841

theorem tailTrace_91053 : CollatzResearch.WordTrace tailWord_91053 prefixEnd_91053 31169302689291658945841 := by
  unfold tailWord_91053
  simp only [CollatzResearch.WordTrace]
  refine ⟨3320975739138006459461813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2213983826092004306307875 3320975739138006459461813)
  ·
    refine ⟨311341475544188105574545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3320975739138006459461813 311341475544188105574545)
    ·
      refine ⟨233506106658141079180909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311341475544188105574545 233506106658141079180909)
      ·
        refine ⟨87564789996802904692841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233506106658141079180909 87564789996802904692841)
        ·
          refine ⟨65673592497602178519631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87564789996802904692841 65673592497602178519631)
          ·
            refine ⟨98510388746403267779447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65673592497602178519631 98510388746403267779447)
            ·
              refine ⟨147765583119604901669171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98510388746403267779447 147765583119604901669171)
              ·
                refine ⟨221648374679407352503757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147765583119604901669171 221648374679407352503757)
                ·
                  refine ⟨83118140504777757188909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221648374679407352503757 83118140504777757188909)
                  ·
                    refine ⟨31169302689291658945841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83118140504777757188909 31169302689291658945841)
                    ·
                      rfl

theorem cell22_91053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_91053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91053 prefixEnd_91053 := by exact prefixLift 91053
  have htrace : WordTrace (prefixWord ++ tailWord_91053) baseStart_91053 baseEnd_91053 := by
    simpa [prefixWord, tailWord_91053, baseEnd_91053] using wordTrace_append hprefix tailTrace_91053
  have hstable : (prefixWord ++ tailWord_91053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91053).length < 2 ^ (prefixWord ++ tailWord_91053).sum := by decide
  have hdescent : baseEnd_91053 < baseStart_91053 := by decide
  rcases family_descends (prefixWord ++ tailWord_91053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91092 : List Nat := [2, 4, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_91092 : Nat := 118140960795 + 91092 * 2 ^ 59
def prefixEnd_91092 : Nat := 4983230072969 + 3 ^ 40 * 91092 * 2
def baseEnd_91092 : Nat := 31182653186308557220721

theorem tailTrace_91092 : CollatzResearch.WordTrace tailWord_91092 prefixEnd_91092 31182653186308557220721 := by
  unfold tailWord_91092
  simp only [CollatzResearch.WordTrace]
  refine ⟨1661199092998358060065765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2214932123997810746754353 1661199092998358060065765)
  ·
    refine ⟨311474829937192136262331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1661199092998358060065765 311474829937192136262331)
    ·
      refine ⟨467212244905788204393497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311474829937192136262331 467212244905788204393497)
      ·
        refine ⟨350409183679341153295123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 467212244905788204393497 350409183679341153295123)
        ·
          refine ⟨525613775519011729942685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350409183679341153295123 525613775519011729942685)
          ·
            refine ⟨197105165819629398728507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 525613775519011729942685 197105165819629398728507)
            ·
              refine ⟨295657748729444098092761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197105165819629398728507 295657748729444098092761)
              ·
                refine ⟨221743311547083073569571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295657748729444098092761 221743311547083073569571)
                ·
                  refine ⟨332614967320624610354357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221743311547083073569571 332614967320624610354357)
                  ·
                    refine ⟨31182653186308557220721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 332614967320624610354357 31182653186308557220721)
                    ·
                      rfl

theorem cell22_91092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_91092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91092 prefixEnd_91092 := by exact prefixLift 91092
  have htrace : WordTrace (prefixWord ++ tailWord_91092) baseStart_91092 baseEnd_91092 := by
    simpa [prefixWord, tailWord_91092, baseEnd_91092] using wordTrace_append hprefix tailTrace_91092
  have hstable : (prefixWord ++ tailWord_91092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91092).length < 2 ^ (prefixWord ++ tailWord_91092).sum := by decide
  have hdescent : baseEnd_91092 < baseStart_91092 := by decide
  rcases family_descends (prefixWord ++ tailWord_91092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91111 : List Nat := [1, 1, 5, 2, 2, 3, 2, 2, 4]
def baseStart_91111 : Nat := 118140960795 + 91111 * 2 ^ 59
def prefixEnd_91111 : Nat := 4983230072969 + 3 ^ 40 * 91111 * 2
def baseEnd_91111 : Nat := 10396385758199613665221

theorem tailTrace_91111 : CollatzResearch.WordTrace tailWord_91111 prefixEnd_91111 10396385758199613665221 := by
  unfold tailWord_91111
  simp only [CollatzResearch.WordTrace]
  refine ⟨3323091172927882365073187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2215394115285254910048791 3323091172927882365073187)
  ·
    refine ⟨4984636759391823547609781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3323091172927882365073187 4984636759391823547609781)
    ·
      refine ⟨467309696192983457588417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4984636759391823547609781 467309696192983457588417)
      ·
        refine ⟨350482272144737593191313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 467309696192983457588417 350482272144737593191313)
        ·
          refine ⟨262861704108553194893485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350482272144737593191313 262861704108553194893485)
          ·
            refine ⟨98573139040707448085057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 262861704108553194893485 98573139040707448085057)
            ·
              refine ⟨73929854280530586063793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98573139040707448085057 73929854280530586063793)
              ·
                refine ⟨55447390710397939547845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73929854280530586063793 55447390710397939547845)
                ·
                  refine ⟨10396385758199613665221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55447390710397939547845 10396385758199613665221)
                  ·
                    rfl

theorem cell22_91111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 4].length) (baseStart_91111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91111 prefixEnd_91111 := by exact prefixLift 91111
  have htrace : WordTrace (prefixWord ++ tailWord_91111) baseStart_91111 baseEnd_91111 := by
    simpa [prefixWord, tailWord_91111, baseEnd_91111] using wordTrace_append hprefix tailTrace_91111
  have hstable : (prefixWord ++ tailWord_91111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91111).length < 2 ^ (prefixWord ++ tailWord_91111).sum := by decide
  have hdescent : baseEnd_91111 < baseStart_91111 := by decide
  rcases family_descends (prefixWord ++ tailWord_91111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91137 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 5, 3]
def baseStart_91137 : Nat := 118140960795 + 91137 * 2 ^ 59
def prefixEnd_91137 : Nat := 4983230072969 + 3 ^ 40 * 91137 * 2
def baseEnd_91137 : Nat := 31198057605943439845583

theorem tailTrace_91137 : CollatzResearch.WordTrace tailWord_91137 prefixEnd_91137 31198057605943439845583 := by
  unfold tailWord_91137
  simp only [CollatzResearch.WordTrace]
  refine ⟨3324039470833688805519665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2216026313889125870346443 3324039470833688805519665)
  ·
    refine ⟨2493029603125266604139749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3324039470833688805519665 2493029603125266604139749)
    ·
      refine ⟨467443050585987488276203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2493029603125266604139749 467443050585987488276203)
      ·
        refine ⟨701164575878981232414305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467443050585987488276203 701164575878981232414305)
        ·
          refine ⟨525873431909235924310729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 701164575878981232414305 525873431909235924310729)
          ·
            refine ⟨394405073931926943233047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 525873431909235924310729 394405073931926943233047)
            ·
              refine ⟨591607610897890414849571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394405073931926943233047 591607610897890414849571)
              ·
                refine ⟨887411416346835622274357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 591607610897890414849571 887411416346835622274357)
                ·
                  refine ⟨83194820282515839588221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 887411416346835622274357 83194820282515839588221)
                  ·
                    refine ⟨31198057605943439845583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83194820282515839588221 31198057605943439845583)
                    ·
                      rfl

theorem cell22_91137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_91137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91137 prefixEnd_91137 := by exact prefixLift 91137
  have htrace : WordTrace (prefixWord ++ tailWord_91137) baseStart_91137 baseEnd_91137 := by
    simpa [prefixWord, tailWord_91137, baseEnd_91137] using wordTrace_append hprefix tailTrace_91137
  have hstable : (prefixWord ++ tailWord_91137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91137).length < 2 ^ (prefixWord ++ tailWord_91137).sum := by decide
  have hdescent : baseEnd_91137 < baseStart_91137 := by decide
  rcases family_descends (prefixWord ++ tailWord_91137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91167 : List Nat := [1, 1, 2, 4, 1, 3, 3, 2, 5]
def baseStart_91167 : Nat := 118140960795 + 91167 * 2 ^ 59
def prefixEnd_91167 : Nat := 4983230072969 + 3 ^ 40 * 91167 * 2
def baseEnd_91167 : Nat := 10402775739677787198497

theorem tailTrace_91167 : CollatzResearch.WordTrace tailWord_91167 prefixEnd_91167 10402775739677787198497 := by
  unfold tailWord_91167
  simp only [CollatzResearch.WordTrace]
  refine ⟨3325133660725003929111755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2216755773816669286074503 3325133660725003929111755)
  ·
    refine ⟨4987700491087505893667633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3325133660725003929111755 4987700491087505893667633)
    ·
      refine ⟨3740775368315629420250725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4987700491087505893667633 3740775368315629420250725)
      ·
        refine ⟨701395381559180516297011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3740775368315629420250725 701395381559180516297011)
        ·
          refine ⟨1052093072338770774445517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701395381559180516297011 1052093072338770774445517)
          ·
            refine ⟨394534902127039040417069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1052093072338770774445517 394534902127039040417069)
            ·
              refine ⟨147950588297639640156401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 394534902127039040417069 147950588297639640156401)
              ·
                refine ⟨110962941223229730117301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147950588297639640156401 110962941223229730117301)
                ·
                  refine ⟨10402775739677787198497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110962941223229730117301 10402775739677787198497)
                  ·
                    rfl

theorem cell22_91167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 5].length) (baseStart_91167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91167 prefixEnd_91167 := by exact prefixLift 91167
  have htrace : WordTrace (prefixWord ++ tailWord_91167) baseStart_91167 baseEnd_91167 := by
    simpa [prefixWord, tailWord_91167, baseEnd_91167] using wordTrace_append hprefix tailTrace_91167
  have hstable : (prefixWord ++ tailWord_91167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91167).length < 2 ^ (prefixWord ++ tailWord_91167).sum := by decide
  have hdescent : baseEnd_91167 < baseStart_91167 := by decide
  rcases family_descends (prefixWord ++ tailWord_91167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91182 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 2, 5]
def baseStart_91182 : Nat := 118140960795 + 91182 * 2 ^ 59
def prefixEnd_91182 : Nat := 4983230072969 + 3 ^ 40 * 91182 * 2
def baseEnd_91182 : Nat := 31213462025578322470445

theorem tailTrace_91182 : CollatzResearch.WordTrace tailWord_91182 prefixEnd_91182 31213462025578322470445 := by
  unfold tailWord_91182
  simp only [CollatzResearch.WordTrace]
  refine ⟨415710094458832686363475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2217120503780440993938533 415710094458832686363475)
  ·
    refine ⟨623565141688249029545213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 415710094458832686363475 623565141688249029545213)
    ·
      refine ⟨233836928133093386079455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 623565141688249029545213 233836928133093386079455)
      ·
        refine ⟨350755392199640079119183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233836928133093386079455 350755392199640079119183)
        ·
          refine ⟨526133088299460118678775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350755392199640079119183 526133088299460118678775)
          ·
            refine ⟨789199632449190178018163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526133088299460118678775 789199632449190178018163)
            ·
              refine ⟨1183799448673785267027245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 789199632449190178018163 1183799448673785267027245)
              ·
                refine ⟨443924793252669475135217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1183799448673785267027245 443924793252669475135217)
                ·
                  refine ⟨332943594939502106351413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443924793252669475135217 332943594939502106351413)
                  ·
                    refine ⟨31213462025578322470445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 332943594939502106351413 31213462025578322470445)
                    ·
                      rfl

theorem cell22_91182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_91182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91182 prefixEnd_91182 := by exact prefixLift 91182
  have htrace : WordTrace (prefixWord ++ tailWord_91182) baseStart_91182 baseEnd_91182 := by
    simpa [prefixWord, tailWord_91182, baseEnd_91182] using wordTrace_append hprefix tailTrace_91182
  have hstable : (prefixWord ++ tailWord_91182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91182).length < 2 ^ (prefixWord ++ tailWord_91182).sum := by decide
  have hdescent : baseEnd_91182 < baseStart_91182 := by decide
  rcases family_descends (prefixWord ++ tailWord_91182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91222 : List Nat := [5, 2, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_91222 : Nat := 118140960795 + 91222 * 2 ^ 59
def prefixEnd_91222 : Nat := 4983230072969 + 3 ^ 40 * 91222 * 2
def baseEnd_91222 : Nat := 31227154843031551470323

theorem tailTrace_91222 : CollatzResearch.WordTrace tailWord_91222 prefixEnd_91222 31227154843031551470323 := by
  unfold tailWord_91222
  simp only [CollatzResearch.WordTrace]
  refine ⟨207946229720359270147745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2218093117017165548242613 207946229720359270147745)
  ·
    refine ⟨155959672290269452610809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207946229720359270147745 155959672290269452610809)
    ·
      refine ⟨116969754217702089458107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155959672290269452610809 116969754217702089458107)
      ·
        refine ⟨175454631326553134187161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116969754217702089458107 175454631326553134187161)
        ·
          refine ⟨131590973494914850640371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175454631326553134187161 131590973494914850640371)
          ·
            refine ⟨197386460242372275960557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131590973494914850640371 197386460242372275960557)
            ·
              refine ⟨74019922590889603485209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197386460242372275960557 74019922590889603485209)
              ·
                refine ⟨55514941943167202613907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74019922590889603485209 55514941943167202613907)
                ·
                  refine ⟨83272412914750803920861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55514941943167202613907 83272412914750803920861)
                  ·
                    refine ⟨31227154843031551470323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83272412914750803920861 31227154843031551470323)
                    ·
                      rfl

theorem cell22_91222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_91222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91222 prefixEnd_91222 := by exact prefixLift 91222
  have htrace : WordTrace (prefixWord ++ tailWord_91222) baseStart_91222 baseEnd_91222 := by
    simpa [prefixWord, tailWord_91222, baseEnd_91222] using wordTrace_append hprefix tailTrace_91222
  have hstable : (prefixWord ++ tailWord_91222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91222).length < 2 ^ (prefixWord ++ tailWord_91222).sum := by decide
  have hdescent : baseEnd_91222 < baseStart_91222 := by decide
  rcases family_descends (prefixWord ++ tailWord_91222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91225 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 3, 6]
def baseStart_91225 : Nat := 118140960795 + 91225 * 2 ^ 59
def prefixEnd_91225 : Nat := 4983230072969 + 3 ^ 40 * 91225 * 2
def baseEnd_91225 : Nat := 31228181804340543645313

theorem tailTrace_91225 : CollatzResearch.WordTrace tailWord_91225 prefixEnd_91225 31228181804340543645313 := by
  unfold tailWord_91225
  simp only [CollatzResearch.WordTrace]
  refine ⟨3327249094514879834723129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2218166063009919889815419 3327249094514879834723129)
  ·
    refine ⟨2495436820886159876042347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3327249094514879834723129 2495436820886159876042347)
    ·
      refine ⟨3743155231329239814063521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2495436820886159876042347 3743155231329239814063521)
      ·
        refine ⟨2807366423496929860547641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3743155231329239814063521 2807366423496929860547641)
        ·
          refine ⟨2105524817622697395410731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2807366423496929860547641 2105524817622697395410731)
          ·
            refine ⟨3158287226434046093116097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2105524817622697395410731 3158287226434046093116097)
            ·
              refine ⟨2368715419825534569837073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3158287226434046093116097 2368715419825534569837073)
              ·
                refine ⟨1776536564869150927377805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2368715419825534569837073 1776536564869150927377805)
                ·
                  refine ⟨666201211825931597766677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1776536564869150927377805 666201211825931597766677)
                  ·
                    refine ⟨31228181804340543645313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 666201211825931597766677 31228181804340543645313)
                    ·
                      rfl

theorem cell22_91225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_91225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91225 prefixEnd_91225 := by exact prefixLift 91225
  have htrace : WordTrace (prefixWord ++ tailWord_91225) baseStart_91225 baseEnd_91225 := by
    simpa [prefixWord, tailWord_91225, baseEnd_91225] using wordTrace_append hprefix tailTrace_91225
  have hstable : (prefixWord ++ tailWord_91225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91225).length < 2 ^ (prefixWord ++ tailWord_91225).sum := by decide
  have hdescent : baseEnd_91225 < baseStart_91225 := by decide
  rcases family_descends (prefixWord ++ tailWord_91225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91244 : List Nat := [2, 2, 1, 1, 3, 2, 3, 3, 2, 3]
def baseStart_91244 : Nat := 118140960795 + 91244 * 2 ^ 59
def prefixEnd_91244 : Nat := 4983230072969 + 3 ^ 40 * 91244 * 2
def baseEnd_91244 : Nat := 31234685892630827420255

theorem tailTrace_91244 : CollatzResearch.WordTrace tailWord_91244 prefixEnd_91244 31234685892630827420255 := by
  unfold tailWord_91244
  simp only [CollatzResearch.WordTrace]
  refine ⟨1663971040723023039832393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2218628054297364053109857 1663971040723023039832393)
  ·
    refine ⟨1247978280542267279874295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1663971040723023039832393 1247978280542267279874295)
    ·
      refine ⟨1871967420813400919811443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1247978280542267279874295 1871967420813400919811443)
      ·
        refine ⟨2807951131220101379717165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1871967420813400919811443 2807951131220101379717165)
        ·
          refine ⟨1052981674207538017393937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2807951131220101379717165 1052981674207538017393937)
          ·
            refine ⟨789736255655653513045453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1052981674207538017393937 789736255655653513045453)
            ·
              refine ⟨296151095870870067392045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 789736255655653513045453 296151095870870067392045)
              ·
                refine ⟨111056660951576275272017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 296151095870870067392045 111056660951576275272017)
                ·
                  refine ⟨83292495713682206454013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111056660951576275272017 83292495713682206454013)
                  ·
                    refine ⟨31234685892630827420255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83292495713682206454013 31234685892630827420255)
                    ·
                      rfl

theorem cell22_91244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 3].length) (baseStart_91244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91244 prefixEnd_91244 := by exact prefixLift 91244
  have htrace : WordTrace (prefixWord ++ tailWord_91244) baseStart_91244 baseEnd_91244 := by
    simpa [prefixWord, tailWord_91244, baseEnd_91244] using wordTrace_append hprefix tailTrace_91244
  have hstable : (prefixWord ++ tailWord_91244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91244).length < 2 ^ (prefixWord ++ tailWord_91244).sum := by decide
  have hdescent : baseEnd_91244 < baseStart_91244 := by decide
  rcases family_descends (prefixWord ++ tailWord_91244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91287 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 2, 6]
def baseStart_91287 : Nat := 118140960795 + 91287 * 2 ^ 59
def prefixEnd_91287 : Nat := 4983230072969 + 3 ^ 40 * 91287 * 2
def baseEnd_91287 : Nat := 31249405671393048595123

theorem tailTrace_91287 : CollatzResearch.WordTrace tailWord_91287 prefixEnd_91287 31249405671393048595123 := by
  unfold tailWord_91287
  simp only [CollatzResearch.WordTrace]
  refine ⟨3329510420290264423480115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2219673613526842948986743 3329510420290264423480115)
  ·
    refine ⟨4994265630435396635220173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3329510420290264423480115 4994265630435396635220173)
    ·
      refine ⟨1872849611413273738207565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4994265630435396635220173 1872849611413273738207565)
      ·
        refine ⟨702318604279977651827837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1872849611413273738207565 702318604279977651827837)
        ·
          refine ⟨263369476604991619435439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 702318604279977651827837 263369476604991619435439)
          ·
            refine ⟨395054214907487429153159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263369476604991619435439 395054214907487429153159)
            ·
              refine ⟨592581322361231143729739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395054214907487429153159 592581322361231143729739)
              ·
                refine ⟨888871983541846715594609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592581322361231143729739 888871983541846715594609)
                ·
                  refine ⟨666653987656385036695957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 888871983541846715594609 666653987656385036695957)
                  ·
                    refine ⟨31249405671393048595123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 666653987656385036695957 31249405671393048595123)
                    ·
                      rfl

theorem cell22_91287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_91287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91287 prefixEnd_91287 := by exact prefixLift 91287
  have htrace : WordTrace (prefixWord ++ tailWord_91287) baseStart_91287 baseEnd_91287 := by
    simpa [prefixWord, tailWord_91287, baseEnd_91287] using wordTrace_append hprefix tailTrace_91287
  have hstable : (prefixWord ++ tailWord_91287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91287).length < 2 ^ (prefixWord ++ tailWord_91287).sum := by decide
  have hdescent : baseEnd_91287 < baseStart_91287 := by decide
  rcases family_descends (prefixWord ++ tailWord_91287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91306 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 5, 3]
def baseStart_91306 : Nat := 118140960795 + 91306 * 2 ^ 59
def prefixEnd_91306 : Nat := 4983230072969 + 3 ^ 40 * 91306 * 2
def baseEnd_91306 : Nat := 31255909759683332370065

theorem tailTrace_91306 : CollatzResearch.WordTrace tailWord_91306 prefixEnd_91306 31255909759683332370065 := by
  unfold tailWord_91306
  simp only [CollatzResearch.WordTrace]
  refine ⟨832550851805357667105443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2220135604814287112281181 832550851805357667105443)
  ·
    refine ⟨1248826277708036500658165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 832550851805357667105443 1248826277708036500658165)
    ·
      refine ⟨117077463535128421936703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1248826277708036500658165 117077463535128421936703)
      ·
        refine ⟨175616195302692632905055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117077463535128421936703 175616195302692632905055)
        ·
          refine ⟨263424292954038949357583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175616195302692632905055 263424292954038949357583)
          ·
            refine ⟨395136439431058424036375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263424292954038949357583 395136439431058424036375)
            ·
              refine ⟨592704659146587636054563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395136439431058424036375 592704659146587636054563)
              ·
                refine ⟨889056988719881454081845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592704659146587636054563 889056988719881454081845)
                ·
                  refine ⟨83349092692488886320173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 889056988719881454081845 83349092692488886320173)
                  ·
                    refine ⟨31255909759683332370065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83349092692488886320173 31255909759683332370065)
                    ·
                      rfl

theorem cell22_91306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_91306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91306 prefixEnd_91306 := by exact prefixLift 91306
  have htrace : WordTrace (prefixWord ++ tailWord_91306) baseStart_91306 baseEnd_91306 := by
    simpa [prefixWord, tailWord_91306, baseEnd_91306] using wordTrace_append hprefix tailTrace_91306
  have hstable : (prefixWord ++ tailWord_91306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91306).length < 2 ^ (prefixWord ++ tailWord_91306).sum := by decide
  have hdescent : baseEnd_91306 < baseStart_91306 := by decide
  rcases family_descends (prefixWord ++ tailWord_91306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91379 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 4, 3]
def baseStart_91379 : Nat := 118140960795 + 91379 * 2 ^ 59
def prefixEnd_91379 : Nat := 4983230072969 + 3 ^ 40 * 91379 * 2
def baseEnd_91379 : Nat := 31280899151535475294841

theorem tailTrace_91379 : CollatzResearch.WordTrace tailWord_91379 prefixEnd_91379 31280899151535475294841 := by
  unfold tailWord_91379
  simp only [CollatzResearch.WordTrace]
  refine ⟨3332865935956964135829191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2221910623971309423886127 3332865935956964135829191)
  ·
    refine ⟨4999298903935446203743787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3332865935956964135829191 4999298903935446203743787)
    ·
      refine ⟨7498948355903169305615681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4999298903935446203743787 7498948355903169305615681)
      ·
        refine ⟨5624211266927376979211761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7498948355903169305615681 5624211266927376979211761)
        ·
          refine ⟨4218158450195532734408821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5624211266927376979211761 4218158450195532734408821)
          ·
            refine ⟨395452354705831193850827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4218158450195532734408821 395452354705831193850827)
            ·
              refine ⟨593178532058746790776241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395452354705831193850827 593178532058746790776241)
              ·
                refine ⟨444883899044060093082181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 593178532058746790776241 444883899044060093082181)
                ·
                  refine ⟨83415731070761267452909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 444883899044060093082181 83415731070761267452909)
                  ·
                    refine ⟨31280899151535475294841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83415731070761267452909 31280899151535475294841)
                    ·
                      rfl

theorem cell22_91379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 3].length) (baseStart_91379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91379 prefixEnd_91379 := by exact prefixLift 91379
  have htrace : WordTrace (prefixWord ++ tailWord_91379) baseStart_91379 baseEnd_91379 := by
    simpa [prefixWord, tailWord_91379, baseEnd_91379] using wordTrace_append hprefix tailTrace_91379
  have hstable : (prefixWord ++ tailWord_91379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91379).length < 2 ^ (prefixWord ++ tailWord_91379).sum := by decide
  have hdescent : baseEnd_91379 < baseStart_91379 := by decide
  rcases family_descends (prefixWord ++ tailWord_91379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91396 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 4, 3]
def baseStart_91396 : Nat := 118140960795 + 91396 * 2 ^ 59
def prefixEnd_91396 : Nat := 4983230072969 + 3 ^ 40 * 91396 * 2
def baseEnd_91396 : Nat := 31286718598953097619789

theorem tailTrace_91396 : CollatzResearch.WordTrace tailWord_91396 prefixEnd_91396 31286718598953097619789 := by
  unfold tailWord_91396
  simp only [CollatzResearch.WordTrace]
  refine ⟨1666742988447688019599021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2222323984596917359465361 1666742988447688019599021)
  ·
    refine ⟨625028620667883007349633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1666742988447688019599021 625028620667883007349633)
    ·
      refine ⟨468771465500912255512225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 625028620667883007349633 468771465500912255512225)
      ·
        refine ⟨351578599125684191634169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 468771465500912255512225 351578599125684191634169)
        ·
          refine ⟨263683949344263143725627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351578599125684191634169 263683949344263143725627)
          ·
            refine ⟨395525924016394715588441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263683949344263143725627 395525924016394715588441)
            ·
              refine ⟨296644443012296036691331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395525924016394715588441 296644443012296036691331)
              ·
                refine ⟨444966664518444055036997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296644443012296036691331 444966664518444055036997)
                ·
                  refine ⟨83431249597208260319437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 444966664518444055036997 83431249597208260319437)
                  ·
                    refine ⟨31286718598953097619789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83431249597208260319437 31286718598953097619789)
                    ·
                      rfl

theorem cell22_91396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_91396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91396 prefixEnd_91396 := by exact prefixLift 91396
  have htrace : WordTrace (prefixWord ++ tailWord_91396) baseStart_91396 baseEnd_91396 := by
    simpa [prefixWord, tailWord_91396, baseEnd_91396] using wordTrace_append hprefix tailTrace_91396
  have hstable : (prefixWord ++ tailWord_91396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91396).length < 2 ^ (prefixWord ++ tailWord_91396).sum := by decide
  have hdescent : baseEnd_91396 < baseStart_91396 := by decide
  rcases family_descends (prefixWord ++ tailWord_91396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91516 : List Nat := [2, 2, 2, 1, 1, 1, 3, 6, 4]
def baseStart_91516 : Nat := 118140960795 + 91516 * 2 ^ 59
def prefixEnd_91516 : Nat := 4983230072969 + 3 ^ 40 * 91516 * 2
def baseEnd_91516 : Nat := 10442599017104261539807

theorem tailTrace_91516 : CollatzResearch.WordTrace tailWord_91516 prefixEnd_91516 10442599017104261539807 := by
  unfold tailWord_91516
  simp only [CollatzResearch.WordTrace]
  refine ⟨1668931368230318266783201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2225241824307091022377601 1668931368230318266783201)
  ·
    refine ⟨1251698526172738700087401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1668931368230318266783201 1251698526172738700087401)
    ·
      refine ⟨938773894629554025065551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1251698526172738700087401 938773894629554025065551)
      ·
        refine ⟨1408160841944331037598327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 938773894629554025065551 1408160841944331037598327)
        ·
          refine ⟨2112241262916496556397491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1408160841944331037598327 2112241262916496556397491)
          ·
            refine ⟨3168361894374744834596237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2112241262916496556397491 3168361894374744834596237)
            ·
              refine ⟨1188135710390529312973589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3168361894374744834596237 1188135710390529312973589)
              ·
                refine ⟨55693861424556061545637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1188135710390529312973589 55693861424556061545637)
                ·
                  refine ⟨10442599017104261539807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55693861424556061545637 10442599017104261539807)
                  ·
                    rfl

theorem cell22_91516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 4].length) (baseStart_91516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91516 prefixEnd_91516 := by exact prefixLift 91516
  have htrace : WordTrace (prefixWord ++ tailWord_91516) baseStart_91516 baseEnd_91516 := by
    simpa [prefixWord, tailWord_91516, baseEnd_91516] using wordTrace_append hprefix tailTrace_91516
  have hstable : (prefixWord ++ tailWord_91516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91516).length < 2 ^ (prefixWord ++ tailWord_91516).sum := by decide
  have hdescent : baseEnd_91516 < baseStart_91516 := by decide
  rcases family_descends (prefixWord ++ tailWord_91516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91546 : List Nat := [3, 1, 1, 4, 1, 1, 2, 3, 2, 4]
def baseStart_91546 : Nat := 118140960795 + 91546 * 2 ^ 59
def prefixEnd_91546 : Nat := 4983230072969 + 3 ^ 40 * 91546 * 2
def baseEnd_91546 : Nat := 31338066664402706369329

theorem tailTrace_91546 : CollatzResearch.WordTrace tailWord_91546 prefixEnd_91546 31338066664402706369329 := by
  unfold tailWord_91546
  simp only [CollatzResearch.WordTrace]
  refine ⟨834739231587987914289623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2225971284234634438105661 834739231587987914289623)
  ·
    refine ⟨1252108847381981871434435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 834739231587987914289623 1252108847381981871434435)
    ·
      refine ⟨1878163271072972807151653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1252108847381981871434435 1878163271072972807151653)
      ·
        refine ⟨352155613326182401340935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1878163271072972807151653 352155613326182401340935)
        ·
          refine ⟨528233419989273602011403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352155613326182401340935 528233419989273602011403)
          ·
            refine ⟨792350129983910403017105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528233419989273602011403 792350129983910403017105)
            ·
              refine ⟨594262597487932802262829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 792350129983910403017105 594262597487932802262829)
              ·
                refine ⟨222848474057974800848561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 594262597487932802262829 222848474057974800848561)
                ·
                  refine ⟨167136355543481100636421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 222848474057974800848561 167136355543481100636421)
                  ·
                    refine ⟨31338066664402706369329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 167136355543481100636421 31338066664402706369329)
                    ·
                      rfl

theorem cell22_91546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_91546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91546 prefixEnd_91546 := by exact prefixLift 91546
  have htrace : WordTrace (prefixWord ++ tailWord_91546) baseStart_91546 baseEnd_91546 := by
    simpa [prefixWord, tailWord_91546, baseEnd_91546] using wordTrace_append hprefix tailTrace_91546
  have hstable : (prefixWord ++ tailWord_91546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91546).length < 2 ^ (prefixWord ++ tailWord_91546).sum := by decide
  have hdescent : baseEnd_91546 < baseStart_91546 := by decide
  rcases family_descends (prefixWord ++ tailWord_91546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91586 : List Nat := [3, 5, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_91586 : Nat := 118140960795 + 91586 * 2 ^ 59
def prefixEnd_91586 : Nat := 4983230072969 + 3 ^ 40 * 91586 * 2
def baseEnd_91586 : Nat := 31351759481855935369207

theorem tailTrace_91586 : CollatzResearch.WordTrace tailWord_91586 prefixEnd_91586 31351759481855935369207 := by
  unfold tailWord_91586
  simp only [CollatzResearch.WordTrace]
  refine ⟨835103961551759622153653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2226943897471358992409741 835103961551759622153653)
  ·
    refine ⟨78290996395477464576905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 835103961551759622153653 78290996395477464576905)
    ·
      refine ⟨58718247296608098432679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78290996395477464576905 58718247296608098432679)
      ·
        refine ⟨88077370944912147649019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58718247296608098432679 88077370944912147649019)
        ·
          refine ⟨132116056417368221473529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88077370944912147649019 132116056417368221473529)
          ·
            refine ⟨99087042313026166105147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132116056417368221473529 99087042313026166105147)
            ·
              refine ⟨148630563469539249157721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99087042313026166105147 148630563469539249157721)
              ·
                refine ⟨111472922602154436868291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148630563469539249157721 111472922602154436868291)
                ·
                  refine ⟨167209383903231655302437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111472922602154436868291 167209383903231655302437)
                  ·
                    refine ⟨31351759481855935369207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 167209383903231655302437 31351759481855935369207)
                    ·
                      rfl

theorem cell22_91586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_91586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91586 prefixEnd_91586 := by exact prefixLift 91586
  have htrace : WordTrace (prefixWord ++ tailWord_91586) baseStart_91586 baseEnd_91586 := by
    simpa [prefixWord, tailWord_91586, baseEnd_91586] using wordTrace_append hprefix tailTrace_91586
  have hstable : (prefixWord ++ tailWord_91586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91586).length < 2 ^ (prefixWord ++ tailWord_91586).sum := by decide
  have hdescent : baseEnd_91586 < baseStart_91586 := by decide
  rcases family_descends (prefixWord ++ tailWord_91586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91623 : List Nat := [1, 1, 5, 2, 1, 3, 2, 2, 5]
def baseStart_91623 : Nat := 118140960795 + 91623 * 2 ^ 59
def prefixEnd_91623 : Nat := 4983230072969 + 3 ^ 40 * 91623 * 2
def baseEnd_91623 : Nat := 10454808446000057398031

theorem tailTrace_91623 : CollatzResearch.WordTrace tailWord_91623 prefixEnd_91623 10454808446000057398031 := by
  unfold tailWord_91623
  simp only [CollatzResearch.WordTrace]
  refine ⟨3341765347072993807711523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2227843564715329205141015 3341765347072993807711523)
  ·
    refine ⟨5012648020609490711567285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3341765347072993807711523 5012648020609490711567285)
    ·
      refine ⟨469935751932139754209433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5012648020609490711567285 469935751932139754209433)
      ·
        refine ⟨352451813949104815657075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 469935751932139754209433 352451813949104815657075)
        ·
          refine ⟨528677720923657223485613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352451813949104815657075 528677720923657223485613)
          ·
            refine ⟨198254145346371458807105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 528677720923657223485613 198254145346371458807105)
            ·
              refine ⟨148690609009778594105329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198254145346371458807105 148690609009778594105329)
              ·
                refine ⟨111517956757333945578997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148690609009778594105329 111517956757333945578997)
                ·
                  refine ⟨10454808446000057398031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111517956757333945578997 10454808446000057398031)
                  ·
                    rfl

theorem cell22_91623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 5].length) (baseStart_91623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91623 prefixEnd_91623 := by exact prefixLift 91623
  have htrace : WordTrace (prefixWord ++ tailWord_91623) baseStart_91623 baseEnd_91623 := by
    simpa [prefixWord, tailWord_91623, baseEnd_91623] using wordTrace_append hprefix tailTrace_91623
  have hstable : (prefixWord ++ tailWord_91623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91623).length < 2 ^ (prefixWord ++ tailWord_91623).sum := by decide
  have hdescent : baseEnd_91623 < baseStart_91623 := by decide
  rcases family_descends (prefixWord ++ tailWord_91623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91638 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_91638 : Nat := 118140960795 + 91638 * 2 ^ 59
def prefixEnd_91638 : Nat := 4983230072969 + 3 ^ 40 * 91638 * 2
def baseEnd_91638 : Nat := 31369560144545133069047

theorem tailTrace_91638 : CollatzResearch.WordTrace tailWord_91638 prefixEnd_91638 31369560144545133069047 := by
  unfold tailWord_91638
  simp only [CollatzResearch.WordTrace]
  refine ⟨208894527626165710594223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2228208294679100913005045 208894527626165710594223)
  ·
    refine ⟨313341791439248565891335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208894527626165710594223 313341791439248565891335)
    ·
      refine ⟨470012687158872848837003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313341791439248565891335 470012687158872848837003)
      ·
        refine ⟨705019030738309273255505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470012687158872848837003 705019030738309273255505)
        ·
          refine ⟨528764273053731954941629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 705019030738309273255505 528764273053731954941629)
          ·
            refine ⟨198286602395149483103111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 528764273053731954941629 198286602395149483103111)
            ·
              refine ⟨297429903592724224654667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198286602395149483103111 297429903592724224654667)
              ·
                refine ⟨446144855389086336982001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297429903592724224654667 446144855389086336982001)
                ·
                  refine ⟨334608641541814752736501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446144855389086336982001 334608641541814752736501)
                  ·
                    refine ⟨31369560144545133069047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 334608641541814752736501 31369560144545133069047)
                    ·
                      rfl

theorem cell22_91638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_91638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91638 prefixEnd_91638 := by exact prefixLift 91638
  have htrace : WordTrace (prefixWord ++ tailWord_91638) baseStart_91638 baseEnd_91638 := by
    simpa [prefixWord, tailWord_91638, baseEnd_91638] using wordTrace_append hprefix tailTrace_91638
  have hstable : (prefixWord ++ tailWord_91638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91638).length < 2 ^ (prefixWord ++ tailWord_91638).sum := by decide
  have hdescent : baseEnd_91638 < baseStart_91638 := by decide
  rcases family_descends (prefixWord ++ tailWord_91638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91661 : List Nat := [1, 7, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_91661 : Nat := 118140960795 + 91661 * 2 ^ 59
def prefixEnd_91661 : Nat := 4983230072969 + 3 ^ 40 * 91661 * 2
def baseEnd_91661 : Nat := 31377433514580739743977

theorem tailTrace_91661 : CollatzResearch.WordTrace tailWord_91661 prefixEnd_91661 31377433514580739743977 := by
  unfold tailWord_91661
  simp only [CollatzResearch.WordTrace]
  refine ⟨3343151320935326297594837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2228767547290217531729891 3343151320935326297594837)
  ·
    refine ⟨78355109084421710099879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 3343151320935326297594837 78355109084421710099879)
    ·
      refine ⟨117532663626632565149819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78355109084421710099879 117532663626632565149819)
      ·
        refine ⟨176298995439948847724729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117532663626632565149819 176298995439948847724729)
        ·
          refine ⟨132224246579961635793547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176298995439948847724729 132224246579961635793547)
          ·
            refine ⟨198336369869942453690321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132224246579961635793547 198336369869942453690321)
            ·
              refine ⟨148752277402456840267741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198336369869942453690321 148752277402456840267741)
              ·
                refine ⟨55782104025921315100403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148752277402456840267741 55782104025921315100403)
                ·
                  refine ⟨83673156038881972650605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55782104025921315100403 83673156038881972650605)
                  ·
                    refine ⟨31377433514580739743977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83673156038881972650605 31377433514580739743977)
                    ·
                      rfl

theorem cell22_91661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_91661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91661 prefixEnd_91661 := by exact prefixLift 91661
  have htrace : WordTrace (prefixWord ++ tailWord_91661) baseStart_91661 baseEnd_91661 := by
    simpa [prefixWord, tailWord_91661, baseEnd_91661] using wordTrace_append hprefix tailTrace_91661
  have hstable : (prefixWord ++ tailWord_91661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91661).length < 2 ^ (prefixWord ++ tailWord_91661).sum := by decide
  have hdescent : baseEnd_91661 < baseStart_91661 := by decide
  rcases family_descends (prefixWord ++ tailWord_91661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91726 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 1, 8]
def baseStart_91726 : Nat := 118140960795 + 91726 * 2 ^ 59
def prefixEnd_91726 : Nat := 4983230072969 + 3 ^ 40 * 91726 * 2
def baseEnd_91726 : Nat := 31399684342942236868777

theorem tailTrace_91726 : CollatzResearch.WordTrace tailWord_91726 prefixEnd_91726 31399684342942236868777 := by
  unfold tailWord_91726
  simp only [CollatzResearch.WordTrace]
  refine ⟨418190258212480299838879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2230348043799894932474021 418190258212480299838879)
  ·
    refine ⟨627285387318720449758319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 418190258212480299838879 627285387318720449758319)
    ·
      refine ⟨940928080978080674637479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 627285387318720449758319 940928080978080674637479)
      ·
        refine ⟨1411392121467121011956219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 940928080978080674637479 1411392121467121011956219)
        ·
          refine ⟨2117088182200681517934329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1411392121467121011956219 2117088182200681517934329)
          ·
            refine ⟨1587816136650511138450747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2117088182200681517934329 1587816136650511138450747)
            ·
              refine ⟨2381724204975766707676121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1587816136650511138450747 2381724204975766707676121)
              ·
                refine ⟨1786293153731825030757091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2381724204975766707676121 1786293153731825030757091)
                ·
                  refine ⟨2679439730597737546135637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1786293153731825030757091 2679439730597737546135637)
                  ·
                    refine ⟨31399684342942236868777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2679439730597737546135637 31399684342942236868777)
                    ·
                      rfl

theorem cell22_91726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_91726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91726 prefixEnd_91726 := by exact prefixLift 91726
  have htrace : WordTrace (prefixWord ++ tailWord_91726) baseStart_91726 baseEnd_91726 := by
    simpa [prefixWord, tailWord_91726, baseEnd_91726] using wordTrace_append hprefix tailTrace_91726
  have hstable : (prefixWord ++ tailWord_91726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91726).length < 2 ^ (prefixWord ++ tailWord_91726).sum := by decide
  have hdescent : baseEnd_91726 < baseStart_91726 := by decide
  rcases family_descends (prefixWord ++ tailWord_91726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91756 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 1, 7]
def baseStart_91756 : Nat := 118140960795 + 91756 * 2 ^ 59
def prefixEnd_91756 : Nat := 4983230072969 + 3 ^ 40 * 91756 * 2
def baseEnd_91756 : Nat := 31409953956032158618685

theorem tailTrace_91756 : CollatzResearch.WordTrace tailWord_91756 prefixEnd_91756 31409953956032158618685 := by
  unfold tailWord_91756
  simp only [CollatzResearch.WordTrace]
  refine ⟨1673308127795578761151561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2231077503727438348202081 1673308127795578761151561)
  ·
    refine ⟨1254981095846684070863671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1673308127795578761151561 1254981095846684070863671)
    ·
      refine ⟨1882471643770026106295507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1254981095846684070863671 1882471643770026106295507)
      ·
        refine ⟨2823707465655039159443261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1882471643770026106295507 2823707465655039159443261)
        ·
          refine ⟨1058890299620639684791223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2823707465655039159443261 1058890299620639684791223)
          ·
            refine ⟨1588335449430959527186835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058890299620639684791223 1588335449430959527186835)
            ·
              refine ⟨2382503174146439290780253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1588335449430959527186835 2382503174146439290780253)
              ·
                refine ⟨893438690304914734042595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2382503174146439290780253 893438690304914734042595)
                ·
                  refine ⟨1340158035457372101063893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 893438690304914734042595 1340158035457372101063893)
                  ·
                    refine ⟨31409953956032158618685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1340158035457372101063893 31409953956032158618685)
                    ·
                      rfl

theorem cell22_91756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_91756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91756 prefixEnd_91756 := by exact prefixLift 91756
  have htrace : WordTrace (prefixWord ++ tailWord_91756) baseStart_91756 baseEnd_91756 := by
    simpa [prefixWord, tailWord_91756, baseEnd_91756] using wordTrace_append hprefix tailTrace_91756
  have hstable : (prefixWord ++ tailWord_91756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91756).length < 2 ^ (prefixWord ++ tailWord_91756).sum := by decide
  have hdescent : baseEnd_91756 < baseStart_91756 := by decide
  rcases family_descends (prefixWord ++ tailWord_91756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91852 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 4, 3]
def baseStart_91852 : Nat := 118140960795 + 91852 * 2 ^ 59
def prefixEnd_91852 : Nat := 4983230072969 + 3 ^ 40 * 91852 * 2
def baseEnd_91852 : Nat := 31442816717919908218391

theorem tailTrace_91852 : CollatzResearch.WordTrace tailWord_91852 prefixEnd_91852 31442816717919908218391 := by
  unfold tailWord_91852
  simp only [CollatzResearch.WordTrace]
  refine ⟨1675058831621682958898905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2233411775495577278531873 1675058831621682958898905)
  ·
    refine ⟨1256294123716262219174179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1675058831621682958898905 1256294123716262219174179)
    ·
      refine ⟨1884441185574393328761269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1256294123716262219174179 1884441185574393328761269)
      ·
        refine ⟨176666361147599374571369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1884441185574393328761269 176666361147599374571369)
        ·
          refine ⟨132499770860699530928527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176666361147599374571369 132499770860699530928527)
          ·
            refine ⟨198749656291049296392791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132499770860699530928527 198749656291049296392791)
            ·
              refine ⟨298124484436573944589187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198749656291049296392791 298124484436573944589187)
              ·
                refine ⟨447186726654860916883781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298124484436573944589187 447186726654860916883781)
                ·
                  refine ⟨83847511247786421915709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 447186726654860916883781 83847511247786421915709)
                  ·
                    refine ⟨31442816717919908218391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83847511247786421915709 31442816717919908218391)
                    ·
                      rfl

theorem cell22_91852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 4, 3].length) (baseStart_91852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91852 prefixEnd_91852 := by exact prefixLift 91852
  have htrace : WordTrace (prefixWord ++ tailWord_91852) baseStart_91852 baseEnd_91852 := by
    simpa [prefixWord, tailWord_91852, baseEnd_91852] using wordTrace_append hprefix tailTrace_91852
  have hstable : (prefixWord ++ tailWord_91852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91852).length < 2 ^ (prefixWord ++ tailWord_91852).sum := by decide
  have hdescent : baseEnd_91852 < baseStart_91852 := by decide
  rcases family_descends (prefixWord ++ tailWord_91852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91869 : List Nat := [1, 4, 3, 3, 1, 2, 1, 1, 1, 5]
def baseStart_91869 : Nat := 118140960795 + 91869 * 2 ^ 59
def prefixEnd_91869 : Nat := 4983230072969 + 3 ^ 40 * 91869 * 2
def baseEnd_91869 : Nat := 31448636165337530543339

theorem tailTrace_91869 : CollatzResearch.WordTrace tailWord_91869 prefixEnd_91869 31448636165337530543339 := by
  unfold tailWord_91869
  simp only [CollatzResearch.WordTrace]
  refine ⟨3350737704181777821166661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2233825136121185214111107 3350737704181777821166661)
  ·
    refine ⟨628263319534083341468749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3350737704181777821166661 628263319534083341468749)
    ·
      refine ⟨235598744825281253050781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 628263319534083341468749 235598744825281253050781)
      ·
        refine ⟨88349529309480469894043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235598744825281253050781 88349529309480469894043)
        ·
          refine ⟨132524293964220704841065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88349529309480469894043 132524293964220704841065)
          ·
            refine ⟨99393220473165528630799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132524293964220704841065 99393220473165528630799)
            ·
              refine ⟨149089830709748292946199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99393220473165528630799 149089830709748292946199)
              ·
                refine ⟨223634746064622439419299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149089830709748292946199 223634746064622439419299)
                ·
                  refine ⟨335452119096933659128949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223634746064622439419299 335452119096933659128949)
                  ·
                    refine ⟨31448636165337530543339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 335452119096933659128949 31448636165337530543339)
                    ·
                      rfl

theorem cell22_91869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_91869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91869 prefixEnd_91869 := by exact prefixLift 91869
  have htrace : WordTrace (prefixWord ++ tailWord_91869) baseStart_91869 baseEnd_91869 := by
    simpa [prefixWord, tailWord_91869, baseEnd_91869] using wordTrace_append hprefix tailTrace_91869
  have hstable : (prefixWord ++ tailWord_91869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91869).length < 2 ^ (prefixWord ++ tailWord_91869).sum := by decide
  have hdescent : baseEnd_91869 < baseStart_91869 := by decide
  rcases family_descends (prefixWord ++ tailWord_91869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91927 : List Nat := [1, 1, 3, 4, 2, 1, 4, 1, 5]
def baseStart_91927 : Nat := 118140960795 + 91927 * 2 ^ 59
def prefixEnd_91927 : Nat := 4983230072969 + 3 ^ 40 * 91927 * 2
def baseEnd_91927 : Nat := 10489496916881570864387

theorem tailTrace_91927 : CollatzResearch.WordTrace tailWord_91927 prefixEnd_91927 10489496916881570864387 := by
  unfold tailWord_91927
  simp only [CollatzResearch.WordTrace]
  refine ⟨3352853137971653726778035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2235235425314435817852023 3352853137971653726778035)
  ·
    refine ⟨5029279706957480590167053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3352853137971653726778035 5029279706957480590167053)
    ·
      refine ⟨1885979890109055221312645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5029279706957480590167053 1885979890109055221312645)
      ·
        refine ⟨353621229395447853996121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1885979890109055221312645 353621229395447853996121)
        ·
          refine ⟨265215922046585890497091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353621229395447853996121 265215922046585890497091)
          ·
            refine ⟨397823883069878835745637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265215922046585890497091 397823883069878835745637)
            ·
              refine ⟨74591978075602281702307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 397823883069878835745637 74591978075602281702307)
              ·
                refine ⟨111887967113403422553461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74591978075602281702307 111887967113403422553461)
                ·
                  refine ⟨10489496916881570864387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111887967113403422553461 10489496916881570864387)
                  ·
                    rfl

theorem cell22_91927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 5].length) (baseStart_91927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91927 prefixEnd_91927 := by exact prefixLift 91927
  have htrace : WordTrace (prefixWord ++ tailWord_91927) baseStart_91927 baseEnd_91927 := by
    simpa [prefixWord, tailWord_91927, baseEnd_91927] using wordTrace_append hprefix tailTrace_91927
  have hstable : (prefixWord ++ tailWord_91927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91927).length < 2 ^ (prefixWord ++ tailWord_91927).sum := by decide
  have hdescent : baseEnd_91927 < baseStart_91927 := by decide
  rcases family_descends (prefixWord ++ tailWord_91927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91968 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 5, 6]
def baseStart_91968 : Nat := 118140960795 + 91968 * 2 ^ 59
def prefixEnd_91968 : Nat := 4983230072969 + 3 ^ 40 * 91968 * 2
def baseEnd_91968 : Nat := 31482525888534272318035

theorem tailTrace_91968 : CollatzResearch.WordTrace tailWord_91968 prefixEnd_91968 31482525888534272318035 := by
  unfold tailWord_91968
  simp only [CollatzResearch.WordTrace]
  refine ⟨1677174265411558864510279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2236232353882078486013705 1677174265411558864510279)
  ·
    refine ⟨2515761398117338296765419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1677174265411558864510279 2515761398117338296765419)
    ·
      refine ⟨3773642097176007445148129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2515761398117338296765419 3773642097176007445148129)
      ·
        refine ⟨2830231572882005583861097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3773642097176007445148129 2830231572882005583861097)
        ·
          refine ⟨2122673679661504187895823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2830231572882005583861097 2122673679661504187895823)
          ·
            refine ⟨3184010519492256281843735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2122673679661504187895823 3184010519492256281843735)
            ·
              refine ⟨4776015779238384422765603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3184010519492256281843735 4776015779238384422765603)
              ·
                refine ⟨7164023668857576634148405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4776015779238384422765603 7164023668857576634148405)
                ·
                  refine ⟨671627218955397809451413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7164023668857576634148405 671627218955397809451413)
                  ·
                    refine ⟨31482525888534272318035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 671627218955397809451413 31482525888534272318035)
                    ·
                      rfl

theorem cell22_91968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_91968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91968 prefixEnd_91968 := by exact prefixLift 91968
  have htrace : WordTrace (prefixWord ++ tailWord_91968) baseStart_91968 baseEnd_91968 := by
    simpa [prefixWord, tailWord_91968, baseEnd_91968] using wordTrace_append hprefix tailTrace_91968
  have hstable : (prefixWord ++ tailWord_91968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91968).length < 2 ^ (prefixWord ++ tailWord_91968).sum := by decide
  have hdescent : baseEnd_91968 < baseStart_91968 := by decide
  rcases family_descends (prefixWord ++ tailWord_91968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91974 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_91974 : Nat := 118140960795 + 91974 * 2 ^ 59
def prefixEnd_91974 : Nat := 4983230072969 + 3 ^ 40 * 91974 * 2
def baseEnd_91974 : Nat := 31484579811152256668017

theorem tailTrace_91974 : CollatzResearch.WordTrace tailWord_91974 prefixEnd_91974 31484579811152256668017 := by
  unfold tailWord_91974
  simp only [CollatzResearch.WordTrace]
  refine ⟨104830230275043148554343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2236378245867587169159317 104830230275043148554343)
  ·
    refine ⟨157245345412564722831515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104830230275043148554343 157245345412564722831515)
    ·
      refine ⟨235868018118847084247273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157245345412564722831515 235868018118847084247273)
      ·
        refine ⟨176901013589135313185455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235868018118847084247273 176901013589135313185455)
        ·
          refine ⟨265351520383702969778183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176901013589135313185455 265351520383702969778183)
          ·
            refine ⟨398027280575554454667275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265351520383702969778183 398027280575554454667275)
            ·
              refine ⟨597040920863331682000913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398027280575554454667275 597040920863331682000913)
              ·
                refine ⟨447780690647498761500685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 597040920863331682000913 447780690647498761500685)
                ·
                  refine ⟨167917758992812035562757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 447780690647498761500685 167917758992812035562757)
                  ·
                    refine ⟨31484579811152256668017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 167917758992812035562757 31484579811152256668017)
                    ·
                      rfl

theorem cell22_91974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_91974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_91974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_91974 prefixEnd_91974 := by exact prefixLift 91974
  have htrace : WordTrace (prefixWord ++ tailWord_91974) baseStart_91974 baseEnd_91974 := by
    simpa [prefixWord, tailWord_91974, baseEnd_91974] using wordTrace_append hprefix tailTrace_91974
  have hstable : (prefixWord ++ tailWord_91974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91974).length < 2 ^ (prefixWord ++ tailWord_91974).sum := by decide
  have hdescent : baseEnd_91974 < baseStart_91974 := by decide
  rcases family_descends (prefixWord ++ tailWord_91974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92002 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_92002 : Nat := 118140960795 + 92002 * 2 ^ 59
def prefixEnd_92002 : Nat := 4983230072969 + 3 ^ 40 * 92002 * 2
def baseEnd_92002 : Nat := 31494164783369516967931

theorem tailTrace_92002 : CollatzResearch.WordTrace tailWord_92002 prefixEnd_92002 31494164783369516967931 := by
  unfold tailWord_92002
  simp only [CollatzResearch.WordTrace]
  refine ⟨838897153174985383939565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2237059075133294357172173 838897153174985383939565)
  ·
    refine ⟨314586432440619518977337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 838897153174985383939565 314586432440619518977337)
    ·
      refine ⟨235939824330464639233003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314586432440619518977337 235939824330464639233003)
      ·
        refine ⟨353909736495696958849505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235939824330464639233003 353909736495696958849505)
        ·
          refine ⟨265432302371772719137129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353909736495696958849505 265432302371772719137129)
          ·
            refine ⟨199074226778829539352847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265432302371772719137129 199074226778829539352847)
            ·
              refine ⟨298611340168244309029271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199074226778829539352847 298611340168244309029271)
              ·
                refine ⟨447917010252366463543907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298611340168244309029271 447917010252366463543907)
                ·
                  refine ⟨671875515378549695315861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 447917010252366463543907 671875515378549695315861)
                  ·
                    refine ⟨31494164783369516967931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 671875515378549695315861 31494164783369516967931)
                    ·
                      rfl

theorem cell22_92002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_92002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92002 prefixEnd_92002 := by exact prefixLift 92002
  have htrace : WordTrace (prefixWord ++ tailWord_92002) baseStart_92002 baseEnd_92002 := by
    simpa [prefixWord, tailWord_92002, baseEnd_92002] using wordTrace_append hprefix tailTrace_92002
  have hstable : (prefixWord ++ tailWord_92002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92002).length < 2 ^ (prefixWord ++ tailWord_92002).sum := by decide
  have hdescent : baseEnd_92002 < baseStart_92002 := by decide
  rcases family_descends (prefixWord ++ tailWord_92002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92032 : List Nat := [2, 1, 1, 2, 1, 2, 6, 1, 3, 3]
def baseStart_92032 : Nat := 118140960795 + 92032 * 2 ^ 59
def prefixEnd_92032 : Nat := 4983230072969 + 3 ^ 40 * 92032 * 2
def baseEnd_92032 : Nat := 31504434396459438717839

theorem tailTrace_92032 : CollatzResearch.WordTrace tailWord_92032 prefixEnd_92032 31504434396459438717839 := by
  unfold tailWord_92032
  simp only [CollatzResearch.WordTrace]
  refine ⟨1678341401295628329675175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2237788535060837772900233 1678341401295628329675175)
  ·
    refine ⟨2517512101943442494512763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1678341401295628329675175 2517512101943442494512763)
    ·
      refine ⟨3776268152915163741769145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2517512101943442494512763 3776268152915163741769145)
      ·
        refine ⟨2832201114686372806326859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3776268152915163741769145 2832201114686372806326859)
        ·
          refine ⟨4248301672029559209490289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2832201114686372806326859 4248301672029559209490289)
          ·
            refine ⟨3186226254022169407117717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4248301672029559209490289 3186226254022169407117717)
            ·
              refine ⟨149354355657289190958643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3186226254022169407117717 149354355657289190958643)
              ·
                refine ⟨224031533485933786437965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149354355657289190958643 224031533485933786437965)
                ·
                  refine ⟨84011825057225169914237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 224031533485933786437965 84011825057225169914237)
                  ·
                    refine ⟨31504434396459438717839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84011825057225169914237 31504434396459438717839)
                    ·
                      rfl

theorem cell22_92032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 3, 3].length) (baseStart_92032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92032 prefixEnd_92032 := by exact prefixLift 92032
  have htrace : WordTrace (prefixWord ++ tailWord_92032) baseStart_92032 baseEnd_92032 := by
    simpa [prefixWord, tailWord_92032, baseEnd_92032] using wordTrace_append hprefix tailTrace_92032
  have hstable : (prefixWord ++ tailWord_92032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92032).length < 2 ^ (prefixWord ++ tailWord_92032).sum := by decide
  have hdescent : baseEnd_92032 < baseStart_92032 := by decide
  rcases family_descends (prefixWord ++ tailWord_92032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92090 : List Nat := [3, 1, 1, 1, 2, 1, 2, 5, 6]
def baseStart_92090 : Nat := 118140960795 + 92090 * 2 ^ 59
def prefixEnd_92090 : Nat := 4983230072969 + 3 ^ 40 * 92090 * 2
def baseEnd_92090 : Nat := 10508096327255540255887

theorem tailTrace_92090 : CollatzResearch.WordTrace tailWord_92090 prefixEnd_92090 10508096327255540255887 := by
  unfold tailWord_92090
  simp only [CollatzResearch.WordTrace]
  refine ⟨839699559095283141240431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2239198824254088376641149 839699559095283141240431)
  ·
    refine ⟨1259549338642924711860647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 839699559095283141240431 1259549338642924711860647)
    ·
      refine ⟨1889324007964387067790971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1259549338642924711860647 1889324007964387067790971)
      ·
        refine ⟨2833986011946580601686457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1889324007964387067790971 2833986011946580601686457)
        ·
          refine ⟨2125489508959935451264843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2833986011946580601686457 2125489508959935451264843)
          ·
            refine ⟨3188234263439903176897265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2125489508959935451264843 3188234263439903176897265)
            ·
              refine ⟨2391175697579927382672949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3188234263439903176897265 2391175697579927382672949)
              ·
                refine ⟨224172721648118192125589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2391175697579927382672949 224172721648118192125589)
                ·
                  refine ⟨10508096327255540255887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 224172721648118192125589 10508096327255540255887)
                  ·
                    rfl

theorem cell22_92090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_92090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92090 prefixEnd_92090 := by exact prefixLift 92090
  have htrace : WordTrace (prefixWord ++ tailWord_92090) baseStart_92090 baseEnd_92090 := by
    simpa [prefixWord, tailWord_92090, baseEnd_92090] using wordTrace_append hprefix tailTrace_92090
  have hstable : (prefixWord ++ tailWord_92090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92090).length < 2 ^ (prefixWord ++ tailWord_92090).sum := by decide
  have hdescent : baseEnd_92090 < baseStart_92090 := by decide
  rcases family_descends (prefixWord ++ tailWord_92090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92135 : List Nat := [1, 1, 5, 2, 13]
def baseStart_92135 : Nat := 118140960795 + 92135 * 2 ^ 59
def prefixEnd_92135 : Nat := 4983230072969 + 3 ^ 40 * 92135 * 2
def baseEnd_92135 : Nat := 129792976960500013961

theorem tailTrace_92135 : CollatzResearch.WordTrace tailWord_92135 prefixEnd_92135 129792976960500013961 := by
  unfold tailWord_92135
  simp only [CollatzResearch.WordTrace]
  refine ⟨3360439521218105250349859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2240293014145403500233239 3360439521218105250349859)
  ·
    refine ⟨5040659281827157875524789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3360439521218105250349859 5040659281827157875524789)
    ·
      refine ⟨472561807671296050830449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5040659281827157875524789 472561807671296050830449)
      ·
        refine ⟨354421355753472038122837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 472561807671296050830449 354421355753472038122837)
        ·
          refine ⟨129792976960500013961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 354421355753472038122837 129792976960500013961)
          ·
            rfl

theorem cell22_92135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 13].length) (baseStart_92135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92135 prefixEnd_92135 := by exact prefixLift 92135
  have htrace : WordTrace (prefixWord ++ tailWord_92135) baseStart_92135 baseEnd_92135 := by
    simpa [prefixWord, tailWord_92135, baseEnd_92135] using wordTrace_append hprefix tailTrace_92135
  have hstable : (prefixWord ++ tailWord_92135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92135).length < 2 ^ (prefixWord ++ tailWord_92135).sum := by decide
  have hdescent : baseEnd_92135 < baseStart_92135 := by decide
  rcases family_descends (prefixWord ++ tailWord_92135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92197 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 7]
def baseStart_92197 : Nat := 118140960795 + 92197 * 2 ^ 59
def prefixEnd_92197 : Nat := 4983230072969 + 3 ^ 40 * 92197 * 2
def baseEnd_92197 : Nat := 10520305756151336114111

theorem tailTrace_92197 : CollatzResearch.WordTrace tailWord_92197 prefixEnd_92197 10520305756151336114111 := by
  unfold tailWord_92197
  simp only [CollatzResearch.WordTrace]
  refine ⟨3362700846993489839106845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2241800564662326559404563 3362700846993489839106845)
  ·
    refine ⟨1261012817622558689665067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3362700846993489839106845 1261012817622558689665067)
    ·
      refine ⟨1891519226433838034497601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1261012817622558689665067 1891519226433838034497601)
      ·
        refine ⟨1418639419825378525873201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1891519226433838034497601 1418639419825378525873201)
        ·
          refine ⟨1063979564869033894404901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1418639419825378525873201 1063979564869033894404901)
          ·
            refine ⟨199496168412943855200919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1063979564869033894404901 199496168412943855200919)
            ·
              refine ⟨299244252619415782801379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199496168412943855200919 299244252619415782801379)
              ·
                refine ⟨448866378929123674202069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299244252619415782801379 448866378929123674202069)
                ·
                  refine ⟨10520305756151336114111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 448866378929123674202069 10520305756151336114111)
                  ·
                    rfl

theorem cell22_92197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_92197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92197 prefixEnd_92197 := by exact prefixLift 92197
  have htrace : WordTrace (prefixWord ++ tailWord_92197) baseStart_92197 baseEnd_92197 := by
    simpa [prefixWord, tailWord_92197, baseEnd_92197] using wordTrace_append hprefix tailTrace_92197
  have hstable : (prefixWord ++ tailWord_92197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92197).length < 2 ^ (prefixWord ++ tailWord_92197).sum := by decide
  have hdescent : baseEnd_92197 < baseStart_92197 := by decide
  rcases family_descends (prefixWord ++ tailWord_92197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92259 : List Nat := [1, 1, 1, 5, 1, 1, 2, 6, 4]
def baseStart_92259 : Nat := 118140960795 + 92259 * 2 ^ 59
def prefixEnd_92259 : Nat := 4983230072969 + 3 ^ 40 * 92259 * 2
def baseEnd_92259 : Nat := 10527380378502171097381

theorem tailTrace_92259 : CollatzResearch.WordTrace tailWord_92259 prefixEnd_92259 10527380378502171097381 := by
  unfold tailWord_92259
  simp only [CollatzResearch.WordTrace]
  refine ⟨3364962172768874427863831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2243308115179249618575887 3364962172768874427863831)
  ·
    refine ⟨5047443259153311641795747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3364962172768874427863831 5047443259153311641795747)
    ·
      refine ⟨7571164888729967462693621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5047443259153311641795747 7571164888729967462693621)
      ·
        refine ⟨709796708318434449627527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7571164888729967462693621 709796708318434449627527)
        ·
          refine ⟨1064695062477651674441291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709796708318434449627527 1064695062477651674441291)
          ·
            refine ⟨1597042593716477511661937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064695062477651674441291 1597042593716477511661937)
            ·
              refine ⟨1197781945287358133746453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1597042593716477511661937 1197781945287358133746453)
              ·
                refine ⟨56146028685344912519365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1197781945287358133746453 56146028685344912519365)
                ·
                  refine ⟨10527380378502171097381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56146028685344912519365 10527380378502171097381)
                  ·
                    rfl

theorem cell22_92259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 4].length) (baseStart_92259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92259 prefixEnd_92259 := by exact prefixLift 92259
  have htrace : WordTrace (prefixWord ++ tailWord_92259) baseStart_92259 baseEnd_92259 := by
    simpa [prefixWord, tailWord_92259, baseEnd_92259] using wordTrace_append hprefix tailTrace_92259
  have hstable : (prefixWord ++ tailWord_92259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92259).length < 2 ^ (prefixWord ++ tailWord_92259).sum := by decide
  have hdescent : baseEnd_92259 < baseStart_92259 := by decide
  rcases family_descends (prefixWord ++ tailWord_92259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92278 : List Nat := [5, 1, 1, 2, 1, 4, 1, 2, 1, 4]
def baseStart_92278 : Nat := 118140960795 + 92278 * 2 ^ 59
def prefixEnd_92278 : Nat := 4983230072969 + 3 ^ 40 * 92278 * 2
def baseEnd_92278 : Nat := 31588645223796797067085

theorem tailTrace_92278 : CollatzResearch.WordTrace tailWord_92278 prefixEnd_92278 31588645223796797067085 := by
  unfold tailWord_92278
  simp only [CollatzResearch.WordTrace]
  refine ⟨210353447481252542050343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2243770106466693781870325 210353447481252542050343)
  ·
    refine ⟨315530171221878813075515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210353447481252542050343 315530171221878813075515)
    ·
      refine ⟨473295256832818219613273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315530171221878813075515 473295256832818219613273)
      ·
        refine ⟨354971442624613664709955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 473295256832818219613273 354971442624613664709955)
        ·
          refine ⟨532457163936920497064933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354971442624613664709955 532457163936920497064933)
          ·
            refine ⟨99835718238172593199675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 532457163936920497064933 99835718238172593199675)
            ·
              refine ⟨149753577357258889799513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99835718238172593199675 149753577357258889799513)
              ·
                refine ⟨112315183017944167349635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149753577357258889799513 112315183017944167349635)
                ·
                  refine ⟨168472774526916251024453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112315183017944167349635 168472774526916251024453)
                  ·
                    refine ⟨31588645223796797067085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 168472774526916251024453 31588645223796797067085)
                    ·
                      rfl

theorem cell22_92278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_92278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92278 prefixEnd_92278 := by exact prefixLift 92278
  have htrace : WordTrace (prefixWord ++ tailWord_92278) baseStart_92278 baseEnd_92278 := by
    simpa [prefixWord, tailWord_92278, baseEnd_92278] using wordTrace_append hprefix tailTrace_92278
  have hstable : (prefixWord ++ tailWord_92278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92278).length < 2 ^ (prefixWord ++ tailWord_92278).sum := by decide
  have hdescent : baseEnd_92278 < baseStart_92278 := by decide
  rcases family_descends (prefixWord ++ tailWord_92278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92340 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_92340 : Nat := 118140960795 + 92340 * 2 ^ 59
def prefixEnd_92340 : Nat := 4983230072969 + 3 ^ 40 * 92340 * 2
def baseEnd_92340 : Nat := 31609869090849302016895

theorem tailTrace_92340 : CollatzResearch.WordTrace tailWord_92340 prefixEnd_92340 31609869090849302016895 := by
  unfold tailWord_92340
  simp only [CollatzResearch.WordTrace]
  refine ⟨1683958242737712630781237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2245277656983616841041649 1683958242737712630781237)
  ·
    refine ⟨157871085256660559135741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1683958242737712630781237 157871085256660559135741)
    ·
      refine ⟨59201656971247709675903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157871085256660559135741 59201656971247709675903)
      ·
        refine ⟨88802485456871564513855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59201656971247709675903 88802485456871564513855)
        ·
          refine ⟨133203728185307346770783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88802485456871564513855 133203728185307346770783)
          ·
            refine ⟨199805592277961020156175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133203728185307346770783 199805592277961020156175)
            ·
              refine ⟨299708388416941530234263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199805592277961020156175 299708388416941530234263)
              ·
                refine ⟨449562582625412295351395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299708388416941530234263 449562582625412295351395)
                ·
                  refine ⟨674343873938118443027093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449562582625412295351395 674343873938118443027093)
                  ·
                    refine ⟨31609869090849302016895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 674343873938118443027093 31609869090849302016895)
                    ·
                      rfl

theorem cell22_92340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_92340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92340 prefixEnd_92340 := by exact prefixLift 92340
  have htrace : WordTrace (prefixWord ++ tailWord_92340) baseStart_92340 baseEnd_92340 := by
    simpa [prefixWord, tailWord_92340, baseEnd_92340] using wordTrace_append hprefix tailTrace_92340
  have hstable : (prefixWord ++ tailWord_92340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92340).length < 2 ^ (prefixWord ++ tailWord_92340).sum := by decide
  have hdescent : baseEnd_92340 < baseStart_92340 := by decide
  rcases family_descends (prefixWord ++ tailWord_92340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92347 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 1, 7]
def baseStart_92347 : Nat := 118140960795 + 92347 * 2 ^ 59
def prefixEnd_92347 : Nat := 4983230072969 + 3 ^ 40 * 92347 * 2
def baseEnd_92347 : Nat := 31612265333903617091873

theorem tailTrace_92347 : CollatzResearch.WordTrace tailWord_92347 prefixEnd_92347 31612265333903617091873 := by
  unfold tailWord_92347
  simp only [CollatzResearch.WordTrace]
  refine ⟨3368171796450065457067295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2245447864300043638044863 3368171796450065457067295)
  ·
    refine ⟨5052257694675098185600943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3368171796450065457067295 5052257694675098185600943)
    ·
      refine ⟨7578386542012647278401415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5052257694675098185600943 7578386542012647278401415)
      ·
        refine ⟨11367579813018970917602123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7578386542012647278401415 11367579813018970917602123)
        ·
          refine ⟨17051369719528456376403185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11367579813018970917602123 17051369719528456376403185)
          ·
            refine ⟨12788527289646342282302389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17051369719528456376403185 12788527289646342282302389)
            ·
              refine ⟨1198924433404344588965849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12788527289646342282302389 1198924433404344588965849)
              ·
                refine ⟨899193325053258441724387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1198924433404344588965849 899193325053258441724387)
                ·
                  refine ⟨1348789987579887662586581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899193325053258441724387 1348789987579887662586581)
                  ·
                    refine ⟨31612265333903617091873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1348789987579887662586581 31612265333903617091873)
                    ·
                      rfl

theorem cell22_92347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 7].length) (baseStart_92347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92347 prefixEnd_92347 := by exact prefixLift 92347
  have htrace : WordTrace (prefixWord ++ tailWord_92347) baseStart_92347 baseEnd_92347 := by
    simpa [prefixWord, tailWord_92347, baseEnd_92347] using wordTrace_append hprefix tailTrace_92347
  have hstable : (prefixWord ++ tailWord_92347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92347).length < 2 ^ (prefixWord ++ tailWord_92347).sum := by decide
  have hdescent : baseEnd_92347 < baseStart_92347 := by decide
  rcases family_descends (prefixWord ++ tailWord_92347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92366 : List Nat := [4, 1, 1, 1, 4, 1, 3, 2, 5]
def baseStart_92366 : Nat := 118140960795 + 92366 * 2 ^ 59
def prefixEnd_92366 : Nat := 4983230072969 + 3 ^ 40 * 92366 * 2
def baseEnd_92366 : Nat := 10539589807397966955605

theorem tailTrace_92366 : CollatzResearch.WordTrace tailWord_92366 prefixEnd_92366 10539589807397966955605 := by
  unfold tailWord_92366
  simp only [CollatzResearch.WordTrace]
  refine ⟨421108097922653962751119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2245909855587487801339301 421108097922653962751119)
  ·
    refine ⟨631662146883980944126679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 421108097922653962751119 631662146883980944126679)
    ·
      refine ⟨947493220325971416190019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 631662146883980944126679 947493220325971416190019)
      ·
        refine ⟨1421239830488957124285029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 947493220325971416190019 1421239830488957124285029)
        ·
          refine ⟨266482468216679460803443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1421239830488957124285029 266482468216679460803443)
          ·
            refine ⟨399723702325019191205165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266482468216679460803443 399723702325019191205165)
            ·
              refine ⟨149896388371882196701937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 399723702325019191205165 149896388371882196701937)
              ·
                refine ⟨112422291278911647526453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149896388371882196701937 112422291278911647526453)
                ·
                  refine ⟨10539589807397966955605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112422291278911647526453 10539589807397966955605)
                  ·
                    rfl

theorem cell22_92366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_92366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92366 prefixEnd_92366 := by exact prefixLift 92366
  have htrace : WordTrace (prefixWord ++ tailWord_92366) baseStart_92366 baseEnd_92366 := by
    simpa [prefixWord, tailWord_92366, baseEnd_92366] using wordTrace_append hprefix tailTrace_92366
  have hstable : (prefixWord ++ tailWord_92366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92366).length < 2 ^ (prefixWord ++ tailWord_92366).sum := by decide
  have hdescent : baseEnd_92366 < baseStart_92366 := by decide
  rcases family_descends (prefixWord ++ tailWord_92366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92381 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 2, 5]
def baseStart_92381 : Nat := 118140960795 + 92381 * 2 ^ 59
def prefixEnd_92381 : Nat := 4983230072969 + 3 ^ 40 * 92381 * 2
def baseEnd_92381 : Nat := 31623904228738861741769

theorem tailTrace_92381 : CollatzResearch.WordTrace tailWord_92381 prefixEnd_92381 31623904228738861741769 := by
  unfold tailWord_92381
  simp only [CollatzResearch.WordTrace]
  refine ⟨3369411878326889263804997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2246274585551259509203331 3369411878326889263804997)
  ·
    refine ⟨631764727186291736963437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3369411878326889263804997 631764727186291736963437)
    ·
      refine ⟨236911772694859401361289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 631764727186291736963437 236911772694859401361289)
      ·
        refine ⟨177683829521144551020967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236911772694859401361289 177683829521144551020967)
        ·
          refine ⟨266525744281716826531451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177683829521144551020967 266525744281716826531451)
          ·
            refine ⟨399788616422575239797177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266525744281716826531451 399788616422575239797177)
            ·
              refine ⟨299841462316931429847883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399788616422575239797177 299841462316931429847883)
              ·
                refine ⟨449762193475397144771825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299841462316931429847883 449762193475397144771825)
                ·
                  refine ⟨337321645106547858578869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 449762193475397144771825 337321645106547858578869)
                  ·
                    refine ⟨31623904228738861741769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 337321645106547858578869 31623904228738861741769)
                    ·
                      rfl

theorem cell22_92381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_92381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92381 prefixEnd_92381 := by exact prefixLift 92381
  have htrace : WordTrace (prefixWord ++ tailWord_92381) baseStart_92381 baseEnd_92381 := by
    simpa [prefixWord, tailWord_92381, baseEnd_92381] using wordTrace_append hprefix tailTrace_92381
  have hstable : (prefixWord ++ tailWord_92381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92381).length < 2 ^ (prefixWord ++ tailWord_92381).sum := by decide
  have hdescent : baseEnd_92381 < baseStart_92381 := by decide
  rcases family_descends (prefixWord ++ tailWord_92381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92394 : List Nat := [3, 1, 3, 1, 1, 2, 1, 4, 6]
def baseStart_92394 : Nat := 118140960795 + 92394 * 2 ^ 59
def prefixEnd_92394 : Nat := 4983230072969 + 3 ^ 40 * 92394 * 2
def baseEnd_92394 : Nat := 10542784798137053722243

theorem tailTrace_92394 : CollatzResearch.WordTrace tailWord_92394 prefixEnd_92394 10542784798137053722243 := by
  unfold tailWord_92394
  simp only [CollatzResearch.WordTrace]
  refine ⟨842471506819948121007059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2246590684853194989352157 842471506819948121007059)
  ·
    refine ⟨1263707260229922181510589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 842471506819948121007059 1263707260229922181510589)
    ·
      refine ⟨473890222586220818066471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1263707260229922181510589 473890222586220818066471)
      ·
        refine ⟨710835333879331227099707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473890222586220818066471 710835333879331227099707)
        ·
          refine ⟨1066253000818996840649561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710835333879331227099707 1066253000818996840649561)
          ·
            refine ⟨799689750614247630487171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1066253000818996840649561 799689750614247630487171)
            ·
              refine ⟨1199534625921371445730757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 799689750614247630487171 1199534625921371445730757)
              ·
                refine ⟨224912742360257146074517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1199534625921371445730757 224912742360257146074517)
                ·
                  refine ⟨10542784798137053722243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 224912742360257146074517 10542784798137053722243)
                  ·
                    rfl

theorem cell22_92394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_92394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92394 prefixEnd_92394 := by exact prefixLift 92394
  have htrace : WordTrace (prefixWord ++ tailWord_92394) baseStart_92394 baseEnd_92394 := by
    simpa [prefixWord, tailWord_92394, baseEnd_92394] using wordTrace_append hprefix tailTrace_92394
  have hstable : (prefixWord ++ tailWord_92394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92394).length < 2 ^ (prefixWord ++ tailWord_92394).sum := by decide
  have hdescent : baseEnd_92394 < baseStart_92394 := by decide
  rcases family_descends (prefixWord ++ tailWord_92394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92396 : List Nat := [2, 2, 1, 1, 2, 3, 4, 2, 1, 4]
def baseStart_92396 : Nat := 118140960795 + 92396 * 2 ^ 59
def prefixEnd_92396 : Nat := 4983230072969 + 3 ^ 40 * 92396 * 2
def baseEnd_92396 : Nat := 31629039035283822616723

theorem tailTrace_92396 : CollatzResearch.WordTrace tailWord_92396 prefixEnd_92396 31629039035283822616723 := by
  unfold tailWord_92396
  simp only [CollatzResearch.WordTrace]
  refine ⟨1684979486636273412800521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2246639315515031217067361 1684979486636273412800521)
  ·
    refine ⟨1263734614977205059600391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1684979486636273412800521 1263734614977205059600391)
    ·
      refine ⟨1895601922465807589400587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1263734614977205059600391 1895601922465807589400587)
      ·
        refine ⟨2843402883698711384100881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1895601922465807589400587 2843402883698711384100881)
        ·
          refine ⟨2132552162774033538075661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2843402883698711384100881 2132552162774033538075661)
          ·
            refine ⟨799707061040262576778373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2132552162774033538075661 799707061040262576778373)
            ·
              refine ⟨149945073945049233145945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 799707061040262576778373 149945073945049233145945)
              ·
                refine ⟨112458805458786924859459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149945073945049233145945 112458805458786924859459)
                ·
                  refine ⟨168688208188180387289189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112458805458786924859459 168688208188180387289189)
                  ·
                    refine ⟨31629039035283822616723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 168688208188180387289189 31629039035283822616723)
                    ·
                      rfl

theorem cell22_92396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_92396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92396 prefixEnd_92396 := by exact prefixLift 92396
  have htrace : WordTrace (prefixWord ++ tailWord_92396) baseStart_92396 baseEnd_92396 := by
    simpa [prefixWord, tailWord_92396, baseEnd_92396] using wordTrace_append hprefix tailTrace_92396
  have hstable : (prefixWord ++ tailWord_92396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92396).length < 2 ^ (prefixWord ++ tailWord_92396).sum := by decide
  have hdescent : baseEnd_92396 < baseStart_92396 := by decide
  rcases family_descends (prefixWord ++ tailWord_92396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92426 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 4, 3]
def baseStart_92426 : Nat := 118140960795 + 92426 * 2 ^ 59
def prefixEnd_92426 : Nat := 4983230072969 + 3 ^ 40 * 92426 * 2
def baseEnd_92426 : Nat := 31639308648373744366631

theorem tailTrace_92426 : CollatzResearch.WordTrace tailWord_92426 prefixEnd_92426 31639308648373744366631 := by
  unfold tailWord_92426
  simp only [CollatzResearch.WordTrace]
  refine ⟨842763290790965487298283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2247368775442574632795421 842763290790965487298283)
  ·
    refine ⟨1264144936186448230947425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 842763290790965487298283 1264144936186448230947425)
    ·
      refine ⟨948108702139836173210569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1264144936186448230947425 948108702139836173210569)
      ·
        refine ⟨711081526604877129907927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 948108702139836173210569 711081526604877129907927)
        ·
          refine ⟨1066622289907315694861891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 711081526604877129907927 1066622289907315694861891)
          ·
            refine ⟨1599933434860973542292837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066622289907315694861891 1599933434860973542292837)
            ·
              refine ⟨299987519036432539179907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1599933434860973542292837 299987519036432539179907)
              ·
                refine ⟨449981278554648808769861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299987519036432539179907 449981278554648808769861)
                ·
                  refine ⟨84371489728996651644349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 449981278554648808769861 84371489728996651644349)
                  ·
                    refine ⟨31639308648373744366631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84371489728996651644349 31639308648373744366631)
                    ·
                      rfl

theorem cell22_92426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_92426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92426 prefixEnd_92426 := by exact prefixLift 92426
  have htrace : WordTrace (prefixWord ++ tailWord_92426) baseStart_92426 baseEnd_92426 := by
    simpa [prefixWord, tailWord_92426, baseEnd_92426] using wordTrace_append hprefix tailTrace_92426
  have hstable : (prefixWord ++ tailWord_92426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92426).length < 2 ^ (prefixWord ++ tailWord_92426).sum := by decide
  have hdescent : baseEnd_92426 < baseStart_92426 := by decide
  rcases family_descends (prefixWord ++ tailWord_92426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92428 : List Nat := [2, 2, 1, 2, 2, 2, 5, 2, 4]
def baseStart_92428 : Nat := 118140960795 + 92428 * 2 ^ 59
def prefixEnd_92428 : Nat := 4983230072969 + 3 ^ 40 * 92428 * 2
def baseEnd_92428 : Nat := 10546664429748801938875

theorem tailTrace_92428 : CollatzResearch.WordTrace tailWord_92428 prefixEnd_92428 10546664429748801938875 := by
  unfold tailWord_92428
  simp only [CollatzResearch.WordTrace]
  refine ⟨1685563054578308145382969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2247417406104410860510625 1685563054578308145382969)
  ·
    refine ⟨1264172290933731109037227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1685563054578308145382969 1264172290933731109037227)
    ·
      refine ⟨1896258436400596663555841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1264172290933731109037227 1896258436400596663555841)
      ·
        refine ⟨1422193827300447497666881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1896258436400596663555841 1422193827300447497666881)
        ·
          refine ⟨1066645370475335623250161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1422193827300447497666881 1066645370475335623250161)
          ·
            refine ⟨799984027856501717437621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1066645370475335623250161 799984027856501717437621)
            ·
              refine ⟨74998502611547036009777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 799984027856501717437621 74998502611547036009777)
              ·
                refine ⟨56248876958660277007333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74998502611547036009777 56248876958660277007333)
                ·
                  refine ⟨10546664429748801938875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56248876958660277007333 10546664429748801938875)
                  ·
                    rfl

theorem cell22_92428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 4].length) (baseStart_92428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92428 prefixEnd_92428 := by exact prefixLift 92428
  have htrace : WordTrace (prefixWord ++ tailWord_92428) baseStart_92428 baseEnd_92428 := by
    simpa [prefixWord, tailWord_92428, baseEnd_92428] using wordTrace_append hprefix tailTrace_92428
  have hstable : (prefixWord ++ tailWord_92428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92428).length < 2 ^ (prefixWord ++ tailWord_92428).sum := by decide
  have hdescent : baseEnd_92428 < baseStart_92428 := by decide
  rcases family_descends (prefixWord ++ tailWord_92428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92439 : List Nat := [1, 1, 3, 4, 1, 2, 1, 9]
def baseStart_92439 : Nat := 118140960795 + 92439 * 2 ^ 59
def prefixEnd_92439 : Nat := 4983230072969 + 3 ^ 40 * 92439 * 2
def baseEnd_92439 : Nat := 3515973201560671532399

theorem tailTrace_92439 : CollatzResearch.WordTrace tailWord_92439 prefixEnd_92439 3515973201560671532399 := by
  unfold tailWord_92439
  simp only [CollatzResearch.WordTrace]
  refine ⟨3371527312116765169416371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2247684874744510112944247 3371527312116765169416371)
  ·
    refine ⟨5057290968175147754124557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3371527312116765169416371 5057290968175147754124557)
    ·
      refine ⟨1896484113065680407796709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5057290968175147754124557 1896484113065680407796709)
      ·
        refine ⟨355590771199815076461883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1896484113065680407796709 355590771199815076461883)
        ·
          refine ⟨533386156799722614692825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355590771199815076461883 533386156799722614692825)
          ·
            refine ⟨400039617599791961019619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 533386156799722614692825 400039617599791961019619)
            ·
              refine ⟨600059426399687941529429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400039617599791961019619 600059426399687941529429)
              ·
                refine ⟨3515973201560671532399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 600059426399687941529429 3515973201560671532399)
                ·
                  rfl

theorem cell22_92439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 9].length) (baseStart_92439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92439 prefixEnd_92439 := by exact prefixLift 92439
  have htrace : WordTrace (prefixWord ++ tailWord_92439) baseStart_92439 baseEnd_92439 := by
    simpa [prefixWord, tailWord_92439, baseEnd_92439] using wordTrace_append hprefix tailTrace_92439
  have hstable : (prefixWord ++ tailWord_92439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92439).length < 2 ^ (prefixWord ++ tailWord_92439).sum := by decide
  have hdescent : baseEnd_92439 < baseStart_92439 := by decide
  rcases family_descends (prefixWord ++ tailWord_92439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92443 : List Nat := [1, 1, 1, 1, 1, 1, 10, 1, 2, 3]
def baseStart_92443 : Nat := 118140960795 + 92443 * 2 ^ 59
def prefixEnd_92443 : Nat := 4983230072969 + 3 ^ 40 * 92443 * 2
def baseEnd_92443 : Nat := 31645128095791366691579

theorem tailTrace_92443 : CollatzResearch.WordTrace tailWord_92443 prefixEnd_92443 31645128095791366691579 := by
  unfold tailWord_92443
  simp only [CollatzResearch.WordTrace]
  refine ⟨3371673204102273852561983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2247782136068182568374655 3371673204102273852561983)
  ·
    refine ⟨5057509806153410778842975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3371673204102273852561983 5057509806153410778842975)
    ·
      refine ⟨7586264709230116168264463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5057509806153410778842975 7586264709230116168264463)
      ·
        refine ⟨11379397063845174252396695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7586264709230116168264463 11379397063845174252396695)
        ·
          refine ⟨17069095595767761378595043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11379397063845174252396695 17069095595767761378595043)
          ·
            refine ⟨25603643393651642067892565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17069095595767761378595043 25603643393651642067892565)
            ·
              refine ⟨75010674004838795120779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 25603643393651642067892565 75010674004838795120779)
              ·
                refine ⟨112516011007258192681169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75010674004838795120779 112516011007258192681169)
                ·
                  refine ⟨84387008255443644510877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112516011007258192681169 84387008255443644510877)
                  ·
                    refine ⟨31645128095791366691579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84387008255443644510877 31645128095791366691579)
                    ·
                      rfl

theorem cell22_92443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 2, 3].length) (baseStart_92443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92443 prefixEnd_92443 := by exact prefixLift 92443
  have htrace : WordTrace (prefixWord ++ tailWord_92443) baseStart_92443 baseEnd_92443 := by
    simpa [prefixWord, tailWord_92443, baseEnd_92443] using wordTrace_append hprefix tailTrace_92443
  have hstable : (prefixWord ++ tailWord_92443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92443).length < 2 ^ (prefixWord ++ tailWord_92443).sum := by decide
  have hdescent : baseEnd_92443 < baseStart_92443 := by decide
  rcases family_descends (prefixWord ++ tailWord_92443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92522 : List Nat := [3, 1, 3, 3, 1, 2, 2, 3, 1, 3]
def baseStart_92522 : Nat := 118140960795 + 92522 * 2 ^ 59
def prefixEnd_92522 : Nat := 4983230072969 + 3 ^ 40 * 92522 * 2
def baseEnd_92522 : Nat := 31672171410261493966337

theorem tailTrace_92522 : CollatzResearch.WordTrace tailWord_92522 prefixEnd_92522 31672171410261493966337 := by
  unfold tailWord_92522
  simp only [CollatzResearch.WordTrace]
  refine ⟨843638642704017586171955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2249703047210713563125213 843638642704017586171955)
  ·
    refine ⟨1265457964056026379257933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 843638642704017586171955 1265457964056026379257933)
    ·
      refine ⟨474546736521009892221725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1265457964056026379257933 474546736521009892221725)
      ·
        refine ⟨177955026195378709583147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 474546736521009892221725 177955026195378709583147)
        ·
          refine ⟨266932539293068064374721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177955026195378709583147 266932539293068064374721)
          ·
            refine ⟨200199404469801048281041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266932539293068064374721 200199404469801048281041)
            ·
              refine ⟨150149553352350786210781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200199404469801048281041 150149553352350786210781)
              ·
                refine ⟨56306082507131544829043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150149553352350786210781 56306082507131544829043)
                ·
                  refine ⟨84459123760697317243565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56306082507131544829043 84459123760697317243565)
                  ·
                    refine ⟨31672171410261493966337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84459123760697317243565 31672171410261493966337)
                    ·
                      rfl

theorem cell22_92522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_92522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92522 prefixEnd_92522 := by exact prefixLift 92522
  have htrace : WordTrace (prefixWord ++ tailWord_92522) baseStart_92522 baseEnd_92522 := by
    simpa [prefixWord, tailWord_92522, baseEnd_92522] using wordTrace_append hprefix tailTrace_92522
  have hstable : (prefixWord ++ tailWord_92522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92522).length < 2 ^ (prefixWord ++ tailWord_92522).sum := by decide
  have hdescent : baseEnd_92522 < baseStart_92522 := by decide
  rcases family_descends (prefixWord ++ tailWord_92522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92529 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 10]
def baseStart_92529 : Nat := 118140960795 + 92529 * 2 ^ 59
def prefixEnd_92529 : Nat := 4983230072969 + 3 ^ 40 * 92529 * 2
def baseEnd_92529 : Nat := 10558189217771936347105

theorem tailTrace_92529 : CollatzResearch.WordTrace tailWord_92529 prefixEnd_92529 10558189217771936347105 := by
  unfold tailWord_92529
  simp only [CollatzResearch.WordTrace]
  refine ⟨3374809881790710540192641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2249873254527140360128427 3374809881790710540192641)
  ·
    refine ⟨2531107411343032905144481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3374809881790710540192641 2531107411343032905144481)
    ·
      refine ⟨1898330558507274678858361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2531107411343032905144481 1898330558507274678858361)
      ·
        refine ⟨1423747918880456009143771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1898330558507274678858361 1423747918880456009143771)
        ·
          refine ⟨2135621878320684013715657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1423747918880456009143771 2135621878320684013715657)
          ·
            refine ⟨1601716408740513010286743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2135621878320684013715657 1601716408740513010286743)
            ·
              refine ⟨2402574613110769515430115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1601716408740513010286743 2402574613110769515430115)
              ·
                refine ⟨3603861919666154273145173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2402574613110769515430115 3603861919666154273145173)
                ·
                  refine ⟨10558189217771936347105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 3603861919666154273145173 10558189217771936347105)
                  ·
                    rfl

theorem cell22_92529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 10].length) (baseStart_92529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92529 prefixEnd_92529 := by exact prefixLift 92529
  have htrace : WordTrace (prefixWord ++ tailWord_92529) baseStart_92529 baseEnd_92529 := by
    simpa [prefixWord, tailWord_92529, baseEnd_92529] using wordTrace_append hprefix tailTrace_92529
  have hstable : (prefixWord ++ tailWord_92529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92529).length < 2 ^ (prefixWord ++ tailWord_92529).sum := by decide
  have hdescent : baseEnd_92529 < baseStart_92529 := by decide
  rcases family_descends (prefixWord ++ tailWord_92529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92531 : List Nat := [1, 1, 1, 2, 2, 1, 2, 7, 1, 4]
def baseStart_92531 : Nat := 118140960795 + 92531 * 2 ^ 59
def prefixEnd_92531 : Nat := 4983230072969 + 3 ^ 40 * 92531 * 2
def baseEnd_92531 : Nat := 31675252294188470491309

theorem tailTrace_92531 : CollatzResearch.WordTrace tailWord_92531 prefixEnd_92531 31675252294188470491309 := by
  unfold tailWord_92531
  simp only [CollatzResearch.WordTrace]
  refine ⟨3374882827783464881765447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2249921885188976587843631 3374882827783464881765447)
  ·
    refine ⟨5062324241675197322648171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3374882827783464881765447 5062324241675197322648171)
    ·
      refine ⟨7593486362512795983972257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5062324241675197322648171 7593486362512795983972257)
      ·
        refine ⟨5695114771884596987979193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7593486362512795983972257 5695114771884596987979193)
        ·
          refine ⟨4271336078913447740984395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5695114771884596987979193 4271336078913447740984395)
          ·
            refine ⟨6407004118370171611476593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4271336078913447740984395 6407004118370171611476593)
            ·
              refine ⟨4805253088777628708607445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6407004118370171611476593 4805253088777628708607445)
              ·
                refine ⟨112623119268225672857987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4805253088777628708607445 112623119268225672857987)
                ·
                  refine ⟨168934678902338509286981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112623119268225672857987 168934678902338509286981)
                  ·
                    refine ⟨31675252294188470491309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 168934678902338509286981 31675252294188470491309)
                    ·
                      rfl

theorem cell22_92531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 4].length) (baseStart_92531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92531 prefixEnd_92531 := by exact prefixLift 92531
  have htrace : WordTrace (prefixWord ++ tailWord_92531) baseStart_92531 baseEnd_92531 := by
    simpa [prefixWord, tailWord_92531, baseEnd_92531] using wordTrace_append hprefix tailTrace_92531
  have hstable : (prefixWord ++ tailWord_92531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92531).length < 2 ^ (prefixWord ++ tailWord_92531).sum := by decide
  have hdescent : baseEnd_92531 < baseStart_92531 := by decide
  rcases family_descends (prefixWord ++ tailWord_92531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92544 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 2, 9]
def baseStart_92544 : Nat := 118140960795 + 92544 * 2 ^ 59
def prefixEnd_92544 : Nat := 4983230072969 + 3 ^ 40 * 92544 * 2
def baseEnd_92544 : Nat := 31679702459860769916269

theorem tailTrace_92544 : CollatzResearch.WordTrace tailWord_92544 prefixEnd_92544 31679702459860769916269 := by
  unfold tailWord_92544
  simp only [CollatzResearch.WordTrace]
  refine ⟨1687678488368184050994343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2250237984490912067992457 1687678488368184050994343)
  ·
    refine ⟨2531517732552276076491515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1687678488368184050994343 2531517732552276076491515)
    ·
      refine ⟨3797276598828414114737273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2531517732552276076491515 3797276598828414114737273)
      ·
        refine ⟨2847957449121310586052955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3797276598828414114737273 2847957449121310586052955)
        ·
          refine ⟨4271936173681965879079433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2847957449121310586052955 4271936173681965879079433)
          ·
            refine ⟨3203952130261474409309575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4271936173681965879079433 3203952130261474409309575)
            ·
              refine ⟨4805928195392211613964363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3203952130261474409309575 4805928195392211613964363)
              ·
                refine ⟨7208892293088317420946545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4805928195392211613964363 7208892293088317420946545)
                ·
                  refine ⟨5406669219816238065709909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7208892293088317420946545 5406669219816238065709909)
                  ·
                    refine ⟨31679702459860769916269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 5406669219816238065709909 31679702459860769916269)
                    ·
                      rfl

theorem cell22_92544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_92544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92544 prefixEnd_92544 := by exact prefixLift 92544
  have htrace : WordTrace (prefixWord ++ tailWord_92544) baseStart_92544 baseEnd_92544 := by
    simpa [prefixWord, tailWord_92544, baseEnd_92544] using wordTrace_append hprefix tailTrace_92544
  have hstable : (prefixWord ++ tailWord_92544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92544).length < 2 ^ (prefixWord ++ tailWord_92544).sum := by decide
  have hdescent : baseEnd_92544 < baseStart_92544 := by decide
  rcases family_descends (prefixWord ++ tailWord_92544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92561 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 8, 3]
def baseStart_92561 : Nat := 118140960795 + 92561 * 2 ^ 59
def prefixEnd_92561 : Nat := 4983230072969 + 3 ^ 40 * 92561 * 2
def baseEnd_92561 : Nat := 31685521907278392241217

theorem tailTrace_92561 : CollatzResearch.WordTrace tailWord_92561 prefixEnd_92561 31685521907278392241217 := by
  unfold tailWord_92561
  simp only [CollatzResearch.WordTrace]
  refine ⟨3375977017674780005357537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2250651345116520003571691 3375977017674780005357537)
  ·
    refine ⟨2531982763256085004018153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3375977017674780005357537 2531982763256085004018153)
    ·
      refine ⟨1898987072442063753013615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2531982763256085004018153 1898987072442063753013615)
      ·
        refine ⟨2848480608663095629520423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1898987072442063753013615 2848480608663095629520423)
        ·
          refine ⟨4272720912994643444280635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2848480608663095629520423 4272720912994643444280635)
          ·
            refine ⟨6409081369491965166420953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4272720912994643444280635 6409081369491965166420953)
            ·
              refine ⟨4806811027118973874815715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6409081369491965166420953 4806811027118973874815715)
              ·
                refine ⟨7210216540678460812223573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4806811027118973874815715 7210216540678460812223573)
                ·
                  refine ⟨84494725086075712643245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7210216540678460812223573 84494725086075712643245)
                  ·
                    refine ⟨31685521907278392241217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84494725086075712643245 31685521907278392241217)
                    ·
                      rfl

theorem cell22_92561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 3].length) (baseStart_92561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92561 prefixEnd_92561 := by exact prefixLift 92561
  have htrace : WordTrace (prefixWord ++ tailWord_92561) baseStart_92561 baseEnd_92561 := by
    simpa [prefixWord, tailWord_92561, baseEnd_92561] using wordTrace_append hprefix tailTrace_92561
  have hstable : (prefixWord ++ tailWord_92561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92561).length < 2 ^ (prefixWord ++ tailWord_92561).sum := by decide
  have hdescent : baseEnd_92561 < baseStart_92561 := by decide
  rcases family_descends (prefixWord ++ tailWord_92561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92576 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 1, 6]
def baseStart_92576 : Nat := 118140960795 + 92576 * 2 ^ 59
def prefixEnd_92576 : Nat := 4983230072969 + 3 ^ 40 * 92576 * 2
def baseEnd_92576 : Nat := 31690656713823353116171

theorem tailTrace_92576 : CollatzResearch.WordTrace tailWord_92576 prefixEnd_92576 31690656713823353116171 := by
  unfold tailWord_92576
  simp only [CollatzResearch.WordTrace]
  refine ⟨1688262056310218783576791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2251016075080291711435721 1688262056310218783576791)
  ·
    refine ⟨2532393084465328175365187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1688262056310218783576791 2532393084465328175365187)
    ·
      refine ⟨3798589626697992263047781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2532393084465328175365187 3798589626697992263047781)
      ·
        refine ⟨712235555005873549321459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3798589626697992263047781 712235555005873549321459)
        ·
          refine ⟨1068353332508810323982189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 712235555005873549321459 1068353332508810323982189)
          ·
            refine ⟨400632499690803871493321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1068353332508810323982189 400632499690803871493321)
            ·
              refine ⟨300474374768102903619991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400632499690803871493321 300474374768102903619991)
              ·
                refine ⟨450711562152154355429987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 300474374768102903619991 450711562152154355429987)
                ·
                  refine ⟨676067343228231533144981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 450711562152154355429987 676067343228231533144981)
                  ·
                    refine ⟨31690656713823353116171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 676067343228231533144981 31690656713823353116171)
                    ·
                      rfl

theorem cell22_92576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 1, 6].length) (baseStart_92576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92576 prefixEnd_92576 := by exact prefixLift 92576
  have htrace : WordTrace (prefixWord ++ tailWord_92576) baseStart_92576 baseEnd_92576 := by
    simpa [prefixWord, tailWord_92576, baseEnd_92576] using wordTrace_append hprefix tailTrace_92576
  have hstable : (prefixWord ++ tailWord_92576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92576).length < 2 ^ (prefixWord ++ tailWord_92576).sum := by decide
  have hdescent : baseEnd_92576 < baseStart_92576 := by decide
  rcases family_descends (prefixWord ++ tailWord_92576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92578 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 6, 3]
def baseStart_92578 : Nat := 118140960795 + 92578 * 2 ^ 59
def prefixEnd_92578 : Nat := 4983230072969 + 3 ^ 40 * 92578 * 2
def baseEnd_92578 : Nat := 31691341354696014566165

theorem tailTrace_92578 : CollatzResearch.WordTrace tailWord_92578 prefixEnd_92578 31691341354696014566165 := by
  unfold tailWord_92578
  simp only [CollatzResearch.WordTrace]
  refine ⟨844149264653297977181597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2251064705742127939150925 844149264653297977181597)
  ·
    refine ⟨316555974244986741443099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 844149264653297977181597 316555974244986741443099)
    ·
      refine ⟨474833961367480112164649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316555974244986741443099 474833961367480112164649)
      ·
        refine ⟨356125471025610084123487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 474833961367480112164649 356125471025610084123487)
        ·
          refine ⟨534188206538415126185231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356125471025610084123487 534188206538415126185231)
          ·
            refine ⟨801282309807622689277847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534188206538415126185231 801282309807622689277847)
            ·
              refine ⟨1201923464711434033916771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 801282309807622689277847 1201923464711434033916771)
              ·
                refine ⟨1802885197067151050875157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1201923464711434033916771 1802885197067151050875157)
                ·
                  refine ⟨84510243612522705509773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1802885197067151050875157 84510243612522705509773)
                  ·
                    refine ⟨31691341354696014566165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84510243612522705509773 31691341354696014566165)
                    ·
                      rfl

theorem cell22_92578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_92578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92578 prefixEnd_92578 := by exact prefixLift 92578
  have htrace : WordTrace (prefixWord ++ tailWord_92578) baseStart_92578 baseEnd_92578 := by
    simpa [prefixWord, tailWord_92578, baseEnd_92578] using wordTrace_append hprefix tailTrace_92578
  have hstable : (prefixWord ++ tailWord_92578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92578).length < 2 ^ (prefixWord ++ tailWord_92578).sum := by decide
  have hdescent : baseEnd_92578 < baseStart_92578 := by decide
  rcases family_descends (prefixWord ++ tailWord_92578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92593 : List Nat := [1, 2, 2, 4, 1, 3, 1, 2, 2, 4]
def baseStart_92593 : Nat := 118140960795 + 92593 * 2 ^ 59
def prefixEnd_92593 : Nat := 4983230072969 + 3 ^ 40 * 92593 * 2
def baseEnd_92593 : Nat := 31696476161240975441119

theorem tailTrace_92593 : CollatzResearch.WordTrace tailWord_92593 prefixEnd_92593 31696476161240975441119 := by
  unfold tailWord_92593
  simp only [CollatzResearch.WordTrace]
  refine ⟨3377144153558849470522433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2251429435705899647014955 3377144153558849470522433)
  ·
    refine ⟨2532858115169137102891825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3377144153558849470522433 2532858115169137102891825)
    ·
      refine ⟨1899643586376852827168869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2532858115169137102891825 1899643586376852827168869)
      ·
        refine ⟨356183172445659905094163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1899643586376852827168869 356183172445659905094163)
        ·
          refine ⟨534274758668489857641245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356183172445659905094163 534274758668489857641245)
          ·
            refine ⟨200353034500683696615467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 534274758668489857641245 200353034500683696615467)
            ·
              refine ⟨300529551751025544923201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200353034500683696615467 300529551751025544923201)
              ·
                refine ⟨225397163813269158692401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 300529551751025544923201 225397163813269158692401)
                ·
                  refine ⟨169047872859951869019301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225397163813269158692401 169047872859951869019301)
                  ·
                    refine ⟨31696476161240975441119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 169047872859951869019301 31696476161240975441119)
                    ·
                      rfl

theorem cell22_92593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_92593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92593 prefixEnd_92593 := by exact prefixLift 92593
  have htrace : WordTrace (prefixWord ++ tailWord_92593) baseStart_92593 baseEnd_92593 := by
    simpa [prefixWord, tailWord_92593, baseEnd_92593] using wordTrace_append hprefix tailTrace_92593
  have hstable : (prefixWord ++ tailWord_92593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92593).length < 2 ^ (prefixWord ++ tailWord_92593).sum := by decide
  have hdescent : baseEnd_92593 < baseStart_92593 := by decide
  rcases family_descends (prefixWord ++ tailWord_92593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92597 : List Nat := [1, 3, 3, 2, 3, 1, 3, 2, 4]
def baseStart_92597 : Nat := 118140960795 + 92597 * 2 ^ 59
def prefixEnd_92597 : Nat := 4983230072969 + 3 ^ 40 * 92597 * 2
def baseEnd_92597 : Nat := 10565948480995432780369

theorem tailTrace_92597 : CollatzResearch.WordTrace tailWord_92597 prefixEnd_92597 10565948480995432780369 := by
  unfold tailWord_92597
  simp only [CollatzResearch.WordTrace]
  refine ⟨3377290045544358153668045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2251526697029572102445363 3377290045544358153668045)
  ·
    refine ⟨1266483767079134307625517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3377290045544358153668045 1266483767079134307625517)
    ·
      refine ⟨474931412654675365359569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1266483767079134307625517 474931412654675365359569)
      ·
        refine ⟨356198559491006524019677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 474931412654675365359569 356198559491006524019677)
        ·
          refine ⟨133574459809127446507379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 356198559491006524019677 133574459809127446507379)
          ·
            refine ⟨200361689713691169761069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133574459809127446507379 200361689713691169761069)
            ·
              refine ⟨75135633642634188660401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200361689713691169761069 75135633642634188660401)
              ·
                refine ⟨56351725231975641495301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75135633642634188660401 56351725231975641495301)
                ·
                  refine ⟨10565948480995432780369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56351725231975641495301 10565948480995432780369)
                  ·
                    rfl

theorem cell22_92597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 4].length) (baseStart_92597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92597 prefixEnd_92597 := by exact prefixLift 92597
  have htrace : WordTrace (prefixWord ++ tailWord_92597) baseStart_92597 baseEnd_92597 := by
    simpa [prefixWord, tailWord_92597, baseEnd_92597] using wordTrace_append hprefix tailTrace_92597
  have hstable : (prefixWord ++ tailWord_92597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92597).length < 2 ^ (prefixWord ++ tailWord_92597).sum := by decide
  have hdescent : baseEnd_92597 < baseStart_92597 := by decide
  rcases family_descends (prefixWord ++ tailWord_92597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92612 : List Nat := [2, 3, 3, 2, 2, 1, 1, 3, 2, 3]
def baseStart_92612 : Nat := 118140960795 + 92612 * 2 ^ 59
def prefixEnd_92612 : Nat := 4983230072969 + 3 ^ 40 * 92612 * 2
def baseEnd_92612 : Nat := 31702980249531259216061

theorem tailTrace_92612 : CollatzResearch.WordTrace tailWord_92612 prefixEnd_92612 31702980249531259216061 := by
  unfold tailWord_92612
  simp only [CollatzResearch.WordTrace]
  refine ⟨1688918570245007857732045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2251891426993343810309393 1688918570245007857732045)
  ·
    refine ⟨633344463841877946649517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1688918570245007857732045 633344463841877946649517)
    ·
      refine ⟨237504173940704229993569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 633344463841877946649517 237504173940704229993569)
      ·
        refine ⟨178128130455528172495177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237504173940704229993569 178128130455528172495177)
        ·
          refine ⟨133596097841646129371383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178128130455528172495177 133596097841646129371383)
          ·
            refine ⟨200394146762469194057075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133596097841646129371383 200394146762469194057075)
            ·
              refine ⟨300591220143703791085613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200394146762469194057075 300591220143703791085613)
              ·
                refine ⟨112721707553888921657105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300591220143703791085613 112721707553888921657105)
                ·
                  refine ⟨84541280665416691242829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112721707553888921657105 84541280665416691242829)
                  ·
                    refine ⟨31702980249531259216061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84541280665416691242829 31702980249531259216061)
                    ·
                      rfl

theorem cell22_92612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_92612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92612 prefixEnd_92612 := by exact prefixLift 92612
  have htrace : WordTrace (prefixWord ++ tailWord_92612) baseStart_92612 baseEnd_92612 := by
    simpa [prefixWord, tailWord_92612, baseEnd_92612] using wordTrace_append hprefix tailTrace_92612
  have hstable : (prefixWord ++ tailWord_92612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92612).length < 2 ^ (prefixWord ++ tailWord_92612).sum := by decide
  have hdescent : baseEnd_92612 < baseStart_92612 := by decide
  rcases family_descends (prefixWord ++ tailWord_92612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92640 : List Nat := [2, 1, 1, 3, 1, 1, 4, 5, 1, 3]
def baseStart_92640 : Nat := 118140960795 + 92640 * 2 ^ 59
def prefixEnd_92640 : Nat := 4983230072969 + 3 ^ 40 * 92640 * 2
def baseEnd_92640 : Nat := 31712565221748519515975

theorem tailTrace_92640 : CollatzResearch.WordTrace tailWord_92640 prefixEnd_92640 31712565221748519515975 := by
  unfold tailWord_92640
  simp only [CollatzResearch.WordTrace]
  refine ⟨1689429192194288248741687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2252572256259050998322249 1689429192194288248741687)
  ·
    refine ⟨2534143788291432373112531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1689429192194288248741687 2534143788291432373112531)
    ·
      refine ⟨3801215682437148559668797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2534143788291432373112531 3801215682437148559668797)
      ·
        refine ⟨1425455880913930709875799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3801215682437148559668797 1425455880913930709875799)
        ·
          refine ⟨2138183821370896064813699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1425455880913930709875799 2138183821370896064813699)
          ·
            refine ⟨3207275732056344097220549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2138183821370896064813699 3207275732056344097220549)
            ·
              refine ⟨601364199760564518228853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3207275732056344097220549 601364199760564518228853)
              ·
                refine ⟨56377893727552923583955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 601364199760564518228853 56377893727552923583955)
                ·
                  refine ⟨84566840591329385375933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56377893727552923583955 84566840591329385375933)
                  ·
                    refine ⟨31712565221748519515975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84566840591329385375933 31712565221748519515975)
                    ·
                      rfl

theorem cell22_92640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 1, 3].length) (baseStart_92640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92640 prefixEnd_92640 := by exact prefixLift 92640
  have htrace : WordTrace (prefixWord ++ tailWord_92640) baseStart_92640 baseEnd_92640 := by
    simpa [prefixWord, tailWord_92640, baseEnd_92640] using wordTrace_append hprefix tailTrace_92640
  have hstable : (prefixWord ++ tailWord_92640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92640).length < 2 ^ (prefixWord ++ tailWord_92640).sum := by decide
  have hdescent : baseEnd_92640 < baseStart_92640 := by decide
  rcases family_descends (prefixWord ++ tailWord_92640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92651 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 2, 5]
def baseStart_92651 : Nat := 118140960795 + 92651 * 2 ^ 59
def prefixEnd_92651 : Nat := 4983230072969 + 3 ^ 40 * 92651 * 2
def baseEnd_92651 : Nat := 31716330746548157490941

theorem tailTrace_92651 : CollatzResearch.WordTrace tailWord_92651 prefixEnd_92651 31716330746548157490941 := by
  unfold tailWord_92651
  simp only [CollatzResearch.WordTrace]
  refine ⟨3379259587348725376133807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2252839724899150250755871 3379259587348725376133807)
  ·
    refine ⟨5068889381023088064200711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3379259587348725376133807 5068889381023088064200711)
    ·
      refine ⟨7603334071534632096301067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5068889381023088064200711 7603334071534632096301067)
      ·
        refine ⟨11405001107301948144451601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7603334071534632096301067 11405001107301948144451601)
        ·
          refine ⟨8553750830476461108338701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11405001107301948144451601 8553750830476461108338701)
          ·
            refine ⟨3207656561428672915627013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8553750830476461108338701 3207656561428672915627013)
            ·
              refine ⟨601435605267876171680065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3207656561428672915627013 601435605267876171680065)
              ·
                refine ⟨451076703950907128760049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601435605267876171680065 451076703950907128760049)
                ·
                  refine ⟨338307527963180346570037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451076703950907128760049 338307527963180346570037)
                  ·
                    refine ⟨31716330746548157490941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 338307527963180346570037 31716330746548157490941)
                    ·
                      rfl

theorem cell22_92651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 5].length) (baseStart_92651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92651 prefixEnd_92651 := by exact prefixLift 92651
  have htrace : WordTrace (prefixWord ++ tailWord_92651) baseStart_92651 baseEnd_92651 := by
    simpa [prefixWord, tailWord_92651, baseEnd_92651] using wordTrace_append hprefix tailTrace_92651
  have hstable : (prefixWord ++ tailWord_92651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92651).length < 2 ^ (prefixWord ++ tailWord_92651).sum := by decide
  have hdescent : baseEnd_92651 < baseStart_92651 := by decide
  rcases family_descends (prefixWord ++ tailWord_92651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92683 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 3, 4]
def baseStart_92683 : Nat := 118140960795 + 92683 * 2 ^ 59
def prefixEnd_92683 : Nat := 4983230072969 + 3 ^ 40 * 92683 * 2
def baseEnd_92683 : Nat := 31727285000510740690843

theorem tailTrace_92683 : CollatzResearch.WordTrace tailWord_92683 prefixEnd_92683 31727285000510740690843 := by
  unfold tailWord_92683
  simp only [CollatzResearch.WordTrace]
  refine ⟨3380426723232794841298703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2253617815488529894199135 3380426723232794841298703)
  ·
    refine ⟨5070640084849192261948055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3380426723232794841298703 5070640084849192261948055)
    ·
      refine ⟨7605960127273788392922083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5070640084849192261948055 7605960127273788392922083)
      ·
        refine ⟨11408940190910682589383125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7605960127273788392922083 11408940190910682589383125)
        ·
          refine ⟨267397035724469123188667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 11408940190910682589383125 267397035724469123188667)
          ·
            refine ⟨401095553586703684783001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267397035724469123188667 401095553586703684783001)
            ·
              refine ⟨300821665190027763587251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401095553586703684783001 300821665190027763587251)
              ·
                refine ⟨451232497785041645380877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 300821665190027763587251 451232497785041645380877)
                ·
                  refine ⟨169212186669390617017829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 451232497785041645380877 169212186669390617017829)
                  ·
                    refine ⟨31727285000510740690843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 169212186669390617017829 31727285000510740690843)
                    ·
                      rfl

theorem cell22_92683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 4].length) (baseStart_92683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92683 prefixEnd_92683 := by exact prefixLift 92683
  have htrace : WordTrace (prefixWord ++ tailWord_92683) baseStart_92683 baseEnd_92683 := by
    simpa [prefixWord, tailWord_92683, baseEnd_92683] using wordTrace_append hprefix tailTrace_92683
  have hstable : (prefixWord ++ tailWord_92683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92683).length < 2 ^ (prefixWord ++ tailWord_92683).sum := by decide
  have hdescent : baseEnd_92683 < baseStart_92683 := by decide
  rcases family_descends (prefixWord ++ tailWord_92683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92700 : List Nat := [2, 2, 3, 1, 2, 3, 1, 3, 1, 4]
def baseStart_92700 : Nat := 118140960795 + 92700 * 2 ^ 59
def prefixEnd_92700 : Nat := 4983230072969 + 3 ^ 40 * 92700 * 2
def baseEnd_92700 : Nat := 31733104447928363015791

theorem tailTrace_92700 : CollatzResearch.WordTrace tailWord_92700 prefixEnd_92700 31733104447928363015791 := by
  unfold tailWord_92700
  simp only [CollatzResearch.WordTrace]
  refine ⟨1690523382085603372333777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2254031176114137829778369 1690523382085603372333777)
  ·
    refine ⟨1267892536564202529250333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1690523382085603372333777 1267892536564202529250333)
    ·
      refine ⟨475459701211575948468875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1267892536564202529250333 475459701211575948468875)
      ·
        refine ⟨713189551817363922703313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475459701211575948468875 713189551817363922703313)
        ·
          refine ⟨534892163863022942027485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 713189551817363922703313 534892163863022942027485)
          ·
            refine ⟨200584561448633603260307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 534892163863022942027485 200584561448633603260307)
            ·
              refine ⟨300876842172950404890461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200584561448633603260307 300876842172950404890461)
              ·
                refine ⟨112828815814856401833923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300876842172950404890461 112828815814856401833923)
                ·
                  refine ⟨169243223722284602750885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112828815814856401833923 169243223722284602750885)
                  ·
                    refine ⟨31733104447928363015791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 169243223722284602750885 31733104447928363015791)
                    ·
                      rfl

theorem cell22_92700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_92700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92700 prefixEnd_92700 := by exact prefixLift 92700
  have htrace : WordTrace (prefixWord ++ tailWord_92700) baseStart_92700 baseEnd_92700 := by
    simpa [prefixWord, tailWord_92700, baseEnd_92700] using wordTrace_append hprefix tailTrace_92700
  have hstable : (prefixWord ++ tailWord_92700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92700).length < 2 ^ (prefixWord ++ tailWord_92700).sum := by decide
  have hdescent : baseEnd_92700 < baseStart_92700 := by decide
  rcases family_descends (prefixWord ++ tailWord_92700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92730 : List Nat := [3, 1, 1, 1, 3, 5, 1, 1, 1, 5]
def baseStart_92730 : Nat := 118140960795 + 92730 * 2 ^ 59
def prefixEnd_92730 : Nat := 4983230072969 + 3 ^ 40 * 92730 * 2
def baseEnd_92730 : Nat := 31743374061018284765699

theorem tailTrace_92730 : CollatzResearch.WordTrace tailWord_92730 prefixEnd_92730 31743374061018284765699 := by
  unfold tailWord_92730
  simp only [CollatzResearch.WordTrace]
  refine ⟨845535238515630467064911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2254760636041681245506429 845535238515630467064911)
  ·
    refine ⟨1268302857773445700597367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 845535238515630467064911 1268302857773445700597367)
    ·
      refine ⟨1902454286660168550896051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1268302857773445700597367 1902454286660168550896051)
      ·
        refine ⟨2853681429990252826344077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1902454286660168550896051 2853681429990252826344077)
        ·
          refine ⟨1070130536246344809879029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2853681429990252826344077 1070130536246344809879029)
          ·
            refine ⟨100324737773094825926159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1070130536246344809879029 100324737773094825926159)
            ·
              refine ⟨150487106659642238889239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100324737773094825926159 150487106659642238889239)
              ·
                refine ⟨225730659989463358333859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150487106659642238889239 225730659989463358333859)
                ·
                  refine ⟨338595989984195037500789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225730659989463358333859 338595989984195037500789)
                  ·
                    refine ⟨31743374061018284765699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 338595989984195037500789 31743374061018284765699)
                    ·
                      rfl

theorem cell22_92730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 1, 5].length) (baseStart_92730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92730 prefixEnd_92730 := by exact prefixLift 92730
  have htrace : WordTrace (prefixWord ++ tailWord_92730) baseStart_92730 baseEnd_92730 := by
    simpa [prefixWord, tailWord_92730, baseEnd_92730] using wordTrace_append hprefix tailTrace_92730
  have hstable : (prefixWord ++ tailWord_92730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92730).length < 2 ^ (prefixWord ++ tailWord_92730).sum := by decide
  have hdescent : baseEnd_92730 < baseStart_92730 := by decide
  rcases family_descends (prefixWord ++ tailWord_92730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92734 : List Nat := [4, 2, 1, 4, 1, 1, 2, 2, 1, 4]
def baseStart_92734 : Nat := 118140960795 + 92734 * 2 ^ 59
def prefixEnd_92734 : Nat := 4983230072969 + 3 ^ 40 * 92734 * 2
def baseEnd_92734 : Nat := 31744743342763607665687

theorem tailTrace_92734 : CollatzResearch.WordTrace tailWord_92734 prefixEnd_92734 31744743342763607665687 := by
  unfold tailWord_92734
  simp only [CollatzResearch.WordTrace]
  refine ⟨422785855756003818925657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2254857897365353700936837 422785855756003818925657)
  ·
    refine ⟨317089391817002864194243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 422785855756003818925657 317089391817002864194243)
    ·
      refine ⟨475634087725504296291365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317089391817002864194243 475634087725504296291365)
      ·
        refine ⟨89181391448532055554631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 475634087725504296291365 89181391448532055554631)
        ·
          refine ⟨133772087172798083331947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89181391448532055554631 133772087172798083331947)
          ·
            refine ⟨200658130759197124997921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133772087172798083331947 200658130759197124997921)
            ·
              refine ⟨150493598069397843748441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200658130759197124997921 150493598069397843748441)
              ·
                refine ⟨112870198552048382811331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150493598069397843748441 112870198552048382811331)
                ·
                  refine ⟨169305297828072574216997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112870198552048382811331 169305297828072574216997)
                  ·
                    refine ⟨31744743342763607665687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 169305297828072574216997 31744743342763607665687)
                    ·
                      rfl

theorem cell22_92734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_92734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92734 prefixEnd_92734 := by exact prefixLift 92734
  have htrace : WordTrace (prefixWord ++ tailWord_92734) baseStart_92734 baseEnd_92734 := by
    simpa [prefixWord, tailWord_92734, baseEnd_92734] using wordTrace_append hprefix tailTrace_92734
  have hstable : (prefixWord ++ tailWord_92734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92734).length < 2 ^ (prefixWord ++ tailWord_92734).sum := by decide
  have hdescent : baseEnd_92734 < baseStart_92734 := by decide
  rcases family_descends (prefixWord ++ tailWord_92734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92743 : List Nat := [1, 1, 4, 1, 4, 2, 1, 8]
def baseStart_92743 : Nat := 118140960795 + 92743 * 2 ^ 59
def prefixEnd_92743 : Nat := 4983230072969 + 3 ^ 40 * 92743 * 2
def baseEnd_92743 : Nat := 3527536025187842687851

theorem tailTrace_92743 : CollatzResearch.WordTrace tailWord_92743 prefixEnd_92743 3527536025187842687851 := by
  unfold tailWord_92743
  simp only [CollatzResearch.WordTrace]
  refine ⟨3382615103015425088482883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2255076735343616725655255 3382615103015425088482883)
  ·
    refine ⟨5073922654523137632724325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3382615103015425088482883 5073922654523137632724325)
    ·
      refine ⟨951360497723088306135811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5073922654523137632724325 951360497723088306135811)
      ·
        refine ⟨1427040746584632459203717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 951360497723088306135811 1427040746584632459203717)
        ·
          refine ⟨267570139984618586100697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1427040746584632459203717 267570139984618586100697)
          ·
            refine ⟨200677604988463939575523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267570139984618586100697 200677604988463939575523)
            ·
              refine ⟨301016407482695909363285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200677604988463939575523 301016407482695909363285)
              ·
                refine ⟨3527536025187842687851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 301016407482695909363285 3527536025187842687851)
                ·
                  rfl

theorem cell22_92743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 8].length) (baseStart_92743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92743 prefixEnd_92743 := by exact prefixLift 92743
  have htrace : WordTrace (prefixWord ++ tailWord_92743) baseStart_92743 baseEnd_92743 := by
    simpa [prefixWord, tailWord_92743, baseEnd_92743] using wordTrace_append hprefix tailTrace_92743
  have hstable : (prefixWord ++ tailWord_92743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92743).length < 2 ^ (prefixWord ++ tailWord_92743).sum := by decide
  have hdescent : baseEnd_92743 < baseStart_92743 := by decide
  rcases family_descends (prefixWord ++ tailWord_92743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92749 : List Nat := [1, 6, 1, 1, 2, 3, 1, 3, 4]
def baseStart_92749 : Nat := 118140960795 + 92749 * 2 ^ 59
def prefixEnd_92749 : Nat := 4983230072969 + 3 ^ 40 * 92749 * 2
def baseEnd_92749 : Nat := 10583292716436189513547

theorem tailTrace_92749 : CollatzResearch.WordTrace tailWord_92749 prefixEnd_92749 10583292716436189513547 := by
  unfold tailWord_92749
  simp only [CollatzResearch.WordTrace]
  refine ⟨3382833940993688113201301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2255222627329125408800867 3382833940993688113201301)
  ·
    refine ⟨158570340984079130306311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3382833940993688113201301 158570340984079130306311)
    ·
      refine ⟨237855511476118695459467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158570340984079130306311 237855511476118695459467)
      ·
        refine ⟨356783267214178043189201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237855511476118695459467 356783267214178043189201)
        ·
          refine ⟨267587450410633532391901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356783267214178043189201 267587450410633532391901)
          ·
            refine ⟨100345293903987574646963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 267587450410633532391901 100345293903987574646963)
            ·
              refine ⟨150517940855981361970445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100345293903987574646963 150517940855981361970445)
              ·
                refine ⟨56444227820993010738917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150517940855981361970445 56444227820993010738917)
                ·
                  refine ⟨10583292716436189513547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56444227820993010738917 10583292716436189513547)
                  ·
                    rfl

theorem cell22_92749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_92749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92749 prefixEnd_92749 := by exact prefixLift 92749
  have htrace : WordTrace (prefixWord ++ tailWord_92749) baseStart_92749 baseEnd_92749 := by
    simpa [prefixWord, tailWord_92749, baseEnd_92749] using wordTrace_append hprefix tailTrace_92749
  have hstable : (prefixWord ++ tailWord_92749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92749).length < 2 ^ (prefixWord ++ tailWord_92749).sum := by decide
  have hdescent : baseEnd_92749 < baseStart_92749 := by decide
  rcases family_descends (prefixWord ++ tailWord_92749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92766 : List Nat := [4, 4, 1, 2, 1, 2, 1, 1, 6]
def baseStart_92766 : Nat := 118140960795 + 92766 * 2 ^ 59
def prefixEnd_92766 : Nat := 4983230072969 + 3 ^ 40 * 92766 * 2
def baseEnd_92766 : Nat := 10585232532242063621863

theorem tailTrace_92766 : CollatzResearch.WordTrace tailWord_92766 prefixEnd_92766 10585232532242063621863 := by
  unfold tailWord_92766
  simp only [CollatzResearch.WordTrace]
  refine ⟨422931747741512502071269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2255635987954733344380101 422931747741512502071269)
  ·
    refine ⟨79299702701533594138363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 422931747741512502071269 79299702701533594138363)
    ·
      refine ⟨118949554052300391207545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79299702701533594138363 118949554052300391207545)
      ·
        refine ⟨89212165539225293405659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118949554052300391207545 89212165539225293405659)
        ·
          refine ⟨133818248308837940108489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89212165539225293405659 133818248308837940108489)
          ·
            refine ⟨100363686231628455081367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133818248308837940108489 100363686231628455081367)
            ·
              refine ⟨150545529347442682622051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100363686231628455081367 150545529347442682622051)
              ·
                refine ⟨225818294021164023933077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150545529347442682622051 225818294021164023933077)
                ·
                  refine ⟨10585232532242063621863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 225818294021164023933077 10585232532242063621863)
                  ·
                    rfl

theorem cell22_92766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_92766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92766 prefixEnd_92766 := by exact prefixLift 92766
  have htrace : WordTrace (prefixWord ++ tailWord_92766) baseStart_92766 baseEnd_92766 := by
    simpa [prefixWord, tailWord_92766, baseEnd_92766] using wordTrace_append hprefix tailTrace_92766
  have hstable : (prefixWord ++ tailWord_92766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92766).length < 2 ^ (prefixWord ++ tailWord_92766).sum := by decide
  have hdescent : baseEnd_92766 < baseStart_92766 := by decide
  rcases family_descends (prefixWord ++ tailWord_92766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92826 : List Nat := [3, 1, 1, 6, 1, 1, 1, 4, 1, 3]
def baseStart_92826 : Nat := 118140960795 + 92826 * 2 ^ 59
def prefixEnd_92826 : Nat := 4983230072969 + 3 ^ 40 * 92826 * 2
def baseEnd_92826 : Nat := 31776236822906034365405

theorem tailTrace_92826 : CollatzResearch.WordTrace tailWord_92826 prefixEnd_92826 31776236822906034365405 := by
  unfold tailWord_92826
  simp only [CollatzResearch.WordTrace]
  refine ⟨846410590428682565938583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2257094907809820175836221 846410590428682565938583)
  ·
    refine ⟨1269615885643023848907875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 846410590428682565938583 1269615885643023848907875)
    ·
      refine ⟨1904423828464535773361813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1269615885643023848907875 1904423828464535773361813)
      ·
        refine ⟨89269866959275114376335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1904423828464535773361813 89269866959275114376335)
        ·
          refine ⟨133904800438912671564503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89269866959275114376335 133904800438912671564503)
          ·
            refine ⟨200857200658369007346755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133904800438912671564503 200857200658369007346755)
            ·
              refine ⟨301285800987553511020133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200857200658369007346755 301285800987553511020133)
              ·
                refine ⟨56491087685166283316275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 301285800987553511020133 56491087685166283316275)
                ·
                  refine ⟨84736631527749424974413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56491087685166283316275 84736631527749424974413)
                  ·
                    refine ⟨31776236822906034365405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84736631527749424974413 31776236822906034365405)
                    ·
                      rfl

theorem cell22_92826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 1, 3].length) (baseStart_92826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92826 prefixEnd_92826 := by exact prefixLift 92826
  have htrace : WordTrace (prefixWord ++ tailWord_92826) baseStart_92826 baseEnd_92826 := by
    simpa [prefixWord, tailWord_92826, baseEnd_92826] using wordTrace_append hprefix tailTrace_92826
  have hstable : (prefixWord ++ tailWord_92826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92826).length < 2 ^ (prefixWord ++ tailWord_92826).sum := by decide
  have hdescent : baseEnd_92826 < baseStart_92826 := by decide
  rcases family_descends (prefixWord ++ tailWord_92826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92940 : List Nat := [2, 2, 1, 2, 2, 1, 1, 6, 5]
def baseStart_92940 : Nat := 118140960795 + 92940 * 2 ^ 59
def prefixEnd_92940 : Nat := 4983230072969 + 3 ^ 40 * 92940 * 2
def baseEnd_92940 : Nat := 10605087117549245671685

theorem tailTrace_92940 : CollatzResearch.WordTrace tailWord_92940 prefixEnd_92940 10605087117549245671685 := by
  unfold tailWord_92940
  simp only [CollatzResearch.WordTrace]
  refine ⟨1694900141650863866702137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2259866855534485155602849 1694900141650863866702137)
  ·
    refine ⟨1271175106238147900026603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1694900141650863866702137 1271175106238147900026603)
    ·
      refine ⟨1906762659357221850039905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1271175106238147900026603 1906762659357221850039905)
      ·
        refine ⟨1430071994517916387529929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1906762659357221850039905 1430071994517916387529929)
        ·
          refine ⟨1072553995888437290647447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1430071994517916387529929 1072553995888437290647447)
          ·
            refine ⟨1608830993832655935971171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1072553995888437290647447 1608830993832655935971171)
            ·
              refine ⟨2413246490748983903956757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1608830993832655935971171 2413246490748983903956757)
              ·
                refine ⟨113120929253858620497973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2413246490748983903956757 113120929253858620497973)
                ·
                  refine ⟨10605087117549245671685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113120929253858620497973 10605087117549245671685)
                  ·
                    rfl

theorem cell22_92940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_92940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_92940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_92940 prefixEnd_92940 := by exact prefixLift 92940
  have htrace : WordTrace (prefixWord ++ tailWord_92940) baseStart_92940 baseEnd_92940 := by
    simpa [prefixWord, tailWord_92940, baseEnd_92940] using wordTrace_append hprefix tailTrace_92940
  have hstable : (prefixWord ++ tailWord_92940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92940).length < 2 ^ (prefixWord ++ tailWord_92940).sum := by decide
  have hdescent : baseEnd_92940 < baseStart_92940 := by decide
  rcases family_descends (prefixWord ++ tailWord_92940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93000 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 3, 5]
def baseStart_93000 : Nat := 118140960795 + 93000 * 2 ^ 59
def prefixEnd_93000 : Nat := 4983230072969 + 3 ^ 40 * 93000 * 2
def baseEnd_93000 : Nat := 31835800578827580514871

theorem tailTrace_93000 : CollatzResearch.WordTrace tailWord_93000 prefixEnd_93000 31835800578827580514871 := by
  unfold tailWord_93000
  simp only [CollatzResearch.WordTrace]
  refine ⟨1695994331542178990294227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2261325775389571987058969 1695994331542178990294227)
  ·
    refine ⟨2543991497313268485441341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1695994331542178990294227 2543991497313268485441341)
    ·
      refine ⟨953996811492475682040503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2543991497313268485441341 953996811492475682040503)
      ·
        refine ⟨1430995217238713523060755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 953996811492475682040503 1430995217238713523060755)
        ·
          refine ⟨2146492825858070284591133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1430995217238713523060755 2146492825858070284591133)
          ·
            refine ⟨804934809696776356721675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2146492825858070284591133 804934809696776356721675)
            ·
              refine ⟨1207402214545164535082513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804934809696776356721675 1207402214545164535082513)
              ·
                refine ⟨905551660908873401311885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1207402214545164535082513 905551660908873401311885)
                ·
                  refine ⟨339581872840827525491957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 905551660908873401311885 339581872840827525491957)
                  ·
                    refine ⟨31835800578827580514871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 339581872840827525491957 31835800578827580514871)
                    ·
                      rfl

theorem cell22_93000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_93000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93000 prefixEnd_93000 := by exact prefixLift 93000
  have htrace : WordTrace (prefixWord ++ tailWord_93000) baseStart_93000 baseEnd_93000 := by
    simpa [prefixWord, tailWord_93000, baseEnd_93000] using wordTrace_append hprefix tailTrace_93000
  have hstable : (prefixWord ++ tailWord_93000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93000).length < 2 ^ (prefixWord ++ tailWord_93000).sum := by decide
  have hdescent : baseEnd_93000 < baseStart_93000 := by decide
  rcases family_descends (prefixWord ++ tailWord_93000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93017 : List Nat := [1, 2, 1, 2, 2, 5, 2, 1, 1, 5]
def baseStart_93017 : Nat := 118140960795 + 93017 * 2 ^ 59
def prefixEnd_93017 : Nat := 4983230072969 + 3 ^ 40 * 93017 * 2
def baseEnd_93017 : Nat := 31841620026245202839819

theorem tailTrace_93017 : CollatzResearch.WordTrace tailWord_93017 prefixEnd_93017 31841620026245202839819 := by
  unfold tailWord_93017
  simp only [CollatzResearch.WordTrace]
  refine ⟨3392608704022769883957305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2261739136015179922638203 3392608704022769883957305)
  ·
    refine ⟨2544456528017077412967979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3392608704022769883957305 2544456528017077412967979)
    ·
      refine ⟨3816684792025616119451969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2544456528017077412967979 3816684792025616119451969)
      ·
        refine ⟨2862513594019212089588977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3816684792025616119451969 2862513594019212089588977)
        ·
          refine ⟨2146885195514409067191733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2862513594019212089588977 2146885195514409067191733)
          ·
            refine ⟨201270487079475850049225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2146885195514409067191733 201270487079475850049225)
            ·
              refine ⟨150952865309606887536919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201270487079475850049225 150952865309606887536919)
              ·
                refine ⟨226429297964410331305379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150952865309606887536919 226429297964410331305379)
                ·
                  refine ⟨339643946946615496958069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 226429297964410331305379 339643946946615496958069)
                  ·
                    refine ⟨31841620026245202839819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 339643946946615496958069 31841620026245202839819)
                    ·
                      rfl

theorem cell22_93017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 5].length) (baseStart_93017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93017 prefixEnd_93017 := by exact prefixLift 93017
  have htrace : WordTrace (prefixWord ++ tailWord_93017) baseStart_93017 baseEnd_93017 := by
    simpa [prefixWord, tailWord_93017, baseEnd_93017] using wordTrace_append hprefix tailTrace_93017
  have hstable : (prefixWord ++ tailWord_93017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93017).length < 2 ^ (prefixWord ++ tailWord_93017).sum := by decide
  have hdescent : baseEnd_93017 < baseStart_93017 := by decide
  rcases family_descends (prefixWord ++ tailWord_93017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93032 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 1, 6]
def baseStart_93032 : Nat := 118140960795 + 93032 * 2 ^ 59
def prefixEnd_93032 : Nat := 4983230072969 + 3 ^ 40 * 93032 * 2
def baseEnd_93032 : Nat := 31846754832790163714773

theorem tailTrace_93032 : CollatzResearch.WordTrace tailWord_93032 prefixEnd_93032 31846754832790163714773 := by
  unfold tailWord_93032
  simp only [CollatzResearch.WordTrace]
  refine ⟨1696577899484213722876675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2262103865978951630502233 1696577899484213722876675)
  ·
    refine ⟨2544866849226320584315013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1696577899484213722876675 2544866849226320584315013)
    ·
      refine ⟨477162534229935109559065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2544866849226320584315013 477162534229935109559065)
      ·
        refine ⟨357871900672451332169299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477162534229935109559065 357871900672451332169299)
        ·
          refine ⟨536807851008676998253949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357871900672451332169299 536807851008676998253949)
          ·
            refine ⟨201302944128253874345231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 536807851008676998253949 201302944128253874345231)
            ·
              refine ⟨301954416192380811517847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201302944128253874345231 301954416192380811517847)
              ·
                refine ⟨452931624288571217276771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301954416192380811517847 452931624288571217276771)
                ·
                  refine ⟨679397436432856825915157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 452931624288571217276771 679397436432856825915157)
                  ·
                    refine ⟨31846754832790163714773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 679397436432856825915157 31846754832790163714773)
                    ·
                      rfl

theorem cell22_93032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_93032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93032 prefixEnd_93032 := by exact prefixLift 93032
  have htrace : WordTrace (prefixWord ++ tailWord_93032) baseStart_93032 baseEnd_93032 := by
    simpa [prefixWord, tailWord_93032, baseEnd_93032] using wordTrace_append hprefix tailTrace_93032
  have hstable : (prefixWord ++ tailWord_93032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93032).length < 2 ^ (prefixWord ++ tailWord_93032).sum := by decide
  have hdescent : baseEnd_93032 < baseStart_93032 := by decide
  rcases family_descends (prefixWord ++ tailWord_93032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93038 : List Nat := [4, 1, 2, 3, 2, 2, 2, 1, 1, 4]
def baseStart_93038 : Nat := 118140960795 + 93038 * 2 ^ 59
def prefixEnd_93038 : Nat := 4983230072969 + 3 ^ 40 * 93038 * 2
def baseEnd_93038 : Nat := 31848808755408148064755

theorem tailTrace_93038 : CollatzResearch.WordTrace tailWord_93038 prefixEnd_93038 31848808755408148064755 := by
  unfold tailWord_93038
  simp only [CollatzResearch.WordTrace]
  refine ⟨424171829618336308808971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2262249757964460313647845 424171829618336308808971)
  ·
    refine ⟨636257744427504463213457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 424171829618336308808971 636257744427504463213457)
    ·
      refine ⟨477193308320628347410093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 636257744427504463213457 477193308320628347410093)
      ·
        refine ⟨178947490620235630278785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 477193308320628347410093 178947490620235630278785)
        ·
          refine ⟨134210617965176722709089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178947490620235630278785 134210617965176722709089)
          ·
            refine ⟨100657963473882542031817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134210617965176722709089 100657963473882542031817)
            ·
              refine ⟨75493472605411906523863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100657963473882542031817 75493472605411906523863)
              ·
                refine ⟨113240208908117859785795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75493472605411906523863 113240208908117859785795)
                ·
                  refine ⟨169860313362176789678693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113240208908117859785795 169860313362176789678693)
                  ·
                    refine ⟨31848808755408148064755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 169860313362176789678693 31848808755408148064755)
                    ·
                      rfl

theorem cell22_93038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_93038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93038 prefixEnd_93038 := by exact prefixLift 93038
  have htrace : WordTrace (prefixWord ++ tailWord_93038) baseStart_93038 baseEnd_93038 := by
    simpa [prefixWord, tailWord_93038, baseEnd_93038] using wordTrace_append hprefix tailTrace_93038
  have hstable : (prefixWord ++ tailWord_93038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93038).length < 2 ^ (prefixWord ++ tailWord_93038).sum := by decide
  have hdescent : baseEnd_93038 < baseStart_93038 := by decide
  rcases family_descends (prefixWord ++ tailWord_93038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93113 : List Nat := [1, 2, 1, 4, 2, 3, 3, 2, 1, 3]
def baseStart_93113 : Nat := 118140960795 + 93113 * 2 ^ 59
def prefixEnd_93113 : Nat := 4983230072969 + 3 ^ 40 * 93113 * 2
def baseEnd_93113 : Nat := 31874482788132952439525

theorem tailTrace_93113 : CollatzResearch.WordTrace tailWord_93113 prefixEnd_93113 31874482788132952439525 := by
  unfold tailWord_93113
  simp only [CollatzResearch.WordTrace]
  refine ⟨3396110111674978279451993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2264073407783318852967995 3396110111674978279451993)
  ·
    refine ⟨2547082583756233709588995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3396110111674978279451993 2547082583756233709588995)
    ·
      refine ⟨3820623875634350564383493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2547082583756233709588995 3820623875634350564383493)
      ·
        refine ⟨716366976681440730821905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3820623875634350564383493 716366976681440730821905)
        ·
          refine ⟨537275232511080548116429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 716366976681440730821905 537275232511080548116429)
          ·
            refine ⟨201478212191655205543661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 537275232511080548116429 201478212191655205543661)
            ·
              refine ⟨75554329571870702078873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201478212191655205543661 75554329571870702078873)
              ·
                refine ⟨56665747178903026559155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75554329571870702078873 56665747178903026559155)
                ·
                  refine ⟨84998620768354539838733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56665747178903026559155 84998620768354539838733)
                  ·
                    refine ⟨31874482788132952439525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84998620768354539838733 31874482788132952439525)
                    ·
                      rfl

theorem cell22_93113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 1, 3].length) (baseStart_93113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93113 prefixEnd_93113 := by exact prefixLift 93113
  have htrace : WordTrace (prefixWord ++ tailWord_93113) baseStart_93113 baseEnd_93113 := by
    simpa [prefixWord, tailWord_93113, baseEnd_93113] using wordTrace_append hprefix tailTrace_93113
  have hstable : (prefixWord ++ tailWord_93113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93113).length < 2 ^ (prefixWord ++ tailWord_93113).sum := by decide
  have hdescent : baseEnd_93113 < baseStart_93113 := by decide
  rcases family_descends (prefixWord ++ tailWord_93113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93227 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 7]
def baseStart_93227 : Nat := 118140960795 + 93227 * 2 ^ 59
def prefixEnd_93227 : Nat := 4983230072969 + 3 ^ 40 * 93227 * 2
def baseEnd_93227 : Nat := 10637835772624885029725

theorem tailTrace_93227 : CollatzResearch.WordTrace tailWord_93227 prefixEnd_93227 10637835772624885029725 := by
  unfold tailWord_93227
  simp only [CollatzResearch.WordTrace]
  refine ⟨3400268033261975749101935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2266845355507983832734623 3400268033261975749101935)
  ·
    refine ⟨5100402049892963623652903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3400268033261975749101935 5100402049892963623652903)
    ·
      refine ⟨7650603074839445435479355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5100402049892963623652903 7650603074839445435479355)
      ·
        refine ⟨11475904612259168153219033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7650603074839445435479355 11475904612259168153219033)
        ·
          refine ⟨8606928459194376114914275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11475904612259168153219033 8606928459194376114914275)
          ·
            refine ⟨12910392688791564172371413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8606928459194376114914275 12910392688791564172371413)
            ·
              refine ⟨302587328643552285289955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12910392688791564172371413 302587328643552285289955)
              ·
                refine ⟨453880992965328427934933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302587328643552285289955 453880992965328427934933)
                ·
                  refine ⟨10637835772624885029725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 453880992965328427934933 10637835772624885029725)
                  ·
                    rfl

theorem cell22_93227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 7].length) (baseStart_93227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93227 prefixEnd_93227 := by exact prefixLift 93227
  have htrace : WordTrace (prefixWord ++ tailWord_93227) baseStart_93227 baseEnd_93227 := by
    simpa [prefixWord, tailWord_93227, baseEnd_93227] using wordTrace_append hprefix tailTrace_93227
  have hstable : (prefixWord ++ tailWord_93227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93227).length < 2 ^ (prefixWord ++ tailWord_93227).sum := by decide
  have hdescent : baseEnd_93227 < baseStart_93227 := by decide
  rcases family_descends (prefixWord ++ tailWord_93227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93278 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 7]
def baseStart_93278 : Nat := 118140960795 + 93278 * 2 ^ 59
def prefixEnd_93278 : Nat := 4983230072969 + 3 ^ 40 * 93278 * 2
def baseEnd_93278 : Nat := 10643655220042507354673

theorem tailTrace_93278 : CollatzResearch.WordTrace tailWord_93278 prefixEnd_93278 10643655220042507354673 := by
  unfold tailWord_93278
  simp only [CollatzResearch.WordTrace]
  refine ⟨425266019509651432401061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2268085437384807639472325 425266019509651432401061)
  ·
    refine ⟨79737378658059643575199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 425266019509651432401061 79737378658059643575199)
    ·
      refine ⟨119606067987089465362799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79737378658059643575199 119606067987089465362799)
      ·
        refine ⟨179409101980634198044199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119606067987089465362799 179409101980634198044199)
        ·
          refine ⟨269113652970951297066299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179409101980634198044199 269113652970951297066299)
          ·
            refine ⟨403670479456426945599449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269113652970951297066299 403670479456426945599449)
            ·
              refine ⟨302752859592320209199587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 403670479456426945599449 302752859592320209199587)
              ·
                refine ⟨454129289388480313799381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302752859592320209199587 454129289388480313799381)
                ·
                  refine ⟨10643655220042507354673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 454129289388480313799381 10643655220042507354673)
                  ·
                    rfl

theorem cell22_93278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_93278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93278 prefixEnd_93278 := by exact prefixLift 93278
  have htrace : WordTrace (prefixWord ++ tailWord_93278) baseStart_93278 baseEnd_93278 := by
    simpa [prefixWord, tailWord_93278, baseEnd_93278] using wordTrace_append hprefix tailTrace_93278
  have hstable : (prefixWord ++ tailWord_93278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93278).length < 2 ^ (prefixWord ++ tailWord_93278).sum := by decide
  have hdescent : baseEnd_93278 < baseStart_93278 := by decide
  rcases family_descends (prefixWord ++ tailWord_93278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93282 : List Nat := [3, 3, 2, 2, 1, 2, 3, 2, 1, 3]
def baseStart_93282 : Nat := 118140960795 + 93282 * 2 ^ 59
def prefixEnd_93282 : Nat := 4983230072969 + 3 ^ 40 * 93282 * 2
def baseEnd_93282 : Nat := 31932334941872844964007

theorem tailTrace_93282 : CollatzResearch.WordTrace tailWord_93282 prefixEnd_93282 31932334941872844964007 := by
  unfold tailWord_93282
  simp only [CollatzResearch.WordTrace]
  refine ⟨850568512015680035588525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2268182698708480094902733 850568512015680035588525)
  ·
    refine ⟨318963192005880013345697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 850568512015680035588525 318963192005880013345697)
    ·
      refine ⟨239222394004410010009273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318963192005880013345697 239222394004410010009273)
      ·
        refine ⟨179416795503307507506955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239222394004410010009273 179416795503307507506955)
        ·
          refine ⟨269125193254961261260433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179416795503307507506955 269125193254961261260433)
          ·
            refine ⟨201843894941220945945325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269125193254961261260433 201843894941220945945325)
            ·
              refine ⟨75691460602957854729497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201843894941220945945325 75691460602957854729497)
              ·
                refine ⟨56768595452218391047123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75691460602957854729497 56768595452218391047123)
                ·
                  refine ⟨85152893178327586570685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56768595452218391047123 85152893178327586570685)
                  ·
                    refine ⟨31932334941872844964007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85152893178327586570685 31932334941872844964007)
                    ·
                      rfl

theorem cell22_93282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_93282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93282 prefixEnd_93282 := by exact prefixLift 93282
  have htrace : WordTrace (prefixWord ++ tailWord_93282) baseStart_93282 baseEnd_93282 := by
    simpa [prefixWord, tailWord_93282, baseEnd_93282] using wordTrace_append hprefix tailTrace_93282
  have hstable : (prefixWord ++ tailWord_93282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93282).length < 2 ^ (prefixWord ++ tailWord_93282).sum := by decide
  have hdescent : baseEnd_93282 < baseStart_93282 := by decide
  rcases family_descends (prefixWord ++ tailWord_93282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93289 : List Nat := [1, 2, 1, 1, 1, 6, 3, 1, 6]
def baseStart_93289 : Nat := 118140960795 + 93289 * 2 ^ 59
def prefixEnd_93289 : Nat := 4983230072969 + 3 ^ 40 * 93289 * 2
def baseEnd_93289 : Nat := 10644910394975720012995

theorem tailTrace_93289 : CollatzResearch.WordTrace tailWord_93289 prefixEnd_93289 10644910394975720012995 := by
  unfold tailWord_93289
  simp only [CollatzResearch.WordTrace]
  refine ⟨3402529359037360337858921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2268352906024906891905947 3402529359037360337858921)
  ·
    refine ⟨2551897019278020253394191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3402529359037360337858921 2551897019278020253394191)
    ·
      refine ⟨3827845528917030380091287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2551897019278020253394191 3827845528917030380091287)
      ·
        refine ⟨5741768293375545570136931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3827845528917030380091287 5741768293375545570136931)
        ·
          refine ⟨8612652440063318355205397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5741768293375545570136931 8612652440063318355205397)
          ·
            refine ⟨403718083127968047900253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8612652440063318355205397 403718083127968047900253)
            ·
              refine ⟨151394281172988017962595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 403718083127968047900253 151394281172988017962595)
              ·
                refine ⟨227091421759482026943893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151394281172988017962595 227091421759482026943893)
                ·
                  refine ⟨10644910394975720012995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 227091421759482026943893 10644910394975720012995)
                  ·
                    rfl

theorem cell22_93289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 6].length) (baseStart_93289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93289 prefixEnd_93289 := by exact prefixLift 93289
  have htrace : WordTrace (prefixWord ++ tailWord_93289) baseStart_93289 baseEnd_93289 := by
    simpa [prefixWord, tailWord_93289, baseEnd_93289] using wordTrace_append hprefix tailTrace_93289
  have hstable : (prefixWord ++ tailWord_93289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93289).length < 2 ^ (prefixWord ++ tailWord_93289).sum := by decide
  have hdescent : baseEnd_93289 < baseStart_93289 := by decide
  rcases family_descends (prefixWord ++ tailWord_93289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93336 : List Nat := [2, 1, 2, 4, 2, 1, 2, 2, 2, 4]
def baseStart_93336 : Nat := 118140960795 + 93336 * 2 ^ 59
def prefixEnd_93336 : Nat := 4983230072969 + 3 ^ 40 * 93336 * 2
def baseEnd_93336 : Nat := 31950820245434704113841

theorem tailTrace_93336 : CollatzResearch.WordTrace tailWord_93336 prefixEnd_93336 31950820245434704113841 := by
  unfold tailWord_93336
  simp only [CollatzResearch.WordTrace]
  refine ⟨1702121794933543682409931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2269495726578058243213241 1702121794933543682409931)
  ·
    refine ⟨2553182692400315523614897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1702121794933543682409931 2553182692400315523614897)
    ·
      refine ⟨1914887019300236642711173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2553182692400315523614897 1914887019300236642711173)
      ·
        refine ⟨359041316118794370508345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1914887019300236642711173 359041316118794370508345)
        ·
          refine ⟨269280987089095777881259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359041316118794370508345 269280987089095777881259)
          ·
            refine ⟨403921480633643666821889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269280987089095777881259 403921480633643666821889)
            ·
              refine ⟨302941110475232750116417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 403921480633643666821889 302941110475232750116417)
              ·
                refine ⟨227205832856424562587313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302941110475232750116417 227205832856424562587313)
                ·
                  refine ⟨170404374642318421940485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227205832856424562587313 170404374642318421940485)
                  ·
                    refine ⟨31950820245434704113841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 170404374642318421940485 31950820245434704113841)
                    ·
                      rfl

theorem cell22_93336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_93336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93336 prefixEnd_93336 := by exact prefixLift 93336
  have htrace : WordTrace (prefixWord ++ tailWord_93336) baseStart_93336 baseEnd_93336 := by
    simpa [prefixWord, tailWord_93336, baseEnd_93336] using wordTrace_append hprefix tailTrace_93336
  have hstable : (prefixWord ++ tailWord_93336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93336).length < 2 ^ (prefixWord ++ tailWord_93336).sum := by decide
  have hdescent : baseEnd_93336 < baseStart_93336 := by decide
  rcases family_descends (prefixWord ++ tailWord_93336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93338 : List Nat := [3, 1, 1, 5, 1, 1, 1, 4, 2, 3]
def baseStart_93338 : Nat := 118140960795 + 93338 * 2 ^ 59
def prefixEnd_93338 : Nat := 4983230072969 + 3 ^ 40 * 93338 * 2
def baseEnd_93338 : Nat := 31951504886307365563835

theorem tailTrace_93338 : CollatzResearch.WordTrace tailWord_93338 prefixEnd_93338 31951504886307365563835 := by
  unfold tailWord_93338
  simp only [CollatzResearch.WordTrace]
  refine ⟨851079133964960426598167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2269544357239894470928445 851079133964960426598167)
  ·
    refine ⟨1276618700947440639897251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 851079133964960426598167 1276618700947440639897251)
    ·
      refine ⟨1914928051421160959845877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1276618700947440639897251 1914928051421160959845877)
      ·
        refine ⟨179524504820733839985551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1914928051421160959845877 179524504820733839985551)
        ·
          refine ⟨269286757231100759978327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179524504820733839985551 269286757231100759978327)
          ·
            refine ⟨403930135846651139967491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269286757231100759978327 403930135846651139967491)
            ·
              refine ⟨605895203769976709951237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403930135846651139967491 605895203769976709951237)
              ·
                refine ⟨113605350706870633115857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 605895203769976709951237 113605350706870633115857)
                ·
                  refine ⟨85204013030152974836893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113605350706870633115857 85204013030152974836893)
                  ·
                    refine ⟨31951504886307365563835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85204013030152974836893 31951504886307365563835)
                    ·
                      rfl

theorem cell22_93338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 2, 3].length) (baseStart_93338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93338 prefixEnd_93338 := by exact prefixLift 93338
  have htrace : WordTrace (prefixWord ++ tailWord_93338) baseStart_93338 baseEnd_93338 := by
    simpa [prefixWord, tailWord_93338, baseEnd_93338] using wordTrace_append hprefix tailTrace_93338
  have hstable : (prefixWord ++ tailWord_93338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93338).length < 2 ^ (prefixWord ++ tailWord_93338).sum := by decide
  have hdescent : baseEnd_93338 < baseStart_93338 := by decide
  rcases family_descends (prefixWord ++ tailWord_93338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93340 : List Nat := [2, 2, 3, 2, 1, 4, 2, 2, 4]
def baseStart_93340 : Nat := 118140960795 + 93340 * 2 ^ 59
def prefixEnd_93340 : Nat := 4983230072969 + 3 ^ 40 * 93340 * 2
def baseEnd_93340 : Nat := 10650729842393342337943

theorem tailTrace_93340 : CollatzResearch.WordTrace tailWord_93340 prefixEnd_93340 10650729842393342337943 := by
  unfold tailWord_93340
  simp only [CollatzResearch.WordTrace]
  refine ⟨1702194740926298023982737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2269592987901730698643649 1702194740926298023982737)
  ·
    refine ⟨1276646055694723517987053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1702194740926298023982737 1276646055694723517987053)
    ·
      refine ⟨478742270885521319245145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1276646055694723517987053 478742270885521319245145)
      ·
        refine ⟨359056703164140989433859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 478742270885521319245145 359056703164140989433859)
        ·
          refine ⟨538585054746211484150789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359056703164140989433859 538585054746211484150789)
          ·
            refine ⟨100984697764914653278273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 538585054746211484150789 100984697764914653278273)
            ·
              refine ⟨75738523323685989958705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100984697764914653278273 75738523323685989958705)
              ·
                refine ⟨56803892492764492469029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75738523323685989958705 56803892492764492469029)
                ·
                  refine ⟨10650729842393342337943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56803892492764492469029 10650729842393342337943)
                  ·
                    rfl

theorem cell22_93340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 4].length) (baseStart_93340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93340 prefixEnd_93340 := by exact prefixLift 93340
  have htrace : WordTrace (prefixWord ++ tailWord_93340) baseStart_93340 baseEnd_93340 := by
    simpa [prefixWord, tailWord_93340, baseEnd_93340] using wordTrace_append hprefix tailTrace_93340
  have hstable : (prefixWord ++ tailWord_93340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93340).length < 2 ^ (prefixWord ++ tailWord_93340).sum := by decide
  have hdescent : baseEnd_93340 < baseStart_93340 := by decide
  rcases family_descends (prefixWord ++ tailWord_93340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93351 : List Nat := [1, 1, 6, 2, 1, 1, 3, 7]
def baseStart_93351 : Nat := 118140960795 + 93351 * 2 ^ 59
def prefixEnd_93351 : Nat := 4983230072969 + 3 ^ 40 * 93351 * 2
def baseEnd_93351 : Nat := 3550661672442184998755

theorem tailTrace_93351 : CollatzResearch.WordTrace tailWord_93351 prefixEnd_93351 3550661672442184998755 := by
  unfold tailWord_93351
  simp only [CollatzResearch.WordTrace]
  refine ⟨3404790684812744926615907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2269860456541829951077271 3404790684812744926615907)
  ·
    refine ⟨5107186027219117389923861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3404790684812744926615907 5107186027219117389923861)
    ·
      refine ⟨239399345025896127652681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5107186027219117389923861 239399345025896127652681)
      ·
        refine ⟨179549508769422095739511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239399345025896127652681 179549508769422095739511)
        ·
          refine ⟨269324263154133143609267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179549508769422095739511 269324263154133143609267)
          ·
            refine ⟨403986394731199715413901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269324263154133143609267 403986394731199715413901)
            ·
              refine ⟨151494898024199893280213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 403986394731199715413901 151494898024199893280213)
              ·
                refine ⟨3550661672442184998755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 151494898024199893280213 3550661672442184998755)
                ·
                  rfl

theorem cell22_93351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 7].length) (baseStart_93351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93351 prefixEnd_93351 := by exact prefixLift 93351
  have htrace : WordTrace (prefixWord ++ tailWord_93351) baseStart_93351 baseEnd_93351 := by
    simpa [prefixWord, tailWord_93351, baseEnd_93351] using wordTrace_append hprefix tailTrace_93351
  have hstable : (prefixWord ++ tailWord_93351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93351).length < 2 ^ (prefixWord ++ tailWord_93351).sum := by decide
  have hdescent : baseEnd_93351 < baseStart_93351 := by decide
  rcases family_descends (prefixWord ++ tailWord_93351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93389 : List Nat := [1, 6, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_93389 : Nat := 118140960795 + 93389 * 2 ^ 59
def prefixEnd_93389 : Nat := 4983230072969 + 3 ^ 40 * 93389 * 2
def baseEnd_93389 : Nat := 31968963228560232538679

theorem tailTrace_93389 : CollatzResearch.WordTrace tailWord_93389 prefixEnd_93389 31968963228560232538679 := by
  unfold tailWord_93389
  simp only [CollatzResearch.WordTrace]
  refine ⟨3406176658675077416499221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2270784439116718277666147 3406176658675077416499221)
  ·
    refine ⟨159664530875394253898401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3406176658675077416499221 159664530875394253898401)
    ·
      refine ⟨119748398156545690423801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159664530875394253898401 119748398156545690423801)
      ·
        refine ⟨89811298617409267817851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119748398156545690423801 89811298617409267817851)
        ·
          refine ⟨134716947926113901726777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89811298617409267817851 134716947926113901726777)
          ·
            refine ⟨101037710944585426295083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134716947926113901726777 101037710944585426295083)
            ·
              refine ⟨151556566416878139442625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101037710944585426295083 151556566416878139442625)
              ·
                refine ⟨113667424812658604581969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151556566416878139442625 113667424812658604581969)
                ·
                  refine ⟨85250568609493953436477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113667424812658604581969 85250568609493953436477)
                  ·
                    refine ⟨31968963228560232538679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85250568609493953436477 31968963228560232538679)
                    ·
                      rfl

theorem cell22_93389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_93389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93389 prefixEnd_93389 := by exact prefixLift 93389
  have htrace : WordTrace (prefixWord ++ tailWord_93389) baseStart_93389 baseEnd_93389 := by
    simpa [prefixWord, tailWord_93389, baseEnd_93389] using wordTrace_append hprefix tailTrace_93389
  have hstable : (prefixWord ++ tailWord_93389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93389).length < 2 ^ (prefixWord ++ tailWord_93389).sum := by decide
  have hdescent : baseEnd_93389 < baseStart_93389 := by decide
  rcases family_descends (prefixWord ++ tailWord_93389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93494 : List Nat := [5, 1, 2, 3, 1, 1, 3, 1, 1, 4]
def baseStart_93494 : Nat := 118140960795 + 93494 * 2 ^ 59
def prefixEnd_93494 : Nat := 4983230072969 + 3 ^ 40 * 93494 * 2
def baseEnd_93494 : Nat := 32004906874374958663357

theorem tailTrace_93494 : CollatzResearch.WordTrace tailWord_93494 prefixEnd_93494 32004906874374958663357 := by
  unfold tailWord_93494
  simp only [CollatzResearch.WordTrace]
  refine ⟨213125395205917521816971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2273337548863120232714357 213125395205917521816971)
  ·
    refine ⟨319688092808876282725457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213125395205917521816971 319688092808876282725457)
    ·
      refine ⟨239766069606657212044093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319688092808876282725457 239766069606657212044093)
      ·
        refine ⟨89912276102496454516535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239766069606657212044093 89912276102496454516535)
        ·
          refine ⟨134868414153744681774803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89912276102496454516535 134868414153744681774803)
          ·
            refine ⟨202302621230617022662205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134868414153744681774803 202302621230617022662205)
            ·
              refine ⟨75863482961481383498327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202302621230617022662205 75863482961481383498327)
              ·
                refine ⟨113795224442222075247491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75863482961481383498327 113795224442222075247491)
                ·
                  refine ⟨170692836663333112871237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113795224442222075247491 170692836663333112871237)
                  ·
                    refine ⟨32004906874374958663357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 170692836663333112871237 32004906874374958663357)
                    ·
                      rfl

theorem cell22_93494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_93494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93494 prefixEnd_93494 := by exact prefixLift 93494
  have htrace : WordTrace (prefixWord ++ tailWord_93494) baseStart_93494 baseEnd_93494 := by
    simpa [prefixWord, tailWord_93494, baseEnd_93494] using wordTrace_append hprefix tailTrace_93494
  have hstable : (prefixWord ++ tailWord_93494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93494).length < 2 ^ (prefixWord ++ tailWord_93494).sum := by decide
  have hdescent : baseEnd_93494 < baseStart_93494 := by decide
  rcases family_descends (prefixWord ++ tailWord_93494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93516 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 2, 6]
def baseStart_93516 : Nat := 118140960795 + 93516 * 2 ^ 59
def prefixEnd_93516 : Nat := 4983230072969 + 3 ^ 40 * 93516 * 2
def baseEnd_93516 : Nat := 32012437923974234613289

theorem tailTrace_93516 : CollatzResearch.WordTrace tailWord_93516 prefixEnd_93516 32012437923974234613289 := by
  unfold tailWord_93516
  simp only [CollatzResearch.WordTrace]
  refine ⟨1705404364607489053186201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2273872486143318737581601 1705404364607489053186201)
  ·
    refine ⟨1279053273455616789889651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1705404364607489053186201 1279053273455616789889651)
    ·
      refine ⟨1918579910183425184834477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1279053273455616789889651 1918579910183425184834477)
      ·
        refine ⟨719467466318784444312929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1918579910183425184834477 719467466318784444312929)
        ·
          refine ⟨539600599739088333234697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 719467466318784444312929 539600599739088333234697)
          ·
            refine ⟨404700449804316249926023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 539600599739088333234697 404700449804316249926023)
            ·
              refine ⟨607050674706474374889035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404700449804316249926023 607050674706474374889035)
              ·
                refine ⟨910576012059711562333553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 607050674706474374889035 910576012059711562333553)
                ·
                  refine ⟨682932009044783671750165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 910576012059711562333553 682932009044783671750165)
                  ·
                    refine ⟨32012437923974234613289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 682932009044783671750165 32012437923974234613289)
                    ·
                      rfl

theorem cell22_93516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_93516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93516 prefixEnd_93516 := by exact prefixLift 93516
  have htrace : WordTrace (prefixWord ++ tailWord_93516) baseStart_93516 baseEnd_93516 := by
    simpa [prefixWord, tailWord_93516, baseEnd_93516] using wordTrace_append hprefix tailTrace_93516
  have hstable : (prefixWord ++ tailWord_93516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93516).length < 2 ^ (prefixWord ++ tailWord_93516).sum := by decide
  have hdescent : baseEnd_93516 < baseStart_93516 := by decide
  rcases family_descends (prefixWord ++ tailWord_93516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93518 : List Nat := [4, 1, 1, 1, 1, 1, 4, 3, 3, 3]
def baseStart_93518 : Nat := 118140960795 + 93518 * 2 ^ 59
def prefixEnd_93518 : Nat := 4983230072969 + 3 ^ 40 * 93518 * 2
def baseEnd_93518 : Nat := 32013122564846896063283

theorem tailTrace_93518 : CollatzResearch.WordTrace tailWord_93518 prefixEnd_93518 32013122564846896063283 := by
  unfold tailWord_93518
  simp only [CollatzResearch.WordTrace]
  refine ⟨426360209400966555993151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2273921116805154965296805 426360209400966555993151)
  ·
    refine ⟨639540314101449833989727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 426360209400966555993151 639540314101449833989727)
    ·
      refine ⟨959310471152174750984591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 639540314101449833989727 959310471152174750984591)
      ·
        refine ⟨1438965706728262126476887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 959310471152174750984591 1438965706728262126476887)
        ·
          refine ⟨2158448560092393189715331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438965706728262126476887 2158448560092393189715331)
          ·
            refine ⟨3237672840138589784572997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2158448560092393189715331 3237672840138589784572997)
            ·
              refine ⟨607063657525985584607437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3237672840138589784572997 607063657525985584607437)
              ·
                refine ⟨227648871572244594227789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 607063657525985584607437 227648871572244594227789)
                ·
                  refine ⟨85368326839591722835421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227648871572244594227789 85368326839591722835421)
                  ·
                    refine ⟨32013122564846896063283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85368326839591722835421 32013122564846896063283)
                    ·
                      rfl

theorem cell22_93518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_93518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93518 prefixEnd_93518 := by exact prefixLift 93518
  have htrace : WordTrace (prefixWord ++ tailWord_93518) baseStart_93518 baseEnd_93518 := by
    simpa [prefixWord, tailWord_93518, baseEnd_93518] using wordTrace_append hprefix tailTrace_93518
  have hstable : (prefixWord ++ tailWord_93518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93518).length < 2 ^ (prefixWord ++ tailWord_93518).sum := by decide
  have hdescent : baseEnd_93518 < baseStart_93518 := by decide
  rcases family_descends (prefixWord ++ tailWord_93518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93582 : List Nat := [4, 1, 1, 4, 2, 1, 3, 1, 5]
def baseStart_93582 : Nat := 118140960795 + 93582 * 2 ^ 59
def prefixEnd_93582 : Nat := 4983230072969 + 3 ^ 40 * 93582 * 2
def baseEnd_93582 : Nat := 10678343690924020821029

theorem tailTrace_93582 : CollatzResearch.WordTrace tailWord_93582 prefixEnd_93582 10678343690924020821029 := by
  unfold tailWord_93582
  simp only [CollatzResearch.WordTrace]
  refine ⟨426651993371983922284375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2275477297983914252183333 426651993371983922284375)
  ·
    refine ⟨639977990057975883426563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 426651993371983922284375 639977990057975883426563)
    ·
      refine ⟨959966985086963825139845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 639977990057975883426563 959966985086963825139845)
      ·
        refine ⟨179993809703805717213721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 959966985086963825139845 179993809703805717213721)
        ·
          refine ⟨134995357277854287910291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179993809703805717213721 134995357277854287910291)
          ·
            refine ⟨202493035916781431865437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134995357277854287910291 202493035916781431865437)
            ·
              refine ⟨75934888468793036949539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202493035916781431865437 75934888468793036949539)
              ·
                refine ⟨113902332703189555424309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75934888468793036949539 113902332703189555424309)
                ·
                  refine ⟨10678343690924020821029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113902332703189555424309 10678343690924020821029)
                  ·
                    rfl

theorem cell22_93582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_93582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93582 prefixEnd_93582 := by exact prefixLift 93582
  have htrace : WordTrace (prefixWord ++ tailWord_93582) baseStart_93582 baseEnd_93582 := by
    simpa [prefixWord, tailWord_93582, baseEnd_93582] using wordTrace_append hprefix tailTrace_93582
  have hstable : (prefixWord ++ tailWord_93582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93582).length < 2 ^ (prefixWord ++ tailWord_93582).sum := by decide
  have hdescent : baseEnd_93582 < baseStart_93582 := by decide
  rcases family_descends (prefixWord ++ tailWord_93582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93623 : List Nat := [1, 1, 3, 1, 3, 2, 3, 2, 2, 4]
def baseStart_93623 : Nat := 118140960795 + 93623 * 2 ^ 59
def prefixEnd_93623 : Nat := 4983230072969 + 3 ^ 40 * 93623 * 2
def baseEnd_93623 : Nat := 32049066210661622187961

theorem tailTrace_93623 : CollatzResearch.WordTrace tailWord_93623 prefixEnd_93623 32049066210661622187961 := by
  unfold tailWord_93623
  simp only [CollatzResearch.WordTrace]
  refine ⟨3414711339827335380517523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2276474226551556920345015 3414711339827335380517523)
  ·
    refine ⟨5122067009741003070776285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3414711339827335380517523 5122067009741003070776285)
    ·
      refine ⟨1920775128652876151541107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5122067009741003070776285 1920775128652876151541107)
      ·
        refine ⟨2881162692979314227311661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1920775128652876151541107 2881162692979314227311661)
        ·
          refine ⟨1080436009867242835241873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2881162692979314227311661 1080436009867242835241873)
          ·
            refine ⟨810327007400432126431405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1080436009867242835241873 810327007400432126431405)
            ·
              refine ⟨303872627775162047411777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 810327007400432126431405 303872627775162047411777)
              ·
                refine ⟨227904470831371535558833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303872627775162047411777 227904470831371535558833)
                ·
                  refine ⟨170928353123528651669125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227904470831371535558833 170928353123528651669125)
                  ·
                    refine ⟨32049066210661622187961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 170928353123528651669125 32049066210661622187961)
                    ·
                      rfl

theorem cell22_93623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_93623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93623 prefixEnd_93623 := by exact prefixLift 93623
  have htrace : WordTrace (prefixWord ++ tailWord_93623) baseStart_93623 baseEnd_93623 := by
    simpa [prefixWord, tailWord_93623, baseEnd_93623] using wordTrace_append hprefix tailTrace_93623
  have hstable : (prefixWord ++ tailWord_93623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93623).length < 2 ^ (prefixWord ++ tailWord_93623).sum := by decide
  have hdescent : baseEnd_93623 < baseStart_93623 := by decide
  rcases family_descends (prefixWord ++ tailWord_93623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93642 : List Nat := [3, 1, 2, 1, 2, 3, 4, 1, 2, 3]
def baseStart_93642 : Nat := 118140960795 + 93642 * 2 ^ 59
def prefixEnd_93642 : Nat := 4983230072969 + 3 ^ 40 * 93642 * 2
def baseEnd_93642 : Nat := 32055570298951905962903

theorem tailTrace_93642 : CollatzResearch.WordTrace tailWord_93642 prefixEnd_93642 32055570298951905962903 := by
  unfold tailWord_93642
  simp only [CollatzResearch.WordTrace]
  refine ⟨853851081689625406364795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2276936217839001083639453 853851081689625406364795)
  ·
    refine ⟨1280776622534438109547193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 853851081689625406364795 1280776622534438109547193)
    ·
      refine ⟨960582466900828582160395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1280776622534438109547193 960582466900828582160395)
      ·
        refine ⟨1440873700351242873240593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 960582466900828582160395 1440873700351242873240593)
        ·
          refine ⟨1080655275263432154930445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1440873700351242873240593 1080655275263432154930445)
          ·
            refine ⟨405245728223787058098917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1080655275263432154930445 405245728223787058098917)
            ·
              refine ⟨75983574041960073393547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 405245728223787058098917 75983574041960073393547)
              ·
                refine ⟨113975361062940110090321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75983574041960073393547 113975361062940110090321)
                ·
                  refine ⟨85481520797205082567741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113975361062940110090321 85481520797205082567741)
                  ·
                    refine ⟨32055570298951905962903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85481520797205082567741 32055570298951905962903)
                    ·
                      rfl

theorem cell22_93642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_93642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93642 prefixEnd_93642 := by exact prefixLift 93642
  have htrace : WordTrace (prefixWord ++ tailWord_93642) baseStart_93642 baseEnd_93642 := by
    simpa [prefixWord, tailWord_93642, baseEnd_93642] using wordTrace_append hprefix tailTrace_93642
  have hstable : (prefixWord ++ tailWord_93642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93642).length < 2 ^ (prefixWord ++ tailWord_93642).sum := by decide
  have hdescent : baseEnd_93642 < baseStart_93642 := by decide
  rcases family_descends (prefixWord ++ tailWord_93642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93685 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 2, 6]
def baseStart_93685 : Nat := 118140960795 + 93685 * 2 ^ 59
def prefixEnd_93685 : Nat := 4983230072969 + 3 ^ 40 * 93685 * 2
def baseEnd_93685 : Nat := 32070290077714127137771

theorem tailTrace_93685 : CollatzResearch.WordTrace tailWord_93685 prefixEnd_93685 32070290077714127137771 := by
  unfold tailWord_93685
  simp only [CollatzResearch.WordTrace]
  refine ⟨3416972665602719969274509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2277981777068479979516339 3416972665602719969274509)
  ·
    refine ⟨1281364749601019988477941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3416972665602719969274509 1281364749601019988477941)
    ·
      refine ⟨120127945275095623919807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1281364749601019988477941 120127945275095623919807)
      ·
        refine ⟨180191917912643435879711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120127945275095623919807 180191917912643435879711)
        ·
          refine ⟨270287876868965153819567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180191917912643435879711 270287876868965153819567)
          ·
            refine ⟨405431815303447730729351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270287876868965153819567 405431815303447730729351)
            ·
              refine ⟨608147722955171596094027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405431815303447730729351 608147722955171596094027)
              ·
                refine ⟨912221584432757394141041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 608147722955171596094027 912221584432757394141041)
                ·
                  refine ⟨684166188324568045605781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 912221584432757394141041 684166188324568045605781)
                  ·
                    refine ⟨32070290077714127137771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 684166188324568045605781 32070290077714127137771)
                    ·
                      rfl

theorem cell22_93685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_93685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93685 prefixEnd_93685 := by exact prefixLift 93685
  have htrace : WordTrace (prefixWord ++ tailWord_93685) baseStart_93685 baseEnd_93685 := by
    simpa [prefixWord, tailWord_93685, baseEnd_93685] using wordTrace_append hprefix tailTrace_93685
  have hstable : (prefixWord ++ tailWord_93685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93685).length < 2 ^ (prefixWord ++ tailWord_93685).sum := by decide
  have hdescent : baseEnd_93685 < baseStart_93685 := by decide
  rcases family_descends (prefixWord ++ tailWord_93685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93713 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 3, 4]
def baseStart_93713 : Nat := 118140960795 + 93713 * 2 ^ 59
def prefixEnd_93713 : Nat := 4983230072969 + 3 ^ 40 * 93713 * 2
def baseEnd_93713 : Nat := 32079875049931387437685

theorem tailTrace_93713 : CollatzResearch.WordTrace tailWord_93713 prefixEnd_93713 32079875049931387437685 := by
  unfold tailWord_93713
  simp only [CollatzResearch.WordTrace]
  refine ⟨3417993909501280751293793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2278662606334187167529195 3417993909501280751293793)
  ·
    refine ⟨2563495432125960563470345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3417993909501280751293793 2563495432125960563470345)
    ·
      refine ⟨1922621574094470422602759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2563495432125960563470345 1922621574094470422602759)
      ·
        refine ⟨2883932361141705633904139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1922621574094470422602759 2883932361141705633904139)
        ·
          refine ⟨4325898541712558450856209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2883932361141705633904139 4325898541712558450856209)
          ·
            refine ⟨3244423906284418838142157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4325898541712558450856209 3244423906284418838142157)
            ·
              refine ⟨1216658964856657064303309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3244423906284418838142157 1216658964856657064303309)
              ·
                refine ⟨456247111821246399113741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1216658964856657064303309 456247111821246399113741)
                ·
                  refine ⟨171092666932967399667653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 456247111821246399113741 171092666932967399667653)
                  ·
                    refine ⟨32079875049931387437685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 171092666932967399667653 32079875049931387437685)
                    ·
                      rfl

theorem cell22_93713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_93713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93713 prefixEnd_93713 := by exact prefixLift 93713
  have htrace : WordTrace (prefixWord ++ tailWord_93713) baseStart_93713 baseEnd_93713 := by
    simpa [prefixWord, tailWord_93713, baseEnd_93713] using wordTrace_append hprefix tailTrace_93713
  have hstable : (prefixWord ++ tailWord_93713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93713).length < 2 ^ (prefixWord ++ tailWord_93713).sum := by decide
  have hdescent : baseEnd_93713 < baseStart_93713 := by decide
  rcases family_descends (prefixWord ++ tailWord_93713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93818 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 9]
def baseStart_93818 : Nat := 118140960795 + 93818 * 2 ^ 59
def prefixEnd_93818 : Nat := 4983230072969 + 3 ^ 40 * 93818 * 2
def baseEnd_93818 : Nat := 10705272898582037854121

theorem tailTrace_93818 : CollatzResearch.WordTrace tailWord_93818 prefixEnd_93818 10705272898582037854121 := by
  unfold tailWord_93818
  simp only [CollatzResearch.WordTrace]
  refine ⟨855455893530220920966527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2281215716080589122577405 855455893530220920966527)
  ·
    refine ⟨1283183840295331381449791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 855455893530220920966527 1283183840295331381449791)
    ·
      refine ⟨1924775760442997072174687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1283183840295331381449791 1924775760442997072174687)
      ·
        refine ⟨2887163640664495608262031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1924775760442997072174687 2887163640664495608262031)
        ·
          refine ⟨4330745460996743412393047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2887163640664495608262031 4330745460996743412393047)
          ·
            refine ⟨6496118191495115118589571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4330745460996743412393047 6496118191495115118589571)
            ·
              refine ⟨9744177287242672677884357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6496118191495115118589571 9744177287242672677884357)
              ·
                refine ⟨1827033241358001127103317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9744177287242672677884357 1827033241358001127103317)
                ·
                  refine ⟨10705272898582037854121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1827033241358001127103317 10705272898582037854121)
                  ·
                    rfl

theorem cell22_93818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_93818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93818 prefixEnd_93818 := by exact prefixLift 93818
  have htrace : WordTrace (prefixWord ++ tailWord_93818) baseStart_93818 baseEnd_93818 := by
    simpa [prefixWord, tailWord_93818, baseEnd_93818] using wordTrace_append hprefix tailTrace_93818
  have hstable : (prefixWord ++ tailWord_93818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93818).length < 2 ^ (prefixWord ++ tailWord_93818).sum := by decide
  have hdescent : baseEnd_93818 < baseStart_93818 := by decide
  rcases family_descends (prefixWord ++ tailWord_93818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93856 : List Nat := [2, 1, 1, 4, 3, 1, 4, 2, 1, 3]
def baseStart_93856 : Nat := 118140960795 + 93856 * 2 ^ 59
def prefixEnd_93856 : Nat := 4983230072969 + 3 ^ 40 * 93856 * 2
def baseEnd_93856 : Nat := 32128826872326681112247

theorem tailTrace_93856 : CollatzResearch.WordTrace tailWord_93856 prefixEnd_93856 32128826872326681112247 := by
  unfold tailWord_93856
  simp only [CollatzResearch.WordTrace]
  refine ⟨1711604773991608086874711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2282139698655477449166281 1711604773991608086874711)
  ·
    refine ⟨2567407160987412130312067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1711604773991608086874711 2567407160987412130312067)
    ·
      refine ⟨3851110741481118195468101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2567407160987412130312067 3851110741481118195468101)
      ·
        refine ⟨722083264027709661650269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3851110741481118195468101 722083264027709661650269)
        ·
          refine ⟨270781224010391123118851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 722083264027709661650269 270781224010391123118851)
          ·
            refine ⟨406171836015586684678277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270781224010391123118851 406171836015586684678277)
            ·
              refine ⟨76157219252922503377177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 406171836015586684678277 76157219252922503377177)
              ·
                refine ⟨57117914439691877532883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76157219252922503377177 57117914439691877532883)
                ·
                  refine ⟨85676871659537816299325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57117914439691877532883 85676871659537816299325)
                  ·
                    refine ⟨32128826872326681112247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85676871659537816299325 32128826872326681112247)
                    ·
                      rfl

theorem cell22_93856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 1, 3].length) (baseStart_93856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93856 prefixEnd_93856 := by exact prefixLift 93856
  have htrace : WordTrace (prefixWord ++ tailWord_93856) baseStart_93856 baseEnd_93856 := by
    simpa [prefixWord, tailWord_93856, baseEnd_93856] using wordTrace_append hprefix tailTrace_93856
  have hstable : (prefixWord ++ tailWord_93856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93856).length < 2 ^ (prefixWord ++ tailWord_93856).sum := by decide
  have hdescent : baseEnd_93856 < baseStart_93856 := by decide
  rcases family_descends (prefixWord ++ tailWord_93856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93895 : List Nat := [1, 1, 4, 1, 1, 1, 3, 4, 1, 5]
def baseStart_93895 : Nat := 118140960795 + 93895 * 2 ^ 59
def prefixEnd_93895 : Nat := 4983230072969 + 3 ^ 40 * 93895 * 2
def baseEnd_93895 : Nat := 32142177369343579387127

theorem tailTrace_93895 : CollatzResearch.WordTrace tailWord_93895 prefixEnd_93895 32142177369343579387127 := by
  unfold tailWord_93895
  simp only [CollatzResearch.WordTrace]
  refine ⟨3424631994841925834419139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2283087996561283889612759 3424631994841925834419139)
  ·
    refine ⟨5136947992262888751628709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3424631994841925834419139 5136947992262888751628709)
    ·
      refine ⟨963177748549291640930383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5136947992262888751628709 963177748549291640930383)
      ·
        refine ⟨1444766622823937461395575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 963177748549291640930383 1444766622823937461395575)
        ·
          refine ⟨2167149934235906192093363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1444766622823937461395575 2167149934235906192093363)
          ·
            refine ⟨3250724901353859288140045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2167149934235906192093363 3250724901353859288140045)
            ·
              refine ⟨1219021838007697233052517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3250724901353859288140045 1219021838007697233052517)
              ·
                refine ⟨228566594626443231197347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1219021838007697233052517 228566594626443231197347)
                ·
                  refine ⟨342849891939664846796021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228566594626443231197347 342849891939664846796021)
                  ·
                    refine ⟨32142177369343579387127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 342849891939664846796021 32142177369343579387127)
                    ·
                      rfl

theorem cell22_93895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_93895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93895 prefixEnd_93895 := by exact prefixLift 93895
  have htrace : WordTrace (prefixWord ++ tailWord_93895) baseStart_93895 baseEnd_93895 := by
    simpa [prefixWord, tailWord_93895, baseEnd_93895] using wordTrace_append hprefix tailTrace_93895
  have hstable : (prefixWord ++ tailWord_93895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93895).length < 2 ^ (prefixWord ++ tailWord_93895).sum := by decide
  have hdescent : baseEnd_93895 < baseStart_93895 := by decide
  rcases family_descends (prefixWord ++ tailWord_93895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93912 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 4, 3]
def baseStart_93912 : Nat := 118140960795 + 93912 * 2 ^ 59
def prefixEnd_93912 : Nat := 4983230072969 + 3 ^ 40 * 93912 * 2
def baseEnd_93912 : Nat := 32147996816761201712075

theorem tailTrace_93912 : CollatzResearch.WordTrace tailWord_93912 prefixEnd_93912 32147996816761201712075 := by
  unfold tailWord_93912
  simp only [CollatzResearch.WordTrace]
  refine ⟨1712626017890168868893995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2283501357186891825191993 1712626017890168868893995)
  ·
    refine ⟨2568939026835253303340993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1712626017890168868893995 2568939026835253303340993)
    ·
      refine ⟨1926704270126439977505745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2568939026835253303340993 1926704270126439977505745)
      ·
        refine ⟨1445028202594829983129309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1926704270126439977505745 1445028202594829983129309)
        ·
          refine ⟨541885575973061243673491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1445028202594829983129309 541885575973061243673491)
          ·
            refine ⟨812828363959591865510237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541885575973061243673491 812828363959591865510237)
            ·
              refine ⟨304810636484846949566339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 812828363959591865510237 304810636484846949566339)
              ·
                refine ⟨457215954727270424349509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304810636484846949566339 457215954727270424349509)
                ·
                  refine ⟨85727991511363204565533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 457215954727270424349509 85727991511363204565533)
                  ·
                    refine ⟨32147996816761201712075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85727991511363204565533 32147996816761201712075)
                    ·
                      rfl

theorem cell22_93912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 4, 3].length) (baseStart_93912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93912 prefixEnd_93912 := by exact prefixLift 93912
  have htrace : WordTrace (prefixWord ++ tailWord_93912) baseStart_93912 baseEnd_93912 := by
    simpa [prefixWord, tailWord_93912, baseEnd_93912] using wordTrace_append hprefix tailTrace_93912
  have hstable : (prefixWord ++ tailWord_93912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93912).length < 2 ^ (prefixWord ++ tailWord_93912).sum := by decide
  have hdescent : baseEnd_93912 < baseStart_93912 := by decide
  rcases family_descends (prefixWord ++ tailWord_93912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93925 : List Nat := [1, 3, 1, 4, 1, 1, 2, 9]
def baseStart_93925 : Nat := 118140960795 + 93925 * 2 ^ 59
def prefixEnd_93925 : Nat := 4983230072969 + 3 ^ 40 * 93925 * 2
def baseEnd_93925 : Nat := 3572494109159277904115

theorem tailTrace_93925 : CollatzResearch.WordTrace tailWord_93925 prefixEnd_93925 3572494109159277904115 := by
  unfold tailWord_93925
  simp only [CollatzResearch.WordTrace]
  refine ⟨3425726184733240958011229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2283817456488827305340819 3425726184733240958011229)
  ·
    refine ⟨1284647319274965359254211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3425726184733240958011229 1284647319274965359254211)
    ·
      refine ⟨1926970978912448038881317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1284647319274965359254211 1926970978912448038881317)
      ·
        refine ⟨361307058546084007290247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1926970978912448038881317 361307058546084007290247)
        ·
          refine ⟨541960587819126010935371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361307058546084007290247 541960587819126010935371)
          ·
            refine ⟨812940881728689016403057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541960587819126010935371 812940881728689016403057)
            ·
              refine ⟨609705661296516762302293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 812940881728689016403057 609705661296516762302293)
              ·
                refine ⟨3572494109159277904115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 609705661296516762302293 3572494109159277904115)
                ·
                  rfl

theorem cell22_93925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 9].length) (baseStart_93925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93925 prefixEnd_93925 := by exact prefixLift 93925
  have htrace : WordTrace (prefixWord ++ tailWord_93925) baseStart_93925 baseEnd_93925 := by
    simpa [prefixWord, tailWord_93925, baseEnd_93925] using wordTrace_append hprefix tailTrace_93925
  have hstable : (prefixWord ++ tailWord_93925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93925).length < 2 ^ (prefixWord ++ tailWord_93925).sum := by decide
  have hdescent : baseEnd_93925 < baseStart_93925 := by decide
  rcases family_descends (prefixWord ++ tailWord_93925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93942 : List Nat := [5, 1, 1, 1, 1, 4, 1, 8]
def baseStart_93942 : Nat := 118140960795 + 93942 * 2 ^ 59
def prefixEnd_93942 : Nat := 4983230072969 + 3 ^ 40 * 93942 * 2
def baseEnd_93942 : Nat := 3573140714427902606887

theorem tailTrace_93942 : CollatzResearch.WordTrace tailWord_93942 prefixEnd_93942 3573140714427902606887 := by
  unfold tailWord_93942
  simp only [CollatzResearch.WordTrace]
  refine ⟨214146639104478303836255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2284230817114435240920053 214146639104478303836255)
  ·
    refine ⟨321219958656717455754383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214146639104478303836255 321219958656717455754383)
    ·
      refine ⟨481829937985076183631575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321219958656717455754383 481829937985076183631575)
      ·
        refine ⟨722744906977614275447363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481829937985076183631575 722744906977614275447363)
        ·
          refine ⟨1084117360466421413171045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722744906977614275447363 1084117360466421413171045)
          ·
            refine ⟨203272005087454014969571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1084117360466421413171045 203272005087454014969571)
            ·
              refine ⟨304908007631181022454357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203272005087454014969571 304908007631181022454357)
              ·
                refine ⟨3573140714427902606887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 304908007631181022454357 3573140714427902606887)
                ·
                  rfl

theorem cell22_93942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_93942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93942 prefixEnd_93942 := by exact prefixLift 93942
  have htrace : WordTrace (prefixWord ++ tailWord_93942) baseStart_93942 baseEnd_93942 := by
    simpa [prefixWord, tailWord_93942, baseEnd_93942] using wordTrace_append hprefix tailTrace_93942
  have hstable : (prefixWord ++ tailWord_93942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93942).length < 2 ^ (prefixWord ++ tailWord_93942).sum := by decide
  have hdescent : baseEnd_93942 < baseStart_93942 := by decide
  rcases family_descends (prefixWord ++ tailWord_93942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93959 : List Nat := [1, 1, 4, 4, 3, 1, 8]
def baseStart_93959 : Nat := 118140960795 + 93959 * 2 ^ 59
def prefixEnd_93959 : Nat := 4983230072969 + 3 ^ 40 * 93959 * 2
def baseEnd_93959 : Nat := 1191262439898842436553

theorem tailTrace_93959 : CollatzResearch.WordTrace tailWord_93959 prefixEnd_93959 1191262439898842436553 := by
  unfold tailWord_93959
  simp only [CollatzResearch.WordTrace]
  refine ⟨3426966266610064764748931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2284644177740043176499287 3426966266610064764748931)
  ·
    refine ⟨5140449399915097147123397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3426966266610064764748931 5140449399915097147123397)
    ·
      refine ⟨963834262484080715085637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5140449399915097147123397 963834262484080715085637)
      ·
        refine ⟨180718924215765134078557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 963834262484080715085637 180718924215765134078557)
        ·
          refine ⟨67769596580911925279459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180718924215765134078557 67769596580911925279459)
          ·
            refine ⟨101654394871367887919189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67769596580911925279459 101654394871367887919189)
            ·
              refine ⟨1191262439898842436553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 101654394871367887919189 1191262439898842436553)
              ·
                rfl

theorem cell22_93959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 8].length) (baseStart_93959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93959 prefixEnd_93959 := by exact prefixLift 93959
  have htrace : WordTrace (prefixWord ++ tailWord_93959) baseStart_93959 baseEnd_93959 := by
    simpa [prefixWord, tailWord_93959, baseEnd_93959] using wordTrace_append hprefix tailTrace_93959
  have hstable : (prefixWord ++ tailWord_93959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93959).length < 2 ^ (prefixWord ++ tailWord_93959).sum := by decide
  have hdescent : baseEnd_93959 < baseStart_93959 := by decide
  rcases family_descends (prefixWord ++ tailWord_93959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93965 : List Nat := [1, 7, 2, 1, 1, 2, 1, 1, 6]
def baseStart_93965 : Nat := 118140960795 + 93965 * 2 ^ 59
def prefixEnd_93965 : Nat := 4983230072969 + 3 ^ 40 * 93965 * 2
def baseEnd_93965 : Nat := 10722046599962243378971

theorem tailTrace_93965 : CollatzResearch.WordTrace tailWord_93965 prefixEnd_93965 10722046599962243378971 := by
  unfold tailWord_93965
  simp only [CollatzResearch.WordTrace]
  refine ⟨3427185104588327789467349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2284790069725551859644899 3427185104588327789467349)
  ·
    refine ⟨80324650888788932565641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 3427185104588327789467349 80324650888788932565641)
    ·
      refine ⟨60243488166591699424231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80324650888788932565641 60243488166591699424231)
      ·
        refine ⟨90365232249887549136347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60243488166591699424231 90365232249887549136347)
        ·
          refine ⟨135547848374831323704521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90365232249887549136347 135547848374831323704521)
          ·
            refine ⟨101660886281123492778391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135547848374831323704521 101660886281123492778391)
            ·
              refine ⟨152491329421685239167587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101660886281123492778391 152491329421685239167587)
              ·
                refine ⟨228736994132527858751381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152491329421685239167587 228736994132527858751381)
                ·
                  refine ⟨10722046599962243378971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 228736994132527858751381 10722046599962243378971)
                  ·
                    rfl

theorem cell22_93965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_93965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_93965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_93965 prefixEnd_93965 := by exact prefixLift 93965
  have htrace : WordTrace (prefixWord ++ tailWord_93965) baseStart_93965 baseEnd_93965 := by
    simpa [prefixWord, tailWord_93965, baseEnd_93965] using wordTrace_append hprefix tailTrace_93965
  have hstable : (prefixWord ++ tailWord_93965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93965).length < 2 ^ (prefixWord ++ tailWord_93965).sum := by decide
  have hdescent : baseEnd_93965 < baseStart_93965 := by decide
  rcases family_descends (prefixWord ++ tailWord_93965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94047 : List Nat := [1, 1, 2, 3, 1, 4, 1, 3, 1, 5]
def baseStart_94047 : Nat := 118140960795 + 94047 * 2 ^ 59
def prefixEnd_94047 : Nat := 4983230072969 + 3 ^ 40 * 94047 * 2
def baseEnd_94047 : Nat := 32194210075665849586661

theorem tailTrace_94047 : CollatzResearch.WordTrace tailWord_94047 prefixEnd_94047 32194210075665849586661 := by
  unfold tailWord_94047
  simp only [CollatzResearch.WordTrace]
  refine ⟨3430175890291255793952395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2286783926860837195968263 3430175890291255793952395)
  ·
    refine ⟨5145263835436883690928593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3430175890291255793952395 5145263835436883690928593)
    ·
      refine ⟨3858947876577662768196445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5145263835436883690928593 3858947876577662768196445)
      ·
        refine ⟨1447105453716623538073667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3858947876577662768196445 1447105453716623538073667)
        ·
          refine ⟨2170658180574935307110501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1447105453716623538073667 2170658180574935307110501)
          ·
            refine ⟨406998408857800370083219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2170658180574935307110501 406998408857800370083219)
            ·
              refine ⟨610497613286700555124829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406998408857800370083219 610497613286700555124829)
              ·
                refine ⟨228936604982512708171811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 610497613286700555124829 228936604982512708171811)
                ·
                  refine ⟨343404907473769062257717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228936604982512708171811 343404907473769062257717)
                  ·
                    refine ⟨32194210075665849586661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 343404907473769062257717 32194210075665849586661)
                    ·
                      rfl

theorem cell22_94047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 5].length) (baseStart_94047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94047 prefixEnd_94047 := by exact prefixLift 94047
  have htrace : WordTrace (prefixWord ++ tailWord_94047) baseStart_94047 baseEnd_94047 := by
    simpa [prefixWord, tailWord_94047, baseEnd_94047] using wordTrace_append hprefix tailTrace_94047
  have hstable : (prefixWord ++ tailWord_94047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94047).length < 2 ^ (prefixWord ++ tailWord_94047).sum := by decide
  have hdescent : baseEnd_94047 < baseStart_94047 := by decide
  rcases family_descends (prefixWord ++ tailWord_94047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94111 : List Nat := [1, 1, 2, 5, 3, 2, 2, 6]
def baseStart_94111 : Nat := 118140960795 + 94111 * 2 ^ 59
def prefixEnd_94111 : Nat := 4983230072969 + 3 ^ 40 * 94111 * 2
def baseEnd_94111 : Nat := 3579568731510112887385

theorem tailTrace_94111 : CollatzResearch.WordTrace tailWord_94111 prefixEnd_94111 3579568731510112887385 := by
  unfold tailWord_94111
  simp only [CollatzResearch.WordTrace]
  refine ⟨3432510162059394724282187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2288340108039596482854791 3432510162059394724282187)
  ·
    refine ⟨5148765243089092086423281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3432510162059394724282187 5148765243089092086423281)
    ·
      refine ⟨3861573932316819064817461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5148765243089092086423281 3861573932316819064817461)
      ·
        refine ⟨362022556154701787326637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3861573932316819064817461 362022556154701787326637)
        ·
          refine ⟨135758458558013170247489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 362022556154701787326637 135758458558013170247489)
          ·
            refine ⟨101818843918509877685617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135758458558013170247489 101818843918509877685617)
            ·
              refine ⟨76364132938882408264213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101818843918509877685617 76364132938882408264213)
              ·
                refine ⟨3579568731510112887385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76364132938882408264213 3579568731510112887385)
                ·
                  rfl

theorem cell22_94111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 6].length) (baseStart_94111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94111 prefixEnd_94111 := by exact prefixLift 94111
  have htrace : WordTrace (prefixWord ++ tailWord_94111) baseStart_94111 baseEnd_94111 := by
    simpa [prefixWord, tailWord_94111, baseEnd_94111] using wordTrace_append hprefix tailTrace_94111
  have hstable : (prefixWord ++ tailWord_94111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94111).length < 2 ^ (prefixWord ++ tailWord_94111).sum := by decide
  have hdescent : baseEnd_94111 < baseStart_94111 := by decide
  rcases family_descends (prefixWord ++ tailWord_94111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94143 : List Nat := [1, 1, 2, 2, 2, 1, 7, 2, 1, 3]
def baseStart_94143 : Nat := 118140960795 + 94143 * 2 ^ 59
def prefixEnd_94143 : Nat := 4983230072969 + 3 ^ 40 * 94143 * 2
def baseEnd_94143 : Nat := 32227072837553599186367

theorem tailTrace_94143 : CollatzResearch.WordTrace tailWord_94143 prefixEnd_94143 32227072837553599186367 := by
  unfold tailWord_94143
  simp only [CollatzResearch.WordTrace]
  refine ⟨3433677297943464189447083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2289118198628976126298055 3433677297943464189447083)
  ·
    refine ⟨5150515946915196284170625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3433677297943464189447083 5150515946915196284170625)
    ·
      refine ⟨3862886960186397213127969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5150515946915196284170625 3862886960186397213127969)
      ·
        refine ⟨2897165220139797909845977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3862886960186397213127969 2897165220139797909845977)
        ·
          refine ⟨2172873915104848432384483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2897165220139797909845977 2172873915104848432384483)
          ·
            refine ⟨3259310872657272648576725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2172873915104848432384483 3259310872657272648576725)
            ·
              refine ⟨76390098577904827701017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 3259310872657272648576725 76390098577904827701017)
              ·
                refine ⟨57292573933428620775763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76390098577904827701017 57292573933428620775763)
                ·
                  refine ⟨85938860900142931163645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57292573933428620775763 85938860900142931163645)
                  ·
                    refine ⟨32227072837553599186367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85938860900142931163645 32227072837553599186367)
                    ·
                      rfl

theorem cell22_94143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 1, 3].length) (baseStart_94143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94143 prefixEnd_94143 := by exact prefixLift 94143
  have htrace : WordTrace (prefixWord ++ tailWord_94143) baseStart_94143 baseEnd_94143 := by
    simpa [prefixWord, tailWord_94143, baseEnd_94143] using wordTrace_append hprefix tailTrace_94143
  have hstable : (prefixWord ++ tailWord_94143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94143).length < 2 ^ (prefixWord ++ tailWord_94143).sum := by decide
  have hdescent : baseEnd_94143 < baseStart_94143 := by decide
  rcases family_descends (prefixWord ++ tailWord_94143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94156 : List Nat := [2, 2, 1, 4, 1, 2, 4, 1, 5]
def baseStart_94156 : Nat := 118140960795 + 94156 * 2 ^ 59
def prefixEnd_94156 : Nat := 4983230072969 + 3 ^ 40 * 94156 * 2
def baseEnd_94156 : Nat := 10743841001075299537109

theorem tailTrace_94156 : CollatzResearch.WordTrace tailWord_94156 prefixEnd_94156 10743841001075299537109 := by
  unfold tailWord_94156
  simp only [CollatzResearch.WordTrace]
  refine ⟨1717075723448183704835161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2289434297930911606446881 1717075723448183704835161)
  ·
    refine ⟨1287806792586137778626371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1717075723448183704835161 1287806792586137778626371)
    ·
      refine ⟨1931710188879206667939557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1287806792586137778626371 1931710188879206667939557)
      ·
        refine ⟨362195660414851250238667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1931710188879206667939557 362195660414851250238667)
        ·
          refine ⟨543293490622276875358001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362195660414851250238667 543293490622276875358001)
          ·
            refine ⟨407470117966707656518501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 543293490622276875358001 407470117966707656518501)
            ·
              refine ⟨76400647118757685597219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 407470117966707656518501 76400647118757685597219)
              ·
                refine ⟨114600970678136528395829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76400647118757685597219 114600970678136528395829)
                ·
                  refine ⟨10743841001075299537109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114600970678136528395829 10743841001075299537109)
                  ·
                    rfl

theorem cell22_94156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 5].length) (baseStart_94156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94156 prefixEnd_94156 := by exact prefixLift 94156
  have htrace : WordTrace (prefixWord ++ tailWord_94156) baseStart_94156 baseEnd_94156 := by
    simpa [prefixWord, tailWord_94156, baseEnd_94156] using wordTrace_append hprefix tailTrace_94156
  have hstable : (prefixWord ++ tailWord_94156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94156).length < 2 ^ (prefixWord ++ tailWord_94156).sum := by decide
  have hdescent : baseEnd_94156 < baseStart_94156 := by decide
  rcases family_descends (prefixWord ++ tailWord_94156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94167 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 8]
def baseStart_94167 : Nat := 118140960795 + 94167 * 2 ^ 59
def prefixEnd_94167 : Nat := 4983230072969 + 3 ^ 40 * 94167 * 2
def baseEnd_94167 : Nat := 10745096176008512195431

theorem tailTrace_94167 : CollatzResearch.WordTrace tailWord_94167 prefixEnd_94167 10745096176008512195431 := by
  unfold tailWord_94167
  simp only [CollatzResearch.WordTrace]
  refine ⟨3434552649856516288320755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2289701766571010858880503 3434552649856516288320755)
  ·
    refine ⟨5151828974784774432481133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3434552649856516288320755 5151828974784774432481133)
    ·
      refine ⟨1931935865544290412180425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5151828974784774432481133 1931935865544290412180425)
      ·
        refine ⟨1448951899158217809135319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1931935865544290412180425 1448951899158217809135319)
        ·
          refine ⟨2173427848737326713702979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1448951899158217809135319 2173427848737326713702979)
          ·
            refine ⟨3260141773105990070554469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2173427848737326713702979 3260141773105990070554469)
            ·
              refine ⟨611276582457373138228963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3260141773105990070554469 611276582457373138228963)
              ·
                refine ⟨916914873686059707343445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 611276582457373138228963 916914873686059707343445)
                ·
                  refine ⟨10745096176008512195431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 916914873686059707343445 10745096176008512195431)
                  ·
                    rfl

theorem cell22_94167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 8].length) (baseStart_94167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94167 prefixEnd_94167 := by exact prefixLift 94167
  have htrace : WordTrace (prefixWord ++ tailWord_94167) baseStart_94167 baseEnd_94167 := by
    simpa [prefixWord, tailWord_94167, baseEnd_94167] using wordTrace_append hprefix tailTrace_94167
  have hstable : (prefixWord ++ tailWord_94167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94167).length < 2 ^ (prefixWord ++ tailWord_94167).sum := by decide
  have hdescent : baseEnd_94167 < baseStart_94167 := by decide
  rcases family_descends (prefixWord ++ tailWord_94167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94201 : List Nat := [1, 2, 1, 3, 1, 5, 1, 4, 4]
def baseStart_94201 : Nat := 118140960795 + 94201 * 2 ^ 59
def prefixEnd_94201 : Nat := 4983230072969 + 3 ^ 40 * 94201 * 2
def baseEnd_94201 : Nat := 10748975807620260412063

theorem tailTrace_94201 : CollatzResearch.WordTrace tailWord_94201 prefixEnd_94201 10748975807620260412063 := by
  unfold tailWord_94201
  simp only [CollatzResearch.WordTrace]
  refine ⟨3435792731733340095058457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2290528487822226730038971 3435792731733340095058457)
  ·
    refine ⟨2576844548800005071293843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3435792731733340095058457 2576844548800005071293843)
    ·
      refine ⟨3865266823200007606940765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2576844548800005071293843 3865266823200007606940765)
      ·
        refine ⟨1449475058700002852602787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3865266823200007606940765 1449475058700002852602787)
        ·
          refine ⟨2174212588050004278904181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1449475058700002852602787 2174212588050004278904181)
          ·
            refine ⟨203832430129687901147267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2174212588050004278904181 203832430129687901147267)
            ·
              refine ⟨305748645194531851720901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203832430129687901147267 305748645194531851720901)
              ·
                refine ⟨57327870973974722197669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 305748645194531851720901 57327870973974722197669)
                ·
                  refine ⟨10748975807620260412063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57327870973974722197669 10748975807620260412063)
                  ·
                    rfl

theorem cell22_94201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 4].length) (baseStart_94201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94201 prefixEnd_94201 := by exact prefixLift 94201
  have htrace : WordTrace (prefixWord ++ tailWord_94201) baseStart_94201 baseEnd_94201 := by
    simpa [prefixWord, tailWord_94201, baseEnd_94201] using wordTrace_append hprefix tailTrace_94201
  have hstable : (prefixWord ++ tailWord_94201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94201).length < 2 ^ (prefixWord ++ tailWord_94201).sum := by decide
  have hdescent : baseEnd_94201 < baseStart_94201 := by decide
  rcases family_descends (prefixWord ++ tailWord_94201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94216 : List Nat := [2, 1, 3, 2, 1, 2, 1, 5, 2, 3]
def baseStart_94216 : Nat := 118140960795 + 94216 * 2 ^ 59
def prefixEnd_94216 : Nat := 4983230072969 + 3 ^ 40 * 94216 * 2
def baseEnd_94216 : Nat := 32252062229405742111143

theorem tailTrace_94216 : CollatzResearch.WordTrace tailWord_94216 prefixEnd_94216 32252062229405742111143 := by
  unfold tailWord_94216
  simp only [CollatzResearch.WordTrace]
  refine ⟨1718169913339498828427251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2290893217785998437903001 1718169913339498828427251)
  ·
    refine ⟨2577254870009248242640877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1718169913339498828427251 2577254870009248242640877)
    ·
      refine ⟨966470576253468090990329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2577254870009248242640877 966470576253468090990329)
      ·
        refine ⟨724852932190101068242747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 966470576253468090990329 724852932190101068242747)
        ·
          refine ⟨1087279398285151602364121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 724852932190101068242747 1087279398285151602364121)
          ·
            refine ⟨815459548713863701773091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1087279398285151602364121 815459548713863701773091)
            ·
              refine ⟨1223189323070795552659637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 815459548713863701773091 1223189323070795552659637)
              ·
                refine ⟨114673999037887083061841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1223189323070795552659637 114673999037887083061841)
                ·
                  refine ⟨86005499278415312296381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114673999037887083061841 86005499278415312296381)
                  ·
                    refine ⟨32252062229405742111143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86005499278415312296381 32252062229405742111143)
                    ·
                      rfl

theorem cell22_94216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_94216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94216 prefixEnd_94216 := by exact prefixLift 94216
  have htrace : WordTrace (prefixWord ++ tailWord_94216) baseStart_94216 baseEnd_94216 := by
    simpa [prefixWord, tailWord_94216, baseEnd_94216] using wordTrace_append hprefix tailTrace_94216
  have hstable : (prefixWord ++ tailWord_94216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94216).length < 2 ^ (prefixWord ++ tailWord_94216).sum := by decide
  have hdescent : baseEnd_94216 < baseStart_94216 := by decide
  rcases family_descends (prefixWord ++ tailWord_94216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94231 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 1, 6]
def baseStart_94231 : Nat := 118140960795 + 94231 * 2 ^ 59
def prefixEnd_94231 : Nat := 4983230072969 + 3 ^ 40 * 94231 * 2
def baseEnd_94231 : Nat := 32257197035950702986097

theorem tailTrace_94231 : CollatzResearch.WordTrace tailWord_94231 prefixEnd_94231 32257197035950702986097 := by
  unfold tailWord_94231
  simp only [CollatzResearch.WordTrace]
  refine ⟨3436886921624655218650547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2291257947749770145767031 3436886921624655218650547)
  ·
    refine ⟨5155330382436982827975821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3436886921624655218650547 5155330382436982827975821)
    ·
      refine ⟨1933248893413868560490933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5155330382436982827975821 1933248893413868560490933)
      ·
        refine ⟨181242083757550177546025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1933248893413868560490933 181242083757550177546025)
        ·
          refine ⟨135931562818162633159519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181242083757550177546025 135931562818162633159519)
          ·
            refine ⟨203897344227243949739279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135931562818162633159519 203897344227243949739279)
            ·
              refine ⟨305846016340865924608919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203897344227243949739279 305846016340865924608919)
              ·
                refine ⟨458769024511298886913379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305846016340865924608919 458769024511298886913379)
                ·
                  refine ⟨688153536766948330370069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 458769024511298886913379 688153536766948330370069)
                  ·
                    refine ⟨32257197035950702986097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 688153536766948330370069 32257197035950702986097)
                    ·
                      rfl

theorem cell22_94231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_94231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94231 prefixEnd_94231 := by exact prefixLift 94231
  have htrace : WordTrace (prefixWord ++ tailWord_94231) baseStart_94231 baseEnd_94231 := by
    simpa [prefixWord, tailWord_94231, baseEnd_94231] using wordTrace_append hprefix tailTrace_94231
  have hstable : (prefixWord ++ tailWord_94231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94231).length < 2 ^ (prefixWord ++ tailWord_94231).sum := by decide
  have hdescent : baseEnd_94231 < baseStart_94231 := by decide
  rcases family_descends (prefixWord ++ tailWord_94231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94250 : List Nat := [3, 1, 4, 1, 2, 3, 1, 2, 2, 3]
def baseStart_94250 : Nat := 118140960795 + 94250 * 2 ^ 59
def prefixEnd_94250 : Nat := 4983230072969 + 3 ^ 40 * 94250 * 2
def baseEnd_94250 : Nat := 32263701124240986761039

theorem tailTrace_94250 : CollatzResearch.WordTrace tailWord_94250 prefixEnd_94250 32263701124240986761039 := by
  unfold tailWord_94250
  simp only [CollatzResearch.WordTrace]
  refine ⟨859394977138955365898051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2291719939037214309061469 859394977138955365898051)
  ·
    refine ⟨1289092465708433048847077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 859394977138955365898051 1289092465708433048847077)
    ·
      refine ⟨241704837320331196658827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1289092465708433048847077 241704837320331196658827)
      ·
        refine ⟨362557255980496794988241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241704837320331196658827 362557255980496794988241)
        ·
          refine ⟨271917941985372596241181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362557255980496794988241 271917941985372596241181)
          ·
            refine ⟨101969228244514723590443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271917941985372596241181 101969228244514723590443)
            ·
              refine ⟨152953842366772085385665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101969228244514723590443 152953842366772085385665)
              ·
                refine ⟨114715381775079064039249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152953842366772085385665 114715381775079064039249)
                ·
                  refine ⟨86036536331309298029437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114715381775079064039249 86036536331309298029437)
                  ·
                    refine ⟨32263701124240986761039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86036536331309298029437 32263701124240986761039)
                    ·
                      rfl

theorem cell22_94250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_94250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94250 prefixEnd_94250 := by exact prefixLift 94250
  have htrace : WordTrace (prefixWord ++ tailWord_94250) baseStart_94250 baseEnd_94250 := by
    simpa [prefixWord, tailWord_94250, baseEnd_94250] using wordTrace_append hprefix tailTrace_94250
  have hstable : (prefixWord ++ tailWord_94250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94250).length < 2 ^ (prefixWord ++ tailWord_94250).sum := by decide
  have hdescent : baseEnd_94250 < baseStart_94250 := by decide
  rcases family_descends (prefixWord ++ tailWord_94250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94261 : List Nat := [1, 3, 3, 1, 1, 1, 3, 3, 3, 3]
def baseStart_94261 : Nat := 118140960795 + 94261 * 2 ^ 59
def prefixEnd_94261 : Nat := 4983230072969 + 3 ^ 40 * 94261 * 2
def baseEnd_94261 : Nat := 32267466649040624736005

theorem tailTrace_94261 : CollatzResearch.WordTrace tailWord_94261 prefixEnd_94261 32267466649040624736005 := by
  unfold tailWord_94261
  simp only [CollatzResearch.WordTrace]
  refine ⟨3437981111515970342242637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2291987407677313561495091 3437981111515970342242637)
  ·
    refine ⟨1289242916818488878340989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3437981111515970342242637 1289242916818488878340989)
    ·
      refine ⟨483466093806933329377871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1289242916818488878340989 483466093806933329377871)
      ·
        refine ⟨725199140710399994066807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483466093806933329377871 725199140710399994066807)
        ·
          refine ⟨1087798711065599991100211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725199140710399994066807 1087798711065599991100211)
          ·
            refine ⟨1631698066598399986650317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087798711065599991100211 1631698066598399986650317)
            ·
              refine ⟨611886774974399994993869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1631698066598399986650317 611886774974399994993869)
              ·
                refine ⟨229457540615399998122701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 611886774974399994993869 229457540615399998122701)
                ·
                  refine ⟨86046577730774999296013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 229457540615399998122701 86046577730774999296013)
                  ·
                    refine ⟨32267466649040624736005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86046577730774999296013 32267466649040624736005)
                    ·
                      rfl

theorem cell22_94261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_94261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94261 prefixEnd_94261 := by exact prefixLift 94261
  have htrace : WordTrace (prefixWord ++ tailWord_94261) baseStart_94261 baseEnd_94261 := by
    simpa [prefixWord, tailWord_94261, baseEnd_94261] using wordTrace_append hprefix tailTrace_94261
  have hstable : (prefixWord ++ tailWord_94261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94261).length < 2 ^ (prefixWord ++ tailWord_94261).sum := by decide
  have hdescent : baseEnd_94261 < baseStart_94261 := by decide
  rcases family_descends (prefixWord ++ tailWord_94261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94368 : List Nat := [2, 1, 1, 4, 2, 2, 1, 4, 2, 3]
def baseStart_94368 : Nat := 118140960795 + 94368 * 2 ^ 59
def prefixEnd_94368 : Nat := 4983230072969 + 3 ^ 40 * 94368 * 2
def baseEnd_94368 : Nat := 32304094935728012310677

theorem tailTrace_94368 : CollatzResearch.WordTrace tailWord_94368 prefixEnd_94368 32304094935728012310677 := by
  unfold tailWord_94368
  simp only [CollatzResearch.WordTrace]
  refine ⟨1720941861064163808193879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2294589148085551744258505 1720941861064163808193879)
  ·
    refine ⟨2581412791596245712290819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1720941861064163808193879 2581412791596245712290819)
    ·
      refine ⟨3872119187394368568436229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2581412791596245712290819 3872119187394368568436229)
      ·
        refine ⟨726022347636444106581793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3872119187394368568436229 726022347636444106581793)
        ·
          refine ⟨544516760727333079936345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 726022347636444106581793 544516760727333079936345)
          ·
            refine ⟨408387570545499809952259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 544516760727333079936345 408387570545499809952259)
            ·
              refine ⟨612581355818249714928389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408387570545499809952259 612581355818249714928389)
              ·
                refine ⟨114859004215921821549073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 612581355818249714928389 114859004215921821549073)
                ·
                  refine ⟨86144253161941366161805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114859004215921821549073 86144253161941366161805)
                  ·
                    refine ⟨32304094935728012310677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86144253161941366161805 32304094935728012310677)
                    ·
                      rfl

theorem cell22_94368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 2, 3].length) (baseStart_94368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94368 prefixEnd_94368 := by exact prefixLift 94368
  have htrace : WordTrace (prefixWord ++ tailWord_94368) baseStart_94368 baseEnd_94368 := by
    simpa [prefixWord, tailWord_94368, baseEnd_94368] using wordTrace_append hprefix tailTrace_94368
  have hstable : (prefixWord ++ tailWord_94368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94368).length < 2 ^ (prefixWord ++ tailWord_94368).sum := by decide
  have hdescent : baseEnd_94368 < baseStart_94368 := by decide
  rcases family_descends (prefixWord ++ tailWord_94368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94370 : List Nat := [3, 3, 1, 3, 1, 2, 1, 4, 4]
def baseStart_94370 : Nat := 118140960795 + 94370 * 2 ^ 59
def prefixEnd_94370 : Nat := 4983230072969 + 3 ^ 40 * 94370 * 2
def baseEnd_94370 : Nat := 10768259858866891253557

theorem tailTrace_94370 : CollatzResearch.WordTrace tailWord_94370 prefixEnd_94370 10768259858866891253557 := by
  unfold tailWord_94370
  simp only [CollatzResearch.WordTrace]
  refine ⟨860489167030270489490141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2294637778747387971973709 860489167030270489490141)
  ·
    refine ⟨322683437636351433558803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 860489167030270489490141 322683437636351433558803)
    ·
      refine ⟨484025156454527150338205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322683437636351433558803 484025156454527150338205)
      ·
        refine ⟨181509433670447681376827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 484025156454527150338205 181509433670447681376827)
        ·
          refine ⟨272264150505671522065241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181509433670447681376827 272264150505671522065241)
          ·
            refine ⟨204198112879253641548931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272264150505671522065241 204198112879253641548931)
            ·
              refine ⟨306297169318880462323397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204198112879253641548931 306297169318880462323397)
              ·
                refine ⟨57430719247290086685637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 306297169318880462323397 57430719247290086685637)
                ·
                  refine ⟨10768259858866891253557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57430719247290086685637 10768259858866891253557)
                  ·
                    rfl

theorem cell22_94370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_94370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94370 prefixEnd_94370 := by exact prefixLift 94370
  have htrace : WordTrace (prefixWord ++ tailWord_94370) baseStart_94370 baseEnd_94370 := by
    simpa [prefixWord, tailWord_94370, baseEnd_94370] using wordTrace_append hprefix tailTrace_94370
  have hstable : (prefixWord ++ tailWord_94370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94370).length < 2 ^ (prefixWord ++ tailWord_94370).sum := by decide
  have hdescent : baseEnd_94370 < baseStart_94370 := by decide
  rcases family_descends (prefixWord ++ tailWord_94370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94443 : List Nat := [1, 1, 1, 1, 2, 5, 5, 1, 5]
def baseStart_94443 : Nat := 118140960795 + 94443 * 2 ^ 59
def prefixEnd_94443 : Nat := 4983230072969 + 3 ^ 40 * 94443 * 2
def baseEnd_94443 : Nat := 10776589656150938895149

theorem tailTrace_94443 : CollatzResearch.WordTrace tailWord_94443 prefixEnd_94443 10776589656150938895149 := by
  unfold tailWord_94443
  simp only [CollatzResearch.WordTrace]
  refine ⟨3444619196856615425367983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2296412797904410283578655 3444619196856615425367983)
  ·
    refine ⟨5166928795284923138051975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3444619196856615425367983 5166928795284923138051975)
    ·
      refine ⟨7750393192927384707077963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5166928795284923138051975 7750393192927384707077963)
      ·
        refine ⟨11625589789391077060616945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7750393192927384707077963 11625589789391077060616945)
        ·
          refine ⟨8719192342043307795462709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11625589789391077060616945 8719192342043307795462709)
          ·
            refine ⟨817424282066560105824629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8719192342043307795462709 817424282066560105824629)
            ·
              refine ⟨76633526443740009921059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 817424282066560105824629 76633526443740009921059)
              ·
                refine ⟨114950289665610014881589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76633526443740009921059 114950289665610014881589)
                ·
                  refine ⟨10776589656150938895149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114950289665610014881589 10776589656150938895149)
                  ·
                    rfl

theorem cell22_94443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 5].length) (baseStart_94443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94443 prefixEnd_94443 := by exact prefixLift 94443
  have htrace : WordTrace (prefixWord ++ tailWord_94443) baseStart_94443 baseEnd_94443 := by
    simpa [prefixWord, tailWord_94443, baseEnd_94443] using wordTrace_append hprefix tailTrace_94443
  have hstable : (prefixWord ++ tailWord_94443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94443).length < 2 ^ (prefixWord ++ tailWord_94443).sum := by decide
  have hdescent : baseEnd_94443 < baseStart_94443 := by decide
  rcases family_descends (prefixWord ++ tailWord_94443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94456 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 3, 4]
def baseStart_94456 : Nat := 118140960795 + 94456 * 2 ^ 59
def prefixEnd_94456 : Nat := 4983230072969 + 3 ^ 40 * 94456 * 2
def baseEnd_94456 : Nat := 32334219134125116110407

theorem tailTrace_94456 : CollatzResearch.WordTrace tailWord_94456 prefixEnd_94456 32334219134125116110407 := by
  unfold tailWord_94456
  simp only [CollatzResearch.WordTrace]
  refine ⟨1722546672904759322795611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2296728897206345763727481 1722546672904759322795611)
  ·
    refine ⟨2583820009357138984193417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1722546672904759322795611 2583820009357138984193417)
    ·
      refine ⟨1937865007017854238145063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2583820009357138984193417 1937865007017854238145063)
      ·
        refine ⟨2906797510526781357217595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1937865007017854238145063 2906797510526781357217595)
        ·
          refine ⟨4360196265790172035826393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2906797510526781357217595 4360196265790172035826393)
          ·
            refine ⟨3270147199342629026869795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4360196265790172035826393 3270147199342629026869795)
            ·
              refine ⟨4905220799013943540304693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3270147199342629026869795 4905220799013943540304693)
              ·
                refine ⟨459864449907557206903565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4905220799013943540304693 459864449907557206903565)
                ·
                  refine ⟨172449168715333952588837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 459864449907557206903565 172449168715333952588837)
                  ·
                    refine ⟨32334219134125116110407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 172449168715333952588837 32334219134125116110407)
                    ·
                      rfl

theorem cell22_94456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_94456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94456 prefixEnd_94456 := by exact prefixLift 94456
  have htrace : WordTrace (prefixWord ++ tailWord_94456) baseStart_94456 baseEnd_94456 := by
    simpa [prefixWord, tailWord_94456, baseEnd_94456] using wordTrace_append hprefix tailTrace_94456
  have hstable : (prefixWord ++ tailWord_94456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94456).length < 2 ^ (prefixWord ++ tailWord_94456).sum := by decide
  have hdescent : baseEnd_94456 < baseStart_94456 := by decide
  rcases family_descends (prefixWord ++ tailWord_94456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94473 : List Nat := [1, 2, 1, 1, 3, 4, 2, 3, 1, 4]
def baseStart_94473 : Nat := 118140960795 + 94473 * 2 ^ 59
def prefixEnd_94473 : Nat := 4983230072969 + 3 ^ 40 * 94473 * 2
def baseEnd_94473 : Nat := 32340038581542738435355

theorem tailTrace_94473 : CollatzResearch.WordTrace tailWord_94473 prefixEnd_94473 32340038581542738435355 := by
  unfold tailWord_94473
  simp only [CollatzResearch.WordTrace]
  refine ⟨3445713386747930548960073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2297142257831953699306715 3445713386747930548960073)
  ·
    refine ⟨2584285040060947911720055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3445713386747930548960073 2584285040060947911720055)
    ·
      refine ⟨3876427560091421867580083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2584285040060947911720055 3876427560091421867580083)
      ·
        refine ⟨5814641340137132801370125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3876427560091421867580083 5814641340137132801370125)
        ·
          refine ⟨2180490502551424800513797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5814641340137132801370125 2180490502551424800513797)
          ·
            refine ⟨408841969228392150096337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2180490502551424800513797 408841969228392150096337)
            ·
              refine ⟨306631476921294112572253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408841969228392150096337 306631476921294112572253)
              ·
                refine ⟨114986803845485292214595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306631476921294112572253 114986803845485292214595)
                ·
                  refine ⟨172480205768227938321893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114986803845485292214595 172480205768227938321893)
                  ·
                    refine ⟨32340038581542738435355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 172480205768227938321893 32340038581542738435355)
                    ·
                      rfl

theorem cell22_94473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 4].length) (baseStart_94473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94473 prefixEnd_94473 := by exact prefixLift 94473
  have htrace : WordTrace (prefixWord ++ tailWord_94473) baseStart_94473 baseEnd_94473 := by
    simpa [prefixWord, tailWord_94473, baseEnd_94473] using wordTrace_append hprefix tailTrace_94473
  have hstable : (prefixWord ++ tailWord_94473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94473).length < 2 ^ (prefixWord ++ tailWord_94473).sum := by decide
  have hdescent : baseEnd_94473 < baseStart_94473 := by decide
  rcases family_descends (prefixWord ++ tailWord_94473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94494 : List Nat := [4, 3, 2, 1, 1, 3, 2, 1, 5]
def baseStart_94494 : Nat := 118140960795 + 94494 * 2 ^ 59
def prefixEnd_94494 : Nat := 4983230072969 + 3 ^ 40 * 94494 * 2
def baseEnd_94494 : Nat := 10782409103568561220097

theorem tailTrace_94494 : CollatzResearch.WordTrace tailWord_94494 prefixEnd_94494 10782409103568561220097 := by
  unfold tailWord_94494
  simp only [CollatzResearch.WordTrace]
  refine ⟨430809914958981391934317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2297652879781234090316357 430809914958981391934317)
  ·
    refine ⟨161553718109618021975369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 430809914958981391934317 161553718109618021975369)
    ·
      refine ⟨121165288582213516481527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161553718109618021975369 121165288582213516481527)
      ·
        refine ⟨181747932873320274722291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121165288582213516481527 181747932873320274722291)
        ·
          refine ⟨272621899309980412083437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181747932873320274722291 272621899309980412083437)
          ·
            refine ⟨102233212241242654531289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 272621899309980412083437 102233212241242654531289)
            ·
              refine ⟨76674909180931990898467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102233212241242654531289 76674909180931990898467)
              ·
                refine ⟨115012363771397986347701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76674909180931990898467 115012363771397986347701)
                ·
                  refine ⟨10782409103568561220097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115012363771397986347701 10782409103568561220097)
                  ·
                    rfl

theorem cell22_94494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_94494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94494 prefixEnd_94494 := by exact prefixLift 94494
  have htrace : WordTrace (prefixWord ++ tailWord_94494) baseStart_94494 baseEnd_94494 := by
    simpa [prefixWord, tailWord_94494, baseEnd_94494] using wordTrace_append hprefix tailTrace_94494
  have hstable : (prefixWord ++ tailWord_94494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94494).length < 2 ^ (prefixWord ++ tailWord_94494).sum := by decide
  have hdescent : baseEnd_94494 < baseStart_94494 := by decide
  rcases family_descends (prefixWord ++ tailWord_94494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94561 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 11]
def baseStart_94561 : Nat := 118140960795 + 94561 * 2 ^ 59
def prefixEnd_94561 : Nat := 4983230072969 + 3 ^ 40 * 94561 * 2
def baseEnd_94561 : Nat := 10790054259979947411695

theorem tailTrace_94561 : CollatzResearch.WordTrace tailWord_94561 prefixEnd_94561 10790054259979947411695 := by
  unfold tailWord_94561
  simp only [CollatzResearch.WordTrace]
  refine ⟨3448923010429121578163537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2299282006952747718775691 3448923010429121578163537)
  ·
    refine ⟨2586692257821841183622653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3448923010429121578163537 2586692257821841183622653)
    ·
      refine ⟨970009596683190443858495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2586692257821841183622653 970009596683190443858495)
      ·
        refine ⟨1455014395024785665787743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 970009596683190443858495 1455014395024785665787743)
        ·
          refine ⟨2182521592537178498681615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1455014395024785665787743 2182521592537178498681615)
          ·
            refine ⟨3273782388805767748022423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2182521592537178498681615 3273782388805767748022423)
            ·
              refine ⟨4910673583208651622033635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3273782388805767748022423 4910673583208651622033635)
              ·
                refine ⟨7366010374812977433050453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4910673583208651622033635 7366010374812977433050453)
                ·
                  refine ⟨10790054259979947411695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 7366010374812977433050453 10790054259979947411695)
                  ·
                    rfl

theorem cell22_94561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 11].length) (baseStart_94561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94561 prefixEnd_94561 := by exact prefixLift 94561
  have htrace : WordTrace (prefixWord ++ tailWord_94561) baseStart_94561 baseEnd_94561 := by
    simpa [prefixWord, tailWord_94561, baseEnd_94561] using wordTrace_append hprefix tailTrace_94561
  have hstable : (prefixWord ++ tailWord_94561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94561).length < 2 ^ (prefixWord ++ tailWord_94561).sum := by decide
  have hdescent : baseEnd_94561 < baseStart_94561 := by decide
  rcases family_descends (prefixWord ++ tailWord_94561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94565 : List Nat := [1, 3, 1, 3, 1, 4, 1, 2, 3, 3]
def baseStart_94565 : Nat := 118140960795 + 94565 * 2 ^ 59
def prefixEnd_94565 : Nat := 4983230072969 + 3 ^ 40 * 94565 * 2
def baseEnd_94565 : Nat := 32371532061685165135073

theorem tailTrace_94565 : CollatzResearch.WordTrace tailWord_94565 prefixEnd_94565 32371532061685165135073 := by
  unfold tailWord_94565
  simp only [CollatzResearch.WordTrace]
  refine ⟨3449068902414630261309149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2299379268276420174206099 3449068902414630261309149)
  ·
    refine ⟨1293400838405486347990931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3449068902414630261309149 1293400838405486347990931)
    ·
      refine ⟨1940101257608229521986397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1293400838405486347990931 1940101257608229521986397)
      ·
        refine ⟨727537971603086070744899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1940101257608229521986397 727537971603086070744899)
        ·
          refine ⟨1091306957404629106117349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 727537971603086070744899 1091306957404629106117349)
          ·
            refine ⟨204620054513367957397003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1091306957404629106117349 204620054513367957397003)
            ·
              refine ⟨306930081770051936095505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204620054513367957397003 306930081770051936095505)
              ·
                refine ⟨230197561327538952071629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 306930081770051936095505 230197561327538952071629)
                ·
                  refine ⟨86324085497827107026861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 230197561327538952071629 86324085497827107026861)
                  ·
                    refine ⟨32371532061685165135073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86324085497827107026861 32371532061685165135073)
                    ·
                      rfl

theorem cell22_94565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 3].length) (baseStart_94565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94565 prefixEnd_94565 := by exact prefixLift 94565
  have htrace : WordTrace (prefixWord ++ tailWord_94565) baseStart_94565 baseEnd_94565 := by
    simpa [prefixWord, tailWord_94565, baseEnd_94565] using wordTrace_append hprefix tailTrace_94565
  have hstable : (prefixWord ++ tailWord_94565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94565).length < 2 ^ (prefixWord ++ tailWord_94565).sum := by decide
  have hdescent : baseEnd_94565 < baseStart_94565 := by decide
  rcases family_descends (prefixWord ++ tailWord_94565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94623 : List Nat := [1, 1, 2, 5, 1, 1, 1, 4, 6]
def baseStart_94623 : Nat := 118140960795 + 94623 * 2 ^ 59
def prefixEnd_94623 : Nat := 4983230072969 + 3 ^ 40 * 94623 * 2
def baseEnd_94623 : Nat := 10797128882330782394965

theorem tailTrace_94623 : CollatzResearch.WordTrace tailWord_94623 prefixEnd_94623 10797128882330782394965 := by
  unfold tailWord_94623
  simp only [CollatzResearch.WordTrace]
  refine ⟨3451184336204506166920523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2300789557469670777947015 3451184336204506166920523)
  ·
    refine ⟨5176776504306759250380785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3451184336204506166920523 5176776504306759250380785)
    ·
      refine ⟨3882582378230069437785589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5176776504306759250380785 3882582378230069437785589)
      ·
        refine ⟨363992097959069009792399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3882582378230069437785589 363992097959069009792399)
        ·
          refine ⟨545988146938603514688599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363992097959069009792399 545988146938603514688599)
          ·
            refine ⟨818982220407905272032899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545988146938603514688599 818982220407905272032899)
            ·
              refine ⟨1228473330611857908049349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818982220407905272032899 1228473330611857908049349)
              ·
                refine ⟨230338749489723357759253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1228473330611857908049349 230338749489723357759253)
                ·
                  refine ⟨10797128882330782394965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 230338749489723357759253 10797128882330782394965)
                  ·
                    rfl

theorem cell22_94623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 6].length) (baseStart_94623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94623 prefixEnd_94623 := by exact prefixLift 94623
  have htrace : WordTrace (prefixWord ++ tailWord_94623) baseStart_94623 baseEnd_94623 := by
    simpa [prefixWord, tailWord_94623, baseEnd_94623] using wordTrace_append hprefix tailTrace_94623
  have hstable : (prefixWord ++ tailWord_94623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94623).length < 2 ^ (prefixWord ++ tailWord_94623).sum := by decide
  have hdescent : baseEnd_94623 < baseStart_94623 := by decide
  rcases family_descends (prefixWord ++ tailWord_94623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94713 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 7]
def baseStart_94713 : Nat := 118140960795 + 94713 * 2 ^ 59
def prefixEnd_94713 : Nat := 4983230072969 + 3 ^ 40 * 94713 * 2
def baseEnd_94713 : Nat := 10807398495420704144873

theorem tailTrace_94713 : CollatzResearch.WordTrace tailWord_94713 prefixEnd_94713 10807398495420704144873 := by
  unfold tailWord_94713
  simp only [CollatzResearch.WordTrace]
  refine ⟨3454466905878451537696793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2302977937252301025131195 3454466905878451537696793)
  ·
    refine ⟨2590850179408838653272595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3454466905878451537696793 2590850179408838653272595)
    ·
      refine ⟨3886275269113257979908893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2590850179408838653272595 3886275269113257979908893)
      ·
        refine ⟨1457353225917471742465835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3886275269113257979908893 1457353225917471742465835)
        ·
          refine ⟨2186029838876207613698753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1457353225917471742465835 2186029838876207613698753)
          ·
            refine ⟨1639522379157155710274065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2186029838876207613698753 1639522379157155710274065)
            ·
              refine ⟨1229641784367866782705549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1639522379157155710274065 1229641784367866782705549)
              ·
                refine ⟨461115669137950043514581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1229641784367866782705549 461115669137950043514581)
                ·
                  refine ⟨10807398495420704144873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 461115669137950043514581 10807398495420704144873)
                  ·
                    rfl

theorem cell22_94713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 7].length) (baseStart_94713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94713 prefixEnd_94713 := by exact prefixLift 94713
  have htrace : WordTrace (prefixWord ++ tailWord_94713) baseStart_94713 baseEnd_94713 := by
    simpa [prefixWord, tailWord_94713, baseEnd_94713] using wordTrace_append hprefix tailTrace_94713
  have hstable : (prefixWord ++ tailWord_94713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94713).length < 2 ^ (prefixWord ++ tailWord_94713).sum := by decide
  have hdescent : baseEnd_94713 < baseStart_94713 := by decide
  rcases family_descends (prefixWord ++ tailWord_94713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94730 : List Nat := [3, 1, 2, 2, 2, 1, 1, 5, 5]
def baseStart_94730 : Nat := 118140960795 + 94730 * 2 ^ 59
def prefixEnd_94730 : Nat := 4983230072969 + 3 ^ 40 * 94730 * 2
def baseEnd_94730 : Nat := 10809338311226578253189

theorem tailTrace_94730 : CollatzResearch.WordTrace tailWord_94730 prefixEnd_94730 10809338311226578253189 := by
  unfold tailWord_94730
  simp only [CollatzResearch.WordTrace]
  refine ⟨863771736704215860266411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2303391297877908960710429 863771736704215860266411)
  ·
    refine ⟨1295657605056323790399617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 863771736704215860266411 1295657605056323790399617)
    ·
      refine ⟨971743203792242842799713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1295657605056323790399617 971743203792242842799713)
      ·
        refine ⟨728807402844182132099785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 971743203792242842799713 728807402844182132099785)
        ·
          refine ⟨546605552133136599074839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 728807402844182132099785 546605552133136599074839)
          ·
            refine ⟨819908328199704898612259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546605552133136599074839 819908328199704898612259)
            ·
              refine ⟨1229862492299557347918389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 819908328199704898612259 1229862492299557347918389)
              ·
                refine ⟨115299608653083501367349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1229862492299557347918389 115299608653083501367349)
                ·
                  refine ⟨10809338311226578253189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115299608653083501367349 10809338311226578253189)
                  ·
                    rfl

theorem cell22_94730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_94730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94730 prefixEnd_94730 := by exact prefixLift 94730
  have htrace : WordTrace (prefixWord ++ tailWord_94730) baseStart_94730 baseEnd_94730 := by
    simpa [prefixWord, tailWord_94730, baseEnd_94730] using wordTrace_append hprefix tailTrace_94730
  have hstable : (prefixWord ++ tailWord_94730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94730).length < 2 ^ (prefixWord ++ tailWord_94730).sum := by decide
  have hdescent : baseEnd_94730 < baseStart_94730 := by decide
  rcases family_descends (prefixWord ++ tailWord_94730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94775 : List Nat := [1, 1, 3, 1, 2, 3, 4, 1, 6]
def baseStart_94775 : Nat := 118140960795 + 94775 * 2 ^ 59
def prefixEnd_94775 : Nat := 4983230072969 + 3 ^ 40 * 94775 * 2
def baseEnd_94775 : Nat := 10814473117771539128143

theorem tailTrace_94775 : CollatzResearch.WordTrace tailWord_94775 prefixEnd_94775 10814473117771539128143 := by
  unfold tailWord_94775
  simp only [CollatzResearch.WordTrace]
  refine ⟨3456728231653836126453779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2304485487769224084302519 3456728231653836126453779)
  ·
    refine ⟨5185092347480754189680669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3456728231653836126453779 5185092347480754189680669)
    ·
      refine ⟨1944409630305282821130251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5185092347480754189680669 1944409630305282821130251)
      ·
        refine ⟨2916614445457924231695377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1944409630305282821130251 2916614445457924231695377)
        ·
          refine ⟨2187460834093443173771533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2916614445457924231695377 2187460834093443173771533)
          ·
            refine ⟨820297812785041190164325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2187460834093443173771533 820297812785041190164325)
            ·
              refine ⟨153805839897195223155811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 820297812785041190164325 153805839897195223155811)
              ·
                refine ⟨230708759845792834733717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153805839897195223155811 230708759845792834733717)
                ·
                  refine ⟨10814473117771539128143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 230708759845792834733717 10814473117771539128143)
                  ·
                    rfl

theorem cell22_94775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 6].length) (baseStart_94775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94775 prefixEnd_94775 := by exact prefixLift 94775
  have htrace : WordTrace (prefixWord ++ tailWord_94775) baseStart_94775 baseEnd_94775 := by
    simpa [prefixWord, tailWord_94775, baseEnd_94775] using wordTrace_append hprefix tailTrace_94775
  have hstable : (prefixWord ++ tailWord_94775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94775).length < 2 ^ (prefixWord ++ tailWord_94775).sum := by decide
  have hdescent : baseEnd_94775 < baseStart_94775 := by decide
  rcases family_descends (prefixWord ++ tailWord_94775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94805 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 1, 6]
def baseStart_94805 : Nat := 118140960795 + 94805 * 2 ^ 59
def prefixEnd_94805 : Nat := 4983230072969 + 3 ^ 40 * 94805 * 2
def baseEnd_94805 : Nat := 32453688966404539134337

theorem tailTrace_94805 : CollatzResearch.WordTrace tailWord_94805 prefixEnd_94805 32453688966404539134337 := by
  unfold tailWord_94805
  simp only [CollatzResearch.WordTrace]
  refine ⟨3457822421545151250045869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2305214947696767500030579 3457822421545151250045869)
  ·
    refine ⟨1296683408079431718767201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3457822421545151250045869 1296683408079431718767201)
    ·
      refine ⟨972512556059573789075401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1296683408079431718767201 972512556059573789075401)
      ·
        refine ⟨729384417044680341806551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 972512556059573789075401 729384417044680341806551)
        ·
          refine ⟨1094076625567020512709827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 729384417044680341806551 1094076625567020512709827)
          ·
            refine ⟨1641114938350530769064741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1094076625567020512709827 1641114938350530769064741)
            ·
              refine ⟨307709050940724519199639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1641114938350530769064741 307709050940724519199639)
              ·
                refine ⟨461563576411086778799459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307709050940724519199639 461563576411086778799459)
                ·
                  refine ⟨692345364616630168199189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 461563576411086778799459 692345364616630168199189)
                  ·
                    refine ⟨32453688966404539134337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 692345364616630168199189 32453688966404539134337)
                    ·
                      rfl

theorem cell22_94805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_94805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94805 prefixEnd_94805 := by exact prefixLift 94805
  have htrace : WordTrace (prefixWord ++ tailWord_94805) baseStart_94805 baseEnd_94805 := by
    simpa [prefixWord, tailWord_94805, baseEnd_94805] using wordTrace_append hprefix tailTrace_94805
  have hstable : (prefixWord ++ tailWord_94805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94805).length < 2 ^ (prefixWord ++ tailWord_94805).sum := by decide
  have hdescent : baseEnd_94805 < baseStart_94805 := by decide
  rcases family_descends (prefixWord ++ tailWord_94805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94841 : List Nat := [1, 2, 1, 3, 3, 4, 2, 1, 2, 3]
def baseStart_94841 : Nat := 118140960795 + 94841 * 2 ^ 59
def prefixEnd_94841 : Nat := 4983230072969 + 3 ^ 40 * 94841 * 2
def baseEnd_94841 : Nat := 32466012502112445234227

theorem tailTrace_94841 : CollatzResearch.WordTrace tailWord_94841 prefixEnd_94841 32466012502112445234227 := by
  unfold tailWord_94841
  simp only [CollatzResearch.WordTrace]
  refine ⟨3459135449414729398356377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2306090299609819598904251 3459135449414729398356377)
  ·
    refine ⟨2594351587061047048767283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3459135449414729398356377 2594351587061047048767283)
    ·
      refine ⟨3891527380591570573150925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2594351587061047048767283 3891527380591570573150925)
      ·
        refine ⟨1459322767721838964931597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3891527380591570573150925 1459322767721838964931597)
        ·
          refine ⟨547246037895689611849349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1459322767721838964931597 547246037895689611849349)
          ·
            refine ⟨102608632105441802221753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 547246037895689611849349 102608632105441802221753)
            ·
              refine ⟨76956474079081351666315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102608632105441802221753 76956474079081351666315)
              ·
                refine ⟨115434711118622027499473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76956474079081351666315 115434711118622027499473)
                ·
                  refine ⟨86576033338966520624605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115434711118622027499473 86576033338966520624605)
                  ·
                    refine ⟨32466012502112445234227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86576033338966520624605 32466012502112445234227)
                    ·
                      rfl

theorem cell22_94841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 2, 3].length) (baseStart_94841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94841 prefixEnd_94841 := by exact prefixLift 94841
  have htrace : WordTrace (prefixWord ++ tailWord_94841) baseStart_94841 baseEnd_94841 := by
    simpa [prefixWord, tailWord_94841, baseEnd_94841] using wordTrace_append hprefix tailTrace_94841
  have hstable : (prefixWord ++ tailWord_94841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94841).length < 2 ^ (prefixWord ++ tailWord_94841).sum := by decide
  have hdescent : baseEnd_94841 < baseStart_94841 := by decide
  rcases family_descends (prefixWord ++ tailWord_94841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94912 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 3, 4]
def baseStart_94912 : Nat := 118140960795 + 94912 * 2 ^ 59
def prefixEnd_94912 : Nat := 4983230072969 + 3 ^ 40 * 94912 * 2
def baseEnd_94912 : Nat := 32490317253091926709009

theorem tailTrace_94912 : CollatzResearch.WordTrace tailWord_94912 prefixEnd_94912 32490317253091926709009 := by
  unfold tailWord_94912
  simp only [CollatzResearch.WordTrace]
  refine ⟨1730862516078754262095495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2307816688105005682793993 1730862516078754262095495)
  ·
    refine ⟨2596293774118131393143243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1730862516078754262095495 2596293774118131393143243)
    ·
      refine ⟨3894440661177197089714865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2596293774118131393143243 3894440661177197089714865)
      ·
        refine ⟨2920830495882897817286149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3894440661177197089714865 2920830495882897817286149)
        ·
          refine ⟨547655717978043340741153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2920830495882897817286149 547655717978043340741153)
          ·
            refine ⟨410741788483532505555865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 547655717978043340741153 410741788483532505555865)
            ·
              refine ⟨308056341362649379166899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 410741788483532505555865 308056341362649379166899)
              ·
                refine ⟨462084512043974068750349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308056341362649379166899 462084512043974068750349)
                ·
                  refine ⟨173281692016490275781381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 462084512043974068750349 173281692016490275781381)
                  ·
                    refine ⟨32490317253091926709009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 173281692016490275781381 32490317253091926709009)
                    ·
                      rfl

theorem cell22_94912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 3, 4].length) (baseStart_94912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94912 prefixEnd_94912 := by exact prefixLift 94912
  have htrace : WordTrace (prefixWord ++ tailWord_94912) baseStart_94912 baseEnd_94912 := by
    simpa [prefixWord, tailWord_94912, baseEnd_94912] using wordTrace_append hprefix tailTrace_94912
  have hstable : (prefixWord ++ tailWord_94912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94912).length < 2 ^ (prefixWord ++ tailWord_94912).sum := by decide
  have hdescent : baseEnd_94912 < baseStart_94912 := by decide
  rcases family_descends (prefixWord ++ tailWord_94912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94933 : List Nat := [1, 3, 2, 5, 2, 1, 1, 2, 5]
def baseStart_94933 : Nat := 118140960795 + 94933 * 2 ^ 59
def prefixEnd_94933 : Nat := 4983230072969 + 3 ^ 40 * 94933 * 2
def baseEnd_94933 : Nat := 10832501994084957311315

theorem tailTrace_94933 : CollatzResearch.WordTrace tailWord_94933 prefixEnd_94933 10832501994084957311315 := by
  unfold tailWord_94933
  simp only [CollatzResearch.WordTrace]
  refine ⟨3462490965081429110705453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2308327310054286073803635 3462490965081429110705453)
  ·
    refine ⟨1298434111905535916514545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3462490965081429110705453 1298434111905535916514545)
    ·
      refine ⟨973825583929151937385909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1298434111905535916514545 973825583929151937385909)
      ·
        refine ⟨91296148493357994129929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 973825583929151937385909 91296148493357994129929)
        ·
          refine ⟨68472111370018495597447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91296148493357994129929 68472111370018495597447)
          ·
            refine ⟨102708167055027743396171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68472111370018495597447 102708167055027743396171)
            ·
              refine ⟨154062250582541615094257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102708167055027743396171 154062250582541615094257)
              ·
                refine ⟨115546687936906211320693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154062250582541615094257 115546687936906211320693)
                ·
                  refine ⟨10832501994084957311315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115546687936906211320693 10832501994084957311315)
                  ·
                    rfl

theorem cell22_94933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 5].length) (baseStart_94933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94933 prefixEnd_94933 := by exact prefixLift 94933
  have htrace : WordTrace (prefixWord ++ tailWord_94933) baseStart_94933 baseEnd_94933 := by
    simpa [prefixWord, tailWord_94933, baseEnd_94933] using wordTrace_append hprefix tailTrace_94933
  have hstable : (prefixWord ++ tailWord_94933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94933).length < 2 ^ (prefixWord ++ tailWord_94933).sum := by decide
  have hdescent : baseEnd_94933 < baseStart_94933 := by decide
  rcases family_descends (prefixWord ++ tailWord_94933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94955 : List Nat := [1, 1, 1, 1, 2, 4, 1, 11]
def baseStart_94955 : Nat := 118140960795 + 94955 * 2 ^ 59
def prefixEnd_94955 : Nat := 4983230072969 + 3 ^ 40 * 94955 * 2
def baseEnd_94955 : Nat := 3611670781317127542653

theorem tailTrace_94955 : CollatzResearch.WordTrace tailWord_94955 prefixEnd_94955 3611670781317127542653 := by
  unfold tailWord_94955
  simp only [CollatzResearch.WordTrace]
  refine ⟨3463293371001726868006319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2308862247334484578670879 3463293371001726868006319)
  ·
    refine ⟨5194940056502590302009479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3463293371001726868006319 5194940056502590302009479)
    ·
      refine ⟨7792410084753885453014219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5194940056502590302009479 7792410084753885453014219)
      ·
        refine ⟨11688615127130828179521329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7792410084753885453014219 11688615127130828179521329)
        ·
          refine ⟨8766461345348121134640997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11688615127130828179521329 8766461345348121134640997)
          ·
            refine ⟨1643711502252772712745187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8766461345348121134640997 1643711502252772712745187)
            ·
              refine ⟨2465567253379159069117781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1643711502252772712745187 2465567253379159069117781)
              ·
                refine ⟨3611670781317127542653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 2465567253379159069117781 3611670781317127542653)
                ·
                  rfl

theorem cell22_94955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 11].length) (baseStart_94955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94955 prefixEnd_94955 := by exact prefixLift 94955
  have htrace : WordTrace (prefixWord ++ tailWord_94955) baseStart_94955 baseEnd_94955 := by
    simpa [prefixWord, tailWord_94955, baseEnd_94955] using wordTrace_append hprefix tailTrace_94955
  have hstable : (prefixWord ++ tailWord_94955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94955).length < 2 ^ (prefixWord ++ tailWord_94955).sum := by decide
  have hdescent : baseEnd_94955 < baseStart_94955 := by decide
  rcases family_descends (prefixWord ++ tailWord_94955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94957 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_94957 : Nat := 118140960795 + 94957 * 2 ^ 59
def prefixEnd_94957 : Nat := 4983230072969 + 3 ^ 40 * 94957 * 2
def baseEnd_94957 : Nat := 32505721672726809333871

theorem tailTrace_94957 : CollatzResearch.WordTrace tailWord_94957 prefixEnd_94957 32505721672726809333871 := by
  unfold tailWord_94957
  simp only [CollatzResearch.WordTrace]
  refine ⟨3463366316994481209579125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2308910877996320806386083 3463366316994481209579125)
  ·
    refine ⟨324690592218232613398043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3463366316994481209579125 324690592218232613398043)
    ·
      refine ⟨487035888327348920097065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324690592218232613398043 487035888327348920097065)
      ·
        refine ⟨365276916245511690072799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487035888327348920097065 365276916245511690072799)
        ·
          refine ⟨547915374368267535109199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365276916245511690072799 547915374368267535109199)
          ·
            refine ⟨821873061552401302663799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547915374368267535109199 821873061552401302663799)
            ·
              refine ⟨1232809592328601953995699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821873061552401302663799 1232809592328601953995699)
              ·
                refine ⟨1849214388492902930993549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1232809592328601953995699 1849214388492902930993549)
                ·
                  refine ⟨693455395684838599122581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1849214388492902930993549 693455395684838599122581)
                  ·
                    refine ⟨32505721672726809333871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 693455395684838599122581 32505721672726809333871)
                    ·
                      rfl

theorem cell22_94957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_94957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94957 prefixEnd_94957 := by exact prefixLift 94957
  have htrace : WordTrace (prefixWord ++ tailWord_94957) baseStart_94957 baseEnd_94957 := by
    simpa [prefixWord, tailWord_94957, baseEnd_94957] using wordTrace_append hprefix tailTrace_94957
  have hstable : (prefixWord ++ tailWord_94957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94957).length < 2 ^ (prefixWord ++ tailWord_94957).sum := by decide
  have hdescent : baseEnd_94957 < baseStart_94957 := by decide
  rcases family_descends (prefixWord ++ tailWord_94957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94959 : List Nat := [1, 1, 2, 1, 5, 4, 1, 1, 1, 5]
def baseStart_94959 : Nat := 118140960795 + 94959 * 2 ^ 59
def prefixEnd_94959 : Nat := 4983230072969 + 3 ^ 40 * 94959 * 2
def baseEnd_94959 : Nat := 32506406313599470783865

theorem tailTrace_94959 : CollatzResearch.WordTrace tailWord_94959 prefixEnd_94959 32506406313599470783865 := by
  unfold tailWord_94959
  simp only [CollatzResearch.WordTrace]
  refine ⟨3463439262987235551151931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2308959508658157034101287 3463439262987235551151931)
  ·
    refine ⟨5195158894480853326727897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3463439262987235551151931 5195158894480853326727897)
    ·
      refine ⟨3896369170860639995045923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5195158894480853326727897 3896369170860639995045923)
      ·
        refine ⟨5844553756290959992568885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3896369170860639995045923 5844553756290959992568885)
        ·
          refine ⟨547926914652277499303333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5844553756290959992568885 547926914652277499303333)
          ·
            refine ⟨102736296497302031119375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 547926914652277499303333 102736296497302031119375)
            ·
              refine ⟨154104444745953046679063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102736296497302031119375 154104444745953046679063)
              ·
                refine ⟨231156667118929570018595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154104444745953046679063 231156667118929570018595)
                ·
                  refine ⟨346735000678394355027893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231156667118929570018595 346735000678394355027893)
                  ·
                    refine ⟨32506406313599470783865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 346735000678394355027893 32506406313599470783865)
                    ·
                      rfl

theorem cell22_94959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 5].length) (baseStart_94959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94959 prefixEnd_94959 := by exact prefixLift 94959
  have htrace : WordTrace (prefixWord ++ tailWord_94959) baseStart_94959 baseEnd_94959 := by
    simpa [prefixWord, tailWord_94959, baseEnd_94959] using wordTrace_append hprefix tailTrace_94959
  have hstable : (prefixWord ++ tailWord_94959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94959).length < 2 ^ (prefixWord ++ tailWord_94959).sum := by decide
  have hdescent : baseEnd_94959 < baseStart_94959 := by decide
  rcases family_descends (prefixWord ++ tailWord_94959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94972 : List Nat := [2, 2, 2, 1, 3, 3, 1, 8]
def baseStart_94972 : Nat := 118140960795 + 94972 * 2 ^ 59
def prefixEnd_94972 : Nat := 4983230072969 + 3 ^ 40 * 94972 * 2
def baseEnd_94972 : Nat := 3612317386585752245425

theorem tailTrace_94972 : CollatzResearch.WordTrace tailWord_94972 prefixEnd_94972 3612317386585752245425 := by
  unfold tailWord_94972
  simp only [CollatzResearch.WordTrace]
  refine ⟨1731956705970069385687585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2309275607960092514250113 1731956705970069385687585)
  ·
    refine ⟨1298967529477552039265689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1731956705970069385687585 1298967529477552039265689)
    ·
      refine ⟨974225647108164029449267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1298967529477552039265689 974225647108164029449267)
      ·
        refine ⟨1461338470662246044173901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 974225647108164029449267 1461338470662246044173901)
        ·
          refine ⟨548001926498342266565213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1461338470662246044173901 548001926498342266565213)
          ·
            refine ⟨205500722436878349961955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 548001926498342266565213 205500722436878349961955)
            ·
              refine ⟨308251083655317524942933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205500722436878349961955 308251083655317524942933)
              ·
                refine ⟨3612317386585752245425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 308251083655317524942933 3612317386585752245425)
                ·
                  rfl

theorem cell22_94972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 8].length) (baseStart_94972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94972 prefixEnd_94972 := by exact prefixLift 94972
  have htrace : WordTrace (prefixWord ++ tailWord_94972) baseStart_94972 baseEnd_94972 := by
    simpa [prefixWord, tailWord_94972, baseEnd_94972] using wordTrace_append hprefix tailTrace_94972
  have hstable : (prefixWord ++ tailWord_94972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94972).length < 2 ^ (prefixWord ++ tailWord_94972).sum := by decide
  have hdescent : baseEnd_94972 < baseStart_94972 := by decide
  rcases family_descends (prefixWord ++ tailWord_94972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94974 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_94974 : Nat := 118140960795 + 94974 * 2 ^ 59
def prefixEnd_94974 : Nat := 4983230072969 + 3 ^ 40 * 94974 * 2
def baseEnd_94974 : Nat := 32511541120144431658819

theorem tailTrace_94974 : CollatzResearch.WordTrace tailWord_94974 prefixEnd_94974 32511541120144431658819 := by
  unfold tailWord_94974
  simp only [CollatzResearch.WordTrace]
  refine ⟨432998294741611639118497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2309324238621928741965317 432998294741611639118497)
  ·
    refine ⟨324748721056208729338873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 432998294741611639118497 324748721056208729338873)
    ·
      refine ⟨243561540792156547004155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324748721056208729338873 243561540792156547004155)
      ·
        refine ⟨365342311188234820506233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243561540792156547004155 365342311188234820506233)
        ·
          refine ⟨274006733391176115379675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365342311188234820506233 274006733391176115379675)
          ·
            refine ⟨411010100086764173069513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274006733391176115379675 411010100086764173069513)
            ·
              refine ⟨308257575065073129802135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411010100086764173069513 308257575065073129802135)
              ·
                refine ⟨462386362597609694703203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308257575065073129802135 462386362597609694703203)
                ·
                  refine ⟨693579543896414542054805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 462386362597609694703203 693579543896414542054805)
                  ·
                    refine ⟨32511541120144431658819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 693579543896414542054805 32511541120144431658819)
                    ·
                      rfl

theorem cell22_94974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_94974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94974 prefixEnd_94974 := by exact prefixLift 94974
  have htrace : WordTrace (prefixWord ++ tailWord_94974) baseStart_94974 baseEnd_94974 := by
    simpa [prefixWord, tailWord_94974, baseEnd_94974] using wordTrace_append hprefix tailTrace_94974
  have hstable : (prefixWord ++ tailWord_94974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94974).length < 2 ^ (prefixWord ++ tailWord_94974).sum := by decide
  have hdescent : baseEnd_94974 < baseStart_94974 := by decide
  rcases family_descends (prefixWord ++ tailWord_94974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94978 : List Nat := [3, 4, 1, 1, 1, 4, 1, 3, 4]
def baseStart_94978 : Nat := 118140960795 + 94978 * 2 ^ 59
def prefixEnd_94978 : Nat := 4983230072969 + 3 ^ 40 * 94978 * 2
def baseEnd_94978 : Nat := 10837636800629918186269

theorem tailTrace_94978 : CollatzResearch.WordTrace tailWord_94978 prefixEnd_94978 10837636800629918186269 := by
  unfold tailWord_94978
  simp only [CollatzResearch.WordTrace]
  refine ⟨866033062479600449023397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2309421499945601197395725 866033062479600449023397)
  ·
    refine ⟨162381199214925084191887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 866033062479600449023397 162381199214925084191887)
    ·
      refine ⟨243571798822387626287831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162381199214925084191887 243571798822387626287831)
      ·
        refine ⟨365357698233581439431747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243571798822387626287831 365357698233581439431747)
        ·
          refine ⟨548036547350372159147621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365357698233581439431747 548036547350372159147621)
          ·
            refine ⟨102756852628194779840179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 548036547350372159147621 102756852628194779840179)
            ·
              refine ⟨154135278942292169760269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102756852628194779840179 154135278942292169760269)
              ·
                refine ⟨57800729603359563660101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154135278942292169760269 57800729603359563660101)
                ·
                  refine ⟨10837636800629918186269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57800729603359563660101 10837636800629918186269)
                  ·
                    rfl

theorem cell22_94978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_94978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_94978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_94978 prefixEnd_94978 := by exact prefixLift 94978
  have htrace : WordTrace (prefixWord ++ tailWord_94978) baseStart_94978 baseEnd_94978 := by
    simpa [prefixWord, tailWord_94978, baseEnd_94978] using wordTrace_append hprefix tailTrace_94978
  have hstable : (prefixWord ++ tailWord_94978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94978).length < 2 ^ (prefixWord ++ tailWord_94978).sum := by decide
  have hdescent : baseEnd_94978 < baseStart_94978 := by decide
  rcases family_descends (prefixWord ++ tailWord_94978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95002 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 2, 6]
def baseStart_95002 : Nat := 118140960795 + 95002 * 2 ^ 59
def prefixEnd_95002 : Nat := 4983230072969 + 3 ^ 40 * 95002 * 2
def baseEnd_95002 : Nat := 32521126092361691958733

theorem tailTrace_95002 : CollatzResearch.WordTrace tailWord_95002 prefixEnd_95002 32521126092361691958733 := by
  unfold tailWord_95002
  simp only [CollatzResearch.WordTrace]
  refine ⟨866251900457863473741815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2310005067887635929978173 866251900457863473741815)
  ·
    refine ⟨1299377850686795210612723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 866251900457863473741815 1299377850686795210612723)
    ·
      refine ⟨1949066776030192815919085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1299377850686795210612723 1949066776030192815919085)
      ·
        refine ⟨730900041011322305969657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1949066776030192815919085 730900041011322305969657)
        ·
          refine ⟨548175030758491729477243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 730900041011322305969657 548175030758491729477243)
          ·
            refine ⟨822262546137737594215865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548175030758491729477243 822262546137737594215865)
            ·
              refine ⟨616696909603303195661899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 822262546137737594215865 616696909603303195661899)
              ·
                refine ⟨925045364404954793492849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616696909603303195661899 925045364404954793492849)
                ·
                  refine ⟨693784023303716095119637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 925045364404954793492849 693784023303716095119637)
                  ·
                    refine ⟨32521126092361691958733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 693784023303716095119637 32521126092361691958733)
                    ·
                      rfl

theorem cell22_95002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_95002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_95002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_95002 prefixEnd_95002 := by exact prefixLift 95002
  have htrace : WordTrace (prefixWord ++ tailWord_95002) baseStart_95002 baseEnd_95002 := by
    simpa [prefixWord, tailWord_95002, baseEnd_95002] using wordTrace_append hprefix tailTrace_95002
  have hstable : (prefixWord ++ tailWord_95002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95002).length < 2 ^ (prefixWord ++ tailWord_95002).sum := by decide
  have hdescent : baseEnd_95002 < baseStart_95002 := by decide
  rcases family_descends (prefixWord ++ tailWord_95002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95017 : List Nat := [1, 2, 1, 1, 1, 1, 1, 9, 5]
def baseStart_95017 : Nat := 118140960795 + 95017 * 2 ^ 59
def prefixEnd_95017 : Nat := 4983230072969 + 3 ^ 40 * 95017 * 2
def baseEnd_95017 : Nat := 10842086966302217611229

theorem tailTrace_95017 : CollatzResearch.WordTrace tailWord_95017 prefixEnd_95017 10842086966302217611229 := by
  unfold tailWord_95017
  simp only [CollatzResearch.WordTrace]
  refine ⟨3465554696777111456763305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2310369797851407637842203 3465554696777111456763305)
  ·
    refine ⟨2599166022582833592572479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3465554696777111456763305 2599166022582833592572479)
    ·
      refine ⟨3898749033874250388858719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2599166022582833592572479 3898749033874250388858719)
      ·
        refine ⟨5848123550811375583288079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3898749033874250388858719 5848123550811375583288079)
        ·
          refine ⟨8772185326217063374932119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5848123550811375583288079 8772185326217063374932119)
          ·
            refine ⟨13158277989325595062398179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8772185326217063374932119 13158277989325595062398179)
            ·
              refine ⟨19737416983988392593597269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13158277989325595062398179 19737416983988392593597269)
              ·
                refine ⟨115648927640556987853109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19737416983988392593597269 115648927640556987853109)
                ·
                  refine ⟨10842086966302217611229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115648927640556987853109 10842086966302217611229)
                  ·
                    rfl

theorem cell22_95017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 5].length) (baseStart_95017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_95017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_95017 prefixEnd_95017 := by exact prefixLift 95017
  have htrace : WordTrace (prefixWord ++ tailWord_95017) baseStart_95017 baseEnd_95017 := by
    simpa [prefixWord, tailWord_95017, baseEnd_95017] using wordTrace_append hprefix tailTrace_95017
  have hstable : (prefixWord ++ tailWord_95017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95017).length < 2 ^ (prefixWord ++ tailWord_95017).sum := by decide
  have hdescent : baseEnd_95017 < baseStart_95017 := by decide
  rcases family_descends (prefixWord ++ tailWord_95017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95079 : List Nat := [1, 1, 5, 1, 2, 3, 1, 2, 6]
def baseStart_95079 : Nat := 118140960795 + 95079 * 2 ^ 59
def prefixEnd_95079 : Nat := 4983230072969 + 3 ^ 40 * 95079 * 2
def baseEnd_95079 : Nat := 10849161588653052594499

theorem tailTrace_95079 : CollatzResearch.WordTrace tailWord_95079 prefixEnd_95079 10849161588653052594499 := by
  unfold tailWord_95079
  simp only [CollatzResearch.WordTrace]
  refine ⟨3467816022552496045520291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2311877348368330697013527 3467816022552496045520291)
  ·
    refine ⟨5201724033828744068280437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3467816022552496045520291 5201724033828744068280437)
    ·
      refine ⟨487661628171444756401291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5201724033828744068280437 487661628171444756401291)
      ·
        refine ⟨731492442257167134601937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487661628171444756401291 731492442257167134601937)
        ·
          refine ⟨548619331692875350951453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 731492442257167134601937 548619331692875350951453)
          ·
            refine ⟨205732249384828256606795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 548619331692875350951453 205732249384828256606795)
            ·
              refine ⟨308598374077242384910193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205732249384828256606795 308598374077242384910193)
              ·
                refine ⟨231448780557931788682645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308598374077242384910193 231448780557931788682645)
                ·
                  refine ⟨10849161588653052594499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 231448780557931788682645 10849161588653052594499)
                  ·
                    rfl

theorem cell22_95079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 6].length) (baseStart_95079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_95079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_95079 prefixEnd_95079 := by exact prefixLift 95079
  have htrace : WordTrace (prefixWord ++ tailWord_95079) baseStart_95079 baseEnd_95079 := by
    simpa [prefixWord, tailWord_95079, baseEnd_95079] using wordTrace_append hprefix tailTrace_95079
  have hstable : (prefixWord ++ tailWord_95079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95079).length < 2 ^ (prefixWord ++ tailWord_95079).sum := by decide
  have hdescent : baseEnd_95079 < baseStart_95079 := by decide
  rcases family_descends (prefixWord ++ tailWord_95079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95107 : List Nat := [1, 1, 1, 3, 4, 1, 11]
def baseStart_95107 : Nat := 118140960795 + 95107 * 2 ^ 59
def prefixEnd_95107 : Nat := 4983230072969 + 3 ^ 40 * 95107 * 2
def baseEnd_95107 : Nat := 1205817397710237706793

theorem tailTrace_95107 : CollatzResearch.WordTrace tailWord_95107 prefixEnd_95107 1205817397710237706793 := by
  unfold tailWord_95107
  simp only [CollatzResearch.WordTrace]
  refine ⟨3468837266451056827539575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2312558177634037885026383 3468837266451056827539575)
  ·
    refine ⟨5203255899676585241309363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3468837266451056827539575 5203255899676585241309363)
    ·
      refine ⟨7804883849514877861964045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5203255899676585241309363 7804883849514877861964045)
      ·
        refine ⟨2926831443568079198236517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7804883849514877861964045 2926831443568079198236517)
        ·
          refine ⟨548780895669014849669347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2926831443568079198236517 548780895669014849669347)
          ·
            refine ⟨823171343503522274504021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548780895669014849669347 823171343503522274504021)
            ·
              refine ⟨1205817397710237706793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 823171343503522274504021 1205817397710237706793)
              ·
                rfl

theorem cell22_95107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 11].length) (baseStart_95107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_95107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_95107 prefixEnd_95107 := by exact prefixLift 95107
  have htrace : WordTrace (prefixWord ++ tailWord_95107) baseStart_95107 baseEnd_95107 := by
    simpa [prefixWord, tailWord_95107, baseEnd_95107] using wordTrace_append hprefix tailTrace_95107
  have hstable : (prefixWord ++ tailWord_95107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95107).length < 2 ^ (prefixWord ++ tailWord_95107).sum := by decide
  have hdescent : baseEnd_95107 < baseStart_95107 := by decide
  rcases family_descends (prefixWord ++ tailWord_95107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95111 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 4, 3]
def baseStart_95111 : Nat := 118140960795 + 95111 * 2 ^ 59
def prefixEnd_95111 : Nat := 4983230072969 + 3 ^ 40 * 95111 * 2
def baseEnd_95111 : Nat := 32558439019921740983399

theorem tailTrace_95111 : CollatzResearch.WordTrace tailWord_95111 prefixEnd_95111 32558439019921740983399 := by
  unfold tailWord_95111
  simp only [CollatzResearch.WordTrace]
  refine ⟨3468983158436565510685187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2312655438957710340456791 3468983158436565510685187)
  ·
    refine ⟨5203474737654848266027781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3468983158436565510685187 5203474737654848266027781)
    ·
      refine ⟨975651513310284049880209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5203474737654848266027781 975651513310284049880209)
      ·
        refine ⟨731738634982713037410157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 975651513310284049880209 731738634982713037410157)
        ·
          refine ⟨274401988118517389028809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 731738634982713037410157 274401988118517389028809)
          ·
            refine ⟨205801491088888041771607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274401988118517389028809 205801491088888041771607)
            ·
              refine ⟨308702236633332062657411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205801491088888041771607 308702236633332062657411)
              ·
                refine ⟨463053354949998093986117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308702236633332062657411 463053354949998093986117)
                ·
                  refine ⟨86822504053124642622397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 463053354949998093986117 86822504053124642622397)
                  ·
                    refine ⟨32558439019921740983399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86822504053124642622397 32558439019921740983399)
                    ·
                      rfl

theorem cell22_95111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_95111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_95111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_95111 prefixEnd_95111 := by exact prefixLift 95111
  have htrace : WordTrace (prefixWord ++ tailWord_95111) baseStart_95111 baseEnd_95111 := by
    simpa [prefixWord, tailWord_95111, baseEnd_95111] using wordTrace_append hprefix tailTrace_95111
  have hstable : (prefixWord ++ tailWord_95111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95111).length < 2 ^ (prefixWord ++ tailWord_95111).sum := by decide
  have hdescent : baseEnd_95111 < baseStart_95111 := by decide
  rcases family_descends (prefixWord ++ tailWord_95111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95124 : List Nat := [2, 4, 2, 1, 1, 1, 2, 9]
def baseStart_95124 : Nat := 118140960795 + 95124 * 2 ^ 59
def prefixEnd_95124 : Nat := 4983230072969 + 3 ^ 40 * 95124 * 2
def baseEnd_95124 : Nat := 3618098798399337823151

theorem tailTrace_95124 : CollatzResearch.WordTrace tailWord_95124 prefixEnd_95124 3618098798399337823151 := by
  unfold tailWord_95124
  simp only [CollatzResearch.WordTrace]
  refine ⟨1734728653694734365454213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2312971538259645820605617 1734728653694734365454213)
  ·
    refine ⟨325261622567762693522665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1734728653694734365454213 325261622567762693522665)
    ·
      refine ⟨243946216925822020141999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325261622567762693522665 243946216925822020141999)
      ·
        refine ⟨365919325388733030212999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243946216925822020141999 365919325388733030212999)
        ·
          refine ⟨548878988083099545319499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365919325388733030212999 548878988083099545319499)
          ·
            refine ⟨823318482124649317979249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548878988083099545319499 823318482124649317979249)
            ·
              refine ⟨617488861593486988484437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 823318482124649317979249 617488861593486988484437)
              ·
                refine ⟨3618098798399337823151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 617488861593486988484437 3618098798399337823151)
                ·
                  rfl

theorem cell22_95124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 9].length) (baseStart_95124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_95124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_95124 prefixEnd_95124 := by exact prefixLift 95124
  have htrace : WordTrace (prefixWord ++ tailWord_95124) baseStart_95124 baseEnd_95124 := by
    simpa [prefixWord, tailWord_95124, baseEnd_95124] using wordTrace_append hprefix tailTrace_95124
  have hstable : (prefixWord ++ tailWord_95124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95124).length < 2 ^ (prefixWord ++ tailWord_95124).sum := by decide
  have hdescent : baseEnd_95124 < baseStart_95124 := by decide
  rcases family_descends (prefixWord ++ tailWord_95124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95229 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 5, 5]
def baseStart_95229 : Nat := 118140960795 + 95229 * 2 ^ 59
def prefixEnd_95229 : Nat := 4983230072969 + 3 ^ 40 * 95229 * 2
def baseEnd_95229 : Nat := 32598832831408766533037

theorem tailTrace_95229 : CollatzResearch.WordTrace tailWord_95229 prefixEnd_95229 32598832831408766533037 := by
  unfold tailWord_95229
  simp only [CollatzResearch.WordTrace]
  refine ⟨3473286972009071663480741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2315524648006047775653827 3473286972009071663480741)
  ·
    refine ⟨651241307251700936902639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3473286972009071663480741 651241307251700936902639)
    ·
      refine ⟨976861960877551405353959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 651241307251700936902639 976861960877551405353959)
      ·
        refine ⟨1465292941316327108030939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 976861960877551405353959 1465292941316327108030939)
        ·
          refine ⟨2197939411974490662046409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1465292941316327108030939 2197939411974490662046409)
          ·
            refine ⟨1648454558980867996534807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2197939411974490662046409 1648454558980867996534807)
            ·
              refine ⟨2472681838471301994802211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1648454558980867996534807 2472681838471301994802211)
              ·
                refine ⟨3709022757706952992203317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2472681838471301994802211 3709022757706952992203317)
                ·
                  refine ⟨347720883535026843019061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3709022757706952992203317 347720883535026843019061)
                  ·
                    refine ⟨32598832831408766533037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 347720883535026843019061 32598832831408766533037)
                    ·
                      rfl

theorem cell22_95229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_95229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_95229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_95229 prefixEnd_95229 := by exact prefixLift 95229
  have htrace : WordTrace (prefixWord ++ tailWord_95229) baseStart_95229 baseEnd_95229 := by
    simpa [prefixWord, tailWord_95229, baseEnd_95229] using wordTrace_append hprefix tailTrace_95229
  have hstable : (prefixWord ++ tailWord_95229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95229).length < 2 ^ (prefixWord ++ tailWord_95229).sum := by decide
  have hdescent : baseEnd_95229 < baseStart_95229 := by decide
  rcases family_descends (prefixWord ++ tailWord_95229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95246 : List Nat := [4, 1, 1, 2, 2, 2, 1, 3, 1, 5]
def baseStart_95246 : Nat := 118140960795 + 95246 * 2 ^ 59
def prefixEnd_95246 : Nat := 4983230072969 + 3 ^ 40 * 95246 * 2
def baseEnd_95246 : Nat := 32604652278826388857985

theorem tailTrace_95246 : CollatzResearch.WordTrace tailWord_95246 prefixEnd_95246 32604652278826388857985 := by
  unfold tailWord_95246
  simp only [CollatzResearch.WordTrace]
  refine ⟨434238376618435445856199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2315938008631655711233061 434238376618435445856199)
  ·
    refine ⟨651357564927653168784299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 434238376618435445856199 651357564927653168784299)
    ·
      refine ⟨977036347391479753176449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 651357564927653168784299 977036347391479753176449)
      ·
        refine ⟨732777260543609814882337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 977036347391479753176449 732777260543609814882337)
        ·
          refine ⟨549582945407707361161753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 732777260543609814882337 549582945407707361161753)
          ·
            refine ⟨412187209055780520871315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 549582945407707361161753 412187209055780520871315)
            ·
              refine ⟨618280813583670781306973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412187209055780520871315 618280813583670781306973)
              ·
                refine ⟨231855305093876542990115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 618280813583670781306973 231855305093876542990115)
                ·
                  refine ⟨347782957640814814485173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231855305093876542990115 347782957640814814485173)
                  ·
                    refine ⟨32604652278826388857985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 347782957640814814485173 32604652278826388857985)
                    ·
                      rfl

theorem cell22_95246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_95246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_95246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_95246 prefixEnd_95246 := by exact prefixLift 95246
  have htrace : WordTrace (prefixWord ++ tailWord_95246) baseStart_95246 baseEnd_95246 := by
    simpa [prefixWord, tailWord_95246, baseEnd_95246] using wordTrace_append hprefix tailTrace_95246
  have hstable : (prefixWord ++ tailWord_95246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95246).length < 2 ^ (prefixWord ++ tailWord_95246).sum := by decide
  have hdescent : baseEnd_95246 < baseStart_95246 := by decide
  rcases family_descends (prefixWord ++ tailWord_95246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95297 : List Nat := [1, 2, 5, 1, 3, 1, 3, 1, 2, 3]
def baseStart_95297 : Nat := 118140960795 + 95297 * 2 ^ 59
def prefixEnd_95297 : Nat := 4983230072969 + 3 ^ 40 * 95297 * 2
def baseEnd_95297 : Nat := 32622110621079255832829

theorem tailTrace_95297 : CollatzResearch.WordTrace tailWord_95297 prefixEnd_95297 32622110621079255832829 := by
  unfold tailWord_95297
  simp only [CollatzResearch.WordTrace]
  refine ⟨3475767135762719276956145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2317178090508479517970763 3475767135762719276956145)
  ·
    refine ⟨2606825351822039457717109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3475767135762719276956145 2606825351822039457717109)
    ·
      refine ⟨244389876733316199160979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2606825351822039457717109 244389876733316199160979)
      ·
        refine ⟨366584815099974298741469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244389876733316199160979 366584815099974298741469)
        ·
          refine ⟨137469305662490362028051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 366584815099974298741469 137469305662490362028051)
          ·
            refine ⟨206203958493735543042077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137469305662490362028051 206203958493735543042077)
            ·
              refine ⟨77326484435150828640779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206203958493735543042077 77326484435150828640779)
              ·
                refine ⟨115989726652726242961169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77326484435150828640779 115989726652726242961169)
                ·
                  refine ⟨86992294989544682220877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115989726652726242961169 86992294989544682220877)
                  ·
                    refine ⟨32622110621079255832829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86992294989544682220877 32622110621079255832829)
                    ·
                      rfl

theorem cell22_95297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_95297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_95297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_95297 prefixEnd_95297 := by exact prefixLift 95297
  have htrace : WordTrace (prefixWord ++ tailWord_95297) baseStart_95297 baseEnd_95297 := by
    simpa [prefixWord, tailWord_95297, baseEnd_95297] using wordTrace_append hprefix tailTrace_95297
  have hstable : (prefixWord ++ tailWord_95297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95297).length < 2 ^ (prefixWord ++ tailWord_95297).sum := by decide
  have hdescent : baseEnd_95297 < baseStart_95297 := by decide
  rcases family_descends (prefixWord ++ tailWord_95297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95351 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 3, 4]
def baseStart_95351 : Nat := 118140960795 + 95351 * 2 ^ 59
def prefixEnd_95351 : Nat := 4983230072969 + 3 ^ 40 * 95351 * 2
def baseEnd_95351 : Nat := 32640595924641114982663

theorem tailTrace_95351 : CollatzResearch.WordTrace tailWord_95351 prefixEnd_95351 32640595924641114982663 := by
  unfold tailWord_95351
  simp only [CollatzResearch.WordTrace]
  refine ⟨3477736677567086499421907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2318491118378057666281271 3477736677567086499421907)
  ·
    refine ⟨5216605016350629749132861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3477736677567086499421907 5216605016350629749132861)
    ·
      refine ⟨1956226881131486155924823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5216605016350629749132861 1956226881131486155924823)
      ·
        refine ⟨2934340321697229233887235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1956226881131486155924823 2934340321697229233887235)
        ·
          refine ⟨4401510482545843850830853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2934340321697229233887235 4401510482545843850830853)
          ·
            refine ⟨825283215477345722030785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4401510482545843850830853 825283215477345722030785)
            ·
              refine ⟨618962411608009291523089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 825283215477345722030785 618962411608009291523089)
              ·
                refine ⟨464221808706006968642317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 618962411608009291523089 464221808706006968642317)
                ·
                  refine ⟨174083178264752613240869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 464221808706006968642317 174083178264752613240869)
                  ·
                    refine ⟨32640595924641114982663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 174083178264752613240869 32640595924641114982663)
                    ·
                      rfl

theorem cell22_95351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_95351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_95351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_95351 prefixEnd_95351 := by exact prefixLift 95351
  have htrace : WordTrace (prefixWord ++ tailWord_95351) baseStart_95351 baseEnd_95351 := by
    simpa [prefixWord, tailWord_95351, baseEnd_95351] using wordTrace_append hprefix tailTrace_95351
  have hstable : (prefixWord ++ tailWord_95351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95351).length < 2 ^ (prefixWord ++ tailWord_95351).sum := by decide
  have hdescent : baseEnd_95351 < baseStart_95351 := by decide
  rcases family_descends (prefixWord ++ tailWord_95351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95411 : List Nat := [1, 1, 1, 2, 3, 2, 5, 7]
def baseStart_95411 : Nat := 118140960795 + 95411 * 2 ^ 59
def prefixEnd_95411 : Nat := 4983230072969 + 3 ^ 40 * 95411 * 2
def baseEnd_95411 : Nat := 3629015016757884275831

theorem tailTrace_95411 : CollatzResearch.WordTrace tailWord_95411 prefixEnd_95411 3629015016757884275831 := by
  unfold tailWord_95411
  simp only [CollatzResearch.WordTrace]
  refine ⟨3479925057349716746606087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2319950038233144497737391 3479925057349716746606087)
  ·
    refine ⟨5219887586024575119909131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3479925057349716746606087 5219887586024575119909131)
    ·
      refine ⟨7829831379036862679863697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5219887586024575119909131 7829831379036862679863697)
      ·
        refine ⟨5872373534277647009897773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7829831379036862679863697 5872373534277647009897773)
        ·
          refine ⟨2202140075354117628711665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5872373534277647009897773 2202140075354117628711665)
          ·
            refine ⟨1651605056515588221533749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2202140075354117628711665 1651605056515588221533749)
            ·
              refine ⟨154837974048336395768789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1651605056515588221533749 154837974048336395768789)
              ·
                refine ⟨3629015016757884275831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 154837974048336395768789 3629015016757884275831)
                ·
                  rfl

theorem cell22_95411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 7].length) (baseStart_95411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_95411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_95411 prefixEnd_95411 := by exact prefixLift 95411
  have htrace : WordTrace (prefixWord ++ tailWord_95411) baseStart_95411 baseEnd_95411 := by
    simpa [prefixWord, tailWord_95411, baseEnd_95411] using wordTrace_append hprefix tailTrace_95411
  have hstable : (prefixWord ++ tailWord_95411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95411).length < 2 ^ (prefixWord ++ tailWord_95411).sum := by decide
  have hdescent : baseEnd_95411 < baseStart_95411 := by decide
  rcases family_descends (prefixWord ++ tailWord_95411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95537 : List Nat := [1, 2, 2, 3, 3, 3, 1, 2, 1, 4]
def baseStart_95537 : Nat := 118140960795 + 95537 * 2 ^ 59
def prefixEnd_95537 : Nat := 4983230072969 + 3 ^ 40 * 95537 * 2
def baseEnd_95537 : Nat := 32704267525798629832093

theorem tailTrace_95537 : CollatzResearch.WordTrace tailWord_95537 prefixEnd_95537 32704267525798629832093 := by
  unfold tailWord_95537
  simp only [CollatzResearch.WordTrace]
  refine ⟨3484520654893240265692865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2323013769928826843795243 3484520654893240265692865)
  ·
    refine ⟨2613390491169930199269649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3484520654893240265692865 2613390491169930199269649)
    ·
      refine ⟨1960042868377447649452237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2613390491169930199269649 1960042868377447649452237)
      ·
        refine ⟨735016075641542868544589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1960042868377447649452237 735016075641542868544589)
        ·
          refine ⟨275631028365578575704221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 735016075641542868544589 275631028365578575704221)
          ·
            refine ⟨103361635637091965889083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275631028365578575704221 103361635637091965889083)
            ·
              refine ⟨155042453455637948833625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103361635637091965889083 155042453455637948833625)
              ·
                refine ⟨116281840091728461625219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155042453455637948833625 116281840091728461625219)
                ·
                  refine ⟨174422760137592692437829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116281840091728461625219 174422760137592692437829)
                  ·
                    refine ⟨32704267525798629832093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 174422760137592692437829 32704267525798629832093)
                    ·
                      rfl

theorem cell22_95537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 4].length) (baseStart_95537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_95537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_95537 prefixEnd_95537 := by exact prefixLift 95537
  have htrace : WordTrace (prefixWord ++ tailWord_95537) baseStart_95537 baseEnd_95537 := by
    simpa [prefixWord, tailWord_95537, baseEnd_95537] using wordTrace_append hprefix tailTrace_95537
  have hstable : (prefixWord ++ tailWord_95537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95537).length < 2 ^ (prefixWord ++ tailWord_95537).sum := by decide
  have hdescent : baseEnd_95537 < baseStart_95537 := by decide
  rcases family_descends (prefixWord ++ tailWord_95537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95550 : List Nat := [4, 2, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_95550 : Nat := 118140960795 + 95550 * 2 ^ 59
def prefixEnd_95550 : Nat := 4983230072969 + 3 ^ 40 * 95550 * 2
def baseEnd_95550 : Nat := 32708717691470929257053

theorem tailTrace_95550 : CollatzResearch.WordTrace tailWord_95550 prefixEnd_95550 32708717691470929257053 := by
  unfold tailWord_95550
  simp only [CollatzResearch.WordTrace]
  refine ⟨435624350480767935739513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2323329869230762323944069 435624350480767935739513)
  ·
    refine ⟨326718262860575951804635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 435624350480767935739513 326718262860575951804635)
    ·
      refine ⟨490077394290863927706953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326718262860575951804635 490077394290863927706953)
      ·
        refine ⟨367558045718147945780215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490077394290863927706953 367558045718147945780215)
        ·
          refine ⟨551337068577221918670323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367558045718147945780215 551337068577221918670323)
          ·
            refine ⟨827005602865832878005485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551337068577221918670323 827005602865832878005485)
            ·
              refine ⟨310127101074687329252057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 827005602865832878005485 310127101074687329252057)
              ·
                refine ⟨232595325806015496939043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310127101074687329252057 232595325806015496939043)
                ·
                  refine ⟨348892988709023245408565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232595325806015496939043 348892988709023245408565)
                  ·
                    refine ⟨32708717691470929257053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 348892988709023245408565 32708717691470929257053)
                    ·
                      rfl

theorem cell22_95550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_95550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_95550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_95550 prefixEnd_95550 := by exact prefixLift 95550
  have htrace : WordTrace (prefixWord ++ tailWord_95550) baseStart_95550 baseEnd_95550 := by
    simpa [prefixWord, tailWord_95550, baseEnd_95550] using wordTrace_append hprefix tailTrace_95550
  have hstable : (prefixWord ++ tailWord_95550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95550).length < 2 ^ (prefixWord ++ tailWord_95550).sum := by decide
  have hdescent : baseEnd_95550 < baseStart_95550 := by decide
  rcases family_descends (prefixWord ++ tailWord_95550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95625 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 7]
def baseStart_95625 : Nat := 118140960795 + 95625 * 2 ^ 59
def prefixEnd_95625 : Nat := 4983230072969 + 3 ^ 40 * 95625 * 2
def baseEnd_95625 : Nat := 10911463908065244543941

theorem tailTrace_95625 : CollatzResearch.WordTrace tailWord_95625 prefixEnd_95625 10911463908065244543941 := by
  unfold tailWord_95625
  simp only [CollatzResearch.WordTrace]
  refine ⟨3487730278574431294896329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2325153519049620863264219 3487730278574431294896329)
  ·
    refine ⟨2615797708930823471172247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3487730278574431294896329 2615797708930823471172247)
    ·
      refine ⟨3923696563396235206758371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2615797708930823471172247 3923696563396235206758371)
      ·
        refine ⟨5885544845094352810137557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3923696563396235206758371 5885544845094352810137557)
        ·
          refine ⟨137942457306898893987599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 5885544845094352810137557 137942457306898893987599)
          ·
            refine ⟨206913685960348340981399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137942457306898893987599 206913685960348340981399)
            ·
              refine ⟨310370528940522511472099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206913685960348340981399 310370528940522511472099)
              ·
                refine ⟨465555793410783767208149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310370528940522511472099 465555793410783767208149)
                ·
                  refine ⟨10911463908065244543941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 465555793410783767208149 10911463908065244543941)
                  ·
                    rfl

theorem cell22_95625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 7].length) (baseStart_95625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_95625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_95625 prefixEnd_95625 := by exact prefixLift 95625
  have htrace : WordTrace (prefixWord ++ tailWord_95625) baseStart_95625 baseEnd_95625 := by
    simpa [prefixWord, tailWord_95625, baseEnd_95625] using wordTrace_append hprefix tailTrace_95625
  have hstable : (prefixWord ++ tailWord_95625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95625).length < 2 ^ (prefixWord ++ tailWord_95625).sum := by decide
  have hdescent : baseEnd_95625 < baseStart_95625 := by decide
  rcases family_descends (prefixWord ++ tailWord_95625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95642 : List Nat := [3, 1, 1, 4, 1, 1, 5, 1, 5]
def baseStart_95642 : Nat := 118140960795 + 95642 * 2 ^ 59
def prefixEnd_95642 : Nat := 4983230072969 + 3 ^ 40 * 95642 * 2
def baseEnd_95642 : Nat := 10913403723871118652257

theorem tailTrace_95642 : CollatzResearch.WordTrace tailWord_95642 prefixEnd_95642 10913403723871118652257 := by
  unfold tailWord_95642
  simp only [CollatzResearch.WordTrace]
  refine ⟨872087579878210799566295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2325566879675228798843453 872087579878210799566295)
  ·
    refine ⟨1308131369817316199349443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 872087579878210799566295 1308131369817316199349443)
    ·
      refine ⟨1962197054725974299024165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1308131369817316199349443 1962197054725974299024165)
      ·
        refine ⟨367911947761120181067031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1962197054725974299024165 367911947761120181067031)
        ·
          refine ⟨551867921641680271600547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367911947761120181067031 551867921641680271600547)
          ·
            refine ⟨827801882462520407400821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551867921641680271600547 827801882462520407400821)
            ·
              refine ⟨77606426480861288193827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 827801882462520407400821 77606426480861288193827)
              ·
                refine ⟨116409639721291932290741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77606426480861288193827 116409639721291932290741)
                ·
                  refine ⟨10913403723871118652257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116409639721291932290741 10913403723871118652257)
                  ·
                    rfl

theorem cell22_95642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 5].length) (baseStart_95642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_95642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_95642 prefixEnd_95642 := by exact prefixLift 95642
  have htrace : WordTrace (prefixWord ++ tailWord_95642) baseStart_95642 baseEnd_95642 := by
    simpa [prefixWord, tailWord_95642, baseEnd_95642] using wordTrace_append hprefix tailTrace_95642
  have hstable : (prefixWord ++ tailWord_95642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95642).length < 2 ^ (prefixWord ++ tailWord_95642).sum := by decide
  have hdescent : baseEnd_95642 < baseStart_95642 := by decide
  rcases family_descends (prefixWord ++ tailWord_95642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95653 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 8]
def baseStart_95653 : Nat := 118140960795 + 95653 * 2 ^ 59
def prefixEnd_95653 : Nat := 4983230072969 + 3 ^ 40 * 95653 * 2
def baseEnd_95653 : Nat := 10914658898804331310579

theorem tailTrace_95653 : CollatzResearch.WordTrace tailWord_95653 prefixEnd_95653 10914658898804331310579 := by
  unfold tailWord_95653
  simp only [CollatzResearch.WordTrace]
  refine ⟨3488751522472992076915613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2325834348315328051277075 3488751522472992076915613)
  ·
    refine ⟨1308281820927372028843355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3488751522472992076915613 1308281820927372028843355)
    ·
      refine ⟨1962422731391058043265033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1308281820927372028843355 1962422731391058043265033)
      ·
        refine ⟨1471817048543293532448775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1962422731391058043265033 1471817048543293532448775)
        ·
          refine ⟨2207725572814940298673163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1471817048543293532448775 2207725572814940298673163)
          ·
            refine ⟨3311588359222410448009745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2207725572814940298673163 3311588359222410448009745)
            ·
              refine ⟨2483691269416807836007309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3311588359222410448009745 2483691269416807836007309)
              ·
                refine ⟨931384226031302938502741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2483691269416807836007309 931384226031302938502741)
                ·
                  refine ⟨10914658898804331310579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 931384226031302938502741 10914658898804331310579)
                  ·
                    rfl

theorem cell22_95653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_95653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_95653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_95653 prefixEnd_95653 := by exact prefixLift 95653
  have htrace : WordTrace (prefixWord ++ tailWord_95653) baseStart_95653 baseEnd_95653 := by
    simpa [prefixWord, tailWord_95653, baseEnd_95653] using wordTrace_append hprefix tailTrace_95653
  have hstable : (prefixWord ++ tailWord_95653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95653).length < 2 ^ (prefixWord ++ tailWord_95653).sum := by decide
  have hdescent : baseEnd_95653 < baseStart_95653 := by decide
  rcases family_descends (prefixWord ++ tailWord_95653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95715 : List Nat := [1, 1, 1, 6, 2, 1, 2, 8]
def baseStart_95715 : Nat := 118140960795 + 95715 * 2 ^ 59
def prefixEnd_95715 : Nat := 4983230072969 + 3 ^ 40 * 95715 * 2
def baseEnd_95715 : Nat := 3640577840385055431283

theorem tailTrace_95715 : CollatzResearch.WordTrace tailWord_95715 prefixEnd_95715 3640577840385055431283 := by
  unfold tailWord_95715
  simp only [CollatzResearch.WordTrace]
  refine ⟨3491012848248376665672599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2327341898832251110448399 3491012848248376665672599)
  ·
    refine ⟨5236519272372564998508899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3491012848248376665672599 5236519272372564998508899)
    ·
      refine ⟨7854778908558847497763349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5236519272372564998508899 7854778908558847497763349)
      ·
        refine ⟨368192761338695976457657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7854778908558847497763349 368192761338695976457657)
        ·
          refine ⟨276144571004021982343243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368192761338695976457657 276144571004021982343243)
          ·
            refine ⟨414216856506032973514865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276144571004021982343243 414216856506032973514865)
            ·
              refine ⟨310662642379524730136149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414216856506032973514865 310662642379524730136149)
              ·
                refine ⟨3640577840385055431283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 310662642379524730136149 3640577840385055431283)
                ·
                  rfl

theorem cell22_95715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 8].length) (baseStart_95715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_95715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_95715 prefixEnd_95715 := by exact prefixLift 95715
  have htrace : WordTrace (prefixWord ++ tailWord_95715) baseStart_95715 baseEnd_95715 := by
    simpa [prefixWord, tailWord_95715, baseEnd_95715] using wordTrace_append hprefix tailTrace_95715
  have hstable : (prefixWord ++ tailWord_95715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95715).length < 2 ^ (prefixWord ++ tailWord_95715).sum := by decide
  have hdescent : baseEnd_95715 < baseStart_95715 := by decide
  rcases family_descends (prefixWord ++ tailWord_95715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95717 : List Nat := [1, 3, 1, 5, 1, 1, 1, 3, 2, 4]
def baseStart_95717 : Nat := 118140960795 + 95717 * 2 ^ 59
def prefixEnd_95717 : Nat := 4983230072969 + 3 ^ 40 * 95717 * 2
def baseEnd_95717 : Nat := 32765885204338160331541

theorem tailTrace_95717 : CollatzResearch.WordTrace tailWord_95717 prefixEnd_95717 32765885204338160331541 := by
  unfold tailWord_95717
  simp only [CollatzResearch.WordTrace]
  refine ⟨3491085794241131007245405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2327390529494087338163603 3491085794241131007245405)
  ·
    refine ⟨1309157172840424127717027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3491085794241131007245405 1309157172840424127717027)
    ·
      refine ⟨1963735759260636191575541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1309157172840424127717027 1963735759260636191575541)
      ·
        refine ⟨184100227430684642960207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1963735759260636191575541 184100227430684642960207)
        ·
          refine ⟨276150341146026964440311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184100227430684642960207 276150341146026964440311)
          ·
            refine ⟨414225511719040446660467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276150341146026964440311 414225511719040446660467)
            ·
              refine ⟨621338267578560669990701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414225511719040446660467 621338267578560669990701)
              ·
                refine ⟨233001850341960251246513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 621338267578560669990701 233001850341960251246513)
                ·
                  refine ⟨174751387756470188434885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233001850341960251246513 174751387756470188434885)
                  ·
                    refine ⟨32765885204338160331541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 174751387756470188434885 32765885204338160331541)
                    ·
                      rfl

theorem cell22_95717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_95717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_95717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_95717 prefixEnd_95717 := by exact prefixLift 95717
  have htrace : WordTrace (prefixWord ++ tailWord_95717) baseStart_95717 baseEnd_95717 := by
    simpa [prefixWord, tailWord_95717, baseEnd_95717] using wordTrace_append hprefix tailTrace_95717
  have hstable : (prefixWord ++ tailWord_95717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95717).length < 2 ^ (prefixWord ++ tailWord_95717).sum := by decide
  have hdescent : baseEnd_95717 < baseStart_95717 := by decide
  rcases family_descends (prefixWord ++ tailWord_95717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95856 : List Nat := [2, 1, 1, 1, 6, 2, 3, 2, 4]
def baseStart_95856 : Nat := 118140960795 + 95856 * 2 ^ 59
def prefixEnd_95856 : Nat := 4983230072969 + 3 ^ 40 * 95856 * 2
def baseEnd_95856 : Nat := 10937822581662710368705

theorem tailTrace_95856 : CollatzResearch.WordTrace tailWord_95856 prefixEnd_95856 10937822581662710368705 := by
  unfold tailWord_95856
  simp only [CollatzResearch.WordTrace]
  refine ⟨1748077770368778873277711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2330770360491705164370281 1748077770368778873277711)
  ·
    refine ⟨2622116655553168309916567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1748077770368778873277711 2622116655553168309916567)
    ·
      refine ⟨3933174983329752464874851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2622116655553168309916567 3933174983329752464874851)
      ·
        refine ⟨5899762474994628697312277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3933174983329752464874851 5899762474994628697312277)
        ·
          refine ⟨276551366015373220186513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5899762474994628697312277 276551366015373220186513)
          ·
            refine ⟨207413524511529915139885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276551366015373220186513 207413524511529915139885)
            ·
              refine ⟨77780071691823718177457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207413524511529915139885 77780071691823718177457)
              ·
                refine ⟨58335053768867788633093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77780071691823718177457 58335053768867788633093)
                ·
                  refine ⟨10937822581662710368705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58335053768867788633093 10937822581662710368705)
                  ·
                    rfl

theorem cell22_95856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 4].length) (baseStart_95856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_95856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_95856 prefixEnd_95856 := by exact prefixLift 95856
  have htrace : WordTrace (prefixWord ++ tailWord_95856) baseStart_95856 baseEnd_95856 := by
    simpa [prefixWord, tailWord_95856, baseEnd_95856] using wordTrace_append hprefix tailTrace_95856
  have hstable : (prefixWord ++ tailWord_95856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95856).length < 2 ^ (prefixWord ++ tailWord_95856).sum := by decide
  have hdescent : baseEnd_95856 < baseStart_95856 := by decide
  rcases family_descends (prefixWord ++ tailWord_95856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95918 : List Nat := [4, 1, 4, 1, 3, 1, 1, 7]
def baseStart_95918 : Nat := 118140960795 + 95918 * 2 ^ 59
def prefixEnd_95918 : Nat := 4983230072969 + 3 ^ 40 * 95918 * 2
def baseEnd_95918 : Nat := 3648299068004515117325

theorem tailTrace_95918 : CollatzResearch.WordTrace tailWord_95918 prefixEnd_95918 3648299068004515117325 := by
  unfold tailWord_95918
  simp only [CollatzResearch.WordTrace]
  refine ⟨437302108314117791914051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2332277911008628223541605 437302108314117791914051)
  ·
    refine ⟨655953162471176687871077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 437302108314117791914051 655953162471176687871077)
    ·
      refine ⟨122991217963345628975827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 655953162471176687871077 122991217963345628975827)
      ·
        refine ⟨184486826945018443463741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122991217963345628975827 184486826945018443463741)
        ·
          refine ⟨69182560104381916298903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184486826945018443463741 69182560104381916298903)
          ·
            refine ⟨103773840156572874448355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69182560104381916298903 103773840156572874448355)
            ·
              refine ⟨155660760234859311672533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103773840156572874448355 155660760234859311672533)
              ·
                refine ⟨3648299068004515117325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 155660760234859311672533 3648299068004515117325)
                ·
                  rfl

theorem cell22_95918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_95918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_95918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_95918 prefixEnd_95918 := by exact prefixLift 95918
  have htrace : WordTrace (prefixWord ++ tailWord_95918) baseStart_95918 baseEnd_95918 := by
    simpa [prefixWord, tailWord_95918, baseEnd_95918] using wordTrace_append hprefix tailTrace_95918
  have hstable : (prefixWord ++ tailWord_95918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95918).length < 2 ^ (prefixWord ++ tailWord_95918).sum := by decide
  have hdescent : baseEnd_95918 < baseStart_95918 := by decide
  rcases family_descends (prefixWord ++ tailWord_95918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95927 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 1, 7]
def baseStart_95927 : Nat := 118140960795 + 95927 * 2 ^ 59
def prefixEnd_95927 : Nat := 4983230072969 + 3 ^ 40 * 95927 * 2
def baseEnd_95927 : Nat := 32837772495967612580897

theorem tailTrace_95927 : CollatzResearch.WordTrace tailWord_95927 prefixEnd_95927 32837772495967612580897 := by
  unfold tailWord_95927
  simp only [CollatzResearch.WordTrace]
  refine ⟨3498745123480336872390035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2332496748986891248260023 3498745123480336872390035)
  ·
    refine ⟨5248117685220505308585053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3498745123480336872390035 5248117685220505308585053)
    ·
      refine ⟨1968044131957689490719395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5248117685220505308585053 1968044131957689490719395)
      ·
        refine ⟨2952066197936534236079093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1968044131957689490719395 2952066197936534236079093)
        ·
          refine ⟨276756206056550084632415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2952066197936534236079093 276756206056550084632415)
          ·
            refine ⟨415134309084825126948623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276756206056550084632415 415134309084825126948623)
            ·
              refine ⟨622701463627237690422935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415134309084825126948623 622701463627237690422935)
              ·
                refine ⟨934052195440856535634403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 622701463627237690422935 934052195440856535634403)
                ·
                  refine ⟨1401078293161284803451605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 934052195440856535634403 1401078293161284803451605)
                  ·
                    refine ⟨32837772495967612580897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1401078293161284803451605 32837772495967612580897)
                    ·
                      rfl

theorem cell22_95927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_95927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_95927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_95927 prefixEnd_95927 := by exact prefixLift 95927
  have htrace : WordTrace (prefixWord ++ tailWord_95927) baseStart_95927 baseEnd_95927 := by
    simpa [prefixWord, tailWord_95927, baseEnd_95927] using wordTrace_append hprefix tailTrace_95927
  have hstable : (prefixWord ++ tailWord_95927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95927).length < 2 ^ (prefixWord ++ tailWord_95927).sum := by decide
  have hdescent : baseEnd_95927 < baseStart_95927 := by decide
  rcases family_descends (prefixWord ++ tailWord_95927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95959 : List Nat := [1, 1, 3, 2, 1, 3, 3, 3, 1, 4]
def baseStart_95959 : Nat := 118140960795 + 95959 * 2 ^ 59
def prefixEnd_95959 : Nat := 4983230072969 + 3 ^ 40 * 95959 * 2
def baseEnd_95959 : Nat := 32848726749930195780799

theorem tailTrace_95959 : CollatzResearch.WordTrace tailWord_95959 prefixEnd_95959 32848726749930195780799 := by
  unfold tailWord_95959
  simp only [CollatzResearch.WordTrace]
  refine ⟨3499912259364406337554931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2333274839576270891703287 3499912259364406337554931)
  ·
    refine ⟨5249868389046609506332397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3499912259364406337554931 5249868389046609506332397)
    ·
      refine ⟨1968700645892478564874649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5249868389046609506332397 1968700645892478564874649)
      ·
        refine ⟨1476525484419358923655987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1968700645892478564874649 1476525484419358923655987)
        ·
          refine ⟨2214788226629038385483981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1476525484419358923655987 2214788226629038385483981)
          ·
            refine ⟨830545584985889394556493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2214788226629038385483981 830545584985889394556493)
            ·
              refine ⟨311454594369708522958685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 830545584985889394556493 311454594369708522958685)
              ·
                refine ⟨116795472888640696109507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311454594369708522958685 116795472888640696109507)
                ·
                  refine ⟨175193209332961044164261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116795472888640696109507 175193209332961044164261)
                  ·
                    refine ⟨32848726749930195780799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 175193209332961044164261 32848726749930195780799)
                    ·
                      rfl

theorem cell22_95959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_95959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_95959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_95959 prefixEnd_95959 := by exact prefixLift 95959
  have htrace : WordTrace (prefixWord ++ tailWord_95959) baseStart_95959 baseEnd_95959 := by
    simpa [prefixWord, tailWord_95959, baseEnd_95959] using wordTrace_append hprefix tailTrace_95959
  have hstable : (prefixWord ++ tailWord_95959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95959).length < 2 ^ (prefixWord ++ tailWord_95959).sum := by decide
  have hdescent : baseEnd_95959 < baseStart_95959 := by decide
  rcases family_descends (prefixWord ++ tailWord_95959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95987 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 1, 6]
def baseStart_95987 : Nat := 118140960795 + 95987 * 2 ^ 59
def prefixEnd_95987 : Nat := 4983230072969 + 3 ^ 40 * 95987 * 2
def baseEnd_95987 : Nat := 32858311722147456080713

theorem tailTrace_95987 : CollatzResearch.WordTrace tailWord_95987 prefixEnd_95987 32858311722147456080713 := by
  unfold tailWord_95987
  simp only [CollatzResearch.WordTrace]
  refine ⟨3500933503262967119574215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2333955668841978079716143 3500933503262967119574215)
  ·
    refine ⟨5251400254894450679361323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3500933503262967119574215 5251400254894450679361323)
    ·
      refine ⟨7877100382341676019041985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5251400254894450679361323 7877100382341676019041985)
      ·
        refine ⟨5907825286756257014281489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7877100382341676019041985 5907825286756257014281489)
        ·
          refine ⟨4430868965067192760711117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5907825286756257014281489 4430868965067192760711117)
          ·
            refine ⟨1661575861900197285266669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4430868965067192760711117 1661575861900197285266669)
            ·
              refine ⟨623090948212573981975001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1661575861900197285266669 623090948212573981975001)
              ·
                refine ⟨467318211159430486481251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 623090948212573981975001 467318211159430486481251)
                ·
                  refine ⟨700977316739145729721877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 467318211159430486481251 700977316739145729721877)
                  ·
                    refine ⟨32858311722147456080713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 700977316739145729721877 32858311722147456080713)
                    ·
                      rfl

theorem cell22_95987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 6].length) (baseStart_95987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_95987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_95987 prefixEnd_95987 := by exact prefixLift 95987
  have htrace : WordTrace (prefixWord ++ tailWord_95987) baseStart_95987 baseEnd_95987 := by
    simpa [prefixWord, tailWord_95987, baseEnd_95987] using wordTrace_append hprefix tailTrace_95987
  have hstable : (prefixWord ++ tailWord_95987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95987).length < 2 ^ (prefixWord ++ tailWord_95987).sum := by decide
  have hdescent : baseEnd_95987 < baseStart_95987 := by decide
  rcases family_descends (prefixWord ++ tailWord_95987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96004 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 1, 6]
def baseStart_96004 : Nat := 118140960795 + 96004 * 2 ^ 59
def prefixEnd_96004 : Nat := 4983230072969 + 3 ^ 40 * 96004 * 2
def baseEnd_96004 : Nat := 32864131169565078405661

theorem tailTrace_96004 : CollatzResearch.WordTrace tailWord_96004 prefixEnd_96004 32864131169565078405661 := by
  unfold tailWord_96004
  simp only [CollatzResearch.WordTrace]
  refine ⟨1750776772100689511471533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2334369029467586015295377 1750776772100689511471533)
  ·
    refine ⟨656541289537758566801825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1750776772100689511471533 656541289537758566801825)
    ·
      refine ⟨492405967153318925101369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 656541289537758566801825 492405967153318925101369)
      ·
        refine ⟨369304475364989193826027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 492405967153318925101369 369304475364989193826027)
        ·
          refine ⟨553956713047483790739041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369304475364989193826027 553956713047483790739041)
          ·
            refine ⟨415467534785612843054281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 553956713047483790739041 415467534785612843054281)
            ·
              refine ⟨311600651089209632290711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415467534785612843054281 311600651089209632290711)
              ·
                refine ⟨467400976633814448436067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311600651089209632290711 467400976633814448436067)
                ·
                  refine ⟨701101464950721672654101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 467400976633814448436067 701101464950721672654101)
                  ·
                    refine ⟨32864131169565078405661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 701101464950721672654101 32864131169565078405661)
                    ·
                      rfl

theorem cell22_96004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_96004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96004 prefixEnd_96004 := by exact prefixLift 96004
  have htrace : WordTrace (prefixWord ++ tailWord_96004) baseStart_96004 baseEnd_96004 := by
    simpa [prefixWord, tailWord_96004, baseEnd_96004] using wordTrace_append hprefix tailTrace_96004
  have hstable : (prefixWord ++ tailWord_96004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96004).length < 2 ^ (prefixWord ++ tailWord_96004).sum := by decide
  have hdescent : baseEnd_96004 < baseStart_96004 := by decide
  rcases family_descends (prefixWord ++ tailWord_96004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96040 : List Nat := [2, 1, 5, 1, 1, 4, 2, 1, 2, 3]
def baseStart_96040 : Nat := 118140960795 + 96040 * 2 ^ 59
def prefixEnd_96040 : Nat := 4983230072969 + 3 ^ 40 * 96040 * 2
def baseEnd_96040 : Nat := 32876454705272984505551

theorem tailTrace_96040 : CollatzResearch.WordTrace tailWord_96040 prefixEnd_96040 32876454705272984505551 := by
  unfold tailWord_96040
  simp only [CollatzResearch.WordTrace]
  refine ⟨1751433286035478585626787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2335244381380638114169049 1751433286035478585626787)
  ·
    refine ⟨2627149929053217878440181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1751433286035478585626787 2627149929053217878440181)
    ·
      refine ⟨246295305848739176103767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2627149929053217878440181 246295305848739176103767)
      ·
        refine ⟨369442958773108764155651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246295305848739176103767 369442958773108764155651)
        ·
          refine ⟨554164438159663146233477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369442958773108764155651 554164438159663146233477)
          ·
            refine ⟨103905832154936839918777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 554164438159663146233477 103905832154936839918777)
            ·
              refine ⟨77929374116202629939083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103905832154936839918777 77929374116202629939083)
              ·
                refine ⟨116894061174303944908625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77929374116202629939083 116894061174303944908625)
                ·
                  refine ⟨87670545880727958681469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116894061174303944908625 87670545880727958681469)
                  ·
                    refine ⟨32876454705272984505551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87670545880727958681469 32876454705272984505551)
                    ·
                      rfl

theorem cell22_96040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_96040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96040 prefixEnd_96040 := by exact prefixLift 96040
  have htrace : WordTrace (prefixWord ++ tailWord_96040) baseStart_96040 baseEnd_96040 := by
    simpa [prefixWord, tailWord_96040, baseEnd_96040] using wordTrace_append hprefix tailTrace_96040
  have hstable : (prefixWord ++ tailWord_96040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96040).length < 2 ^ (prefixWord ++ tailWord_96040).sum := by decide
  have hdescent : baseEnd_96040 < baseStart_96040 := by decide
  rcases family_descends (prefixWord ++ tailWord_96040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96081 : List Nat := [1, 2, 2, 1, 5, 2, 2, 2, 5]
def baseStart_96081 : Nat := 118140960795 + 96081 * 2 ^ 59
def prefixEnd_96081 : Nat := 4983230072969 + 3 ^ 40 * 96081 * 2
def baseEnd_96081 : Nat := 10963496614387514743475

theorem tailTrace_96081 : CollatzResearch.WordTrace tailWord_96081 prefixEnd_96081 10963496614387514743475 := by
  unfold tailWord_96081
  simp only [CollatzResearch.WordTrace]
  refine ⟨3504361964922421173496097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2336241309948280782330731 3504361964922421173496097)
  ·
    refine ⟨2628271473691815880122073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3504361964922421173496097 2628271473691815880122073)
    ·
      refine ⟨1971203605268861910091555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2628271473691815880122073 1971203605268861910091555)
      ·
        refine ⟨2956805407903292865137333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1971203605268861910091555 2956805407903292865137333)
        ·
          refine ⟨277200506990933706106625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2956805407903292865137333 277200506990933706106625)
          ·
            refine ⟨207900380243200279579969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277200506990933706106625 207900380243200279579969)
            ·
              refine ⟨155925285182400209684977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207900380243200279579969 155925285182400209684977)
              ·
                refine ⟨116943963886800157263733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155925285182400209684977 116943963886800157263733)
                ·
                  refine ⟨10963496614387514743475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116943963886800157263733 10963496614387514743475)
                  ·
                    rfl

theorem cell22_96081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 5].length) (baseStart_96081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96081 prefixEnd_96081 := by exact prefixLift 96081
  have htrace : WordTrace (prefixWord ++ tailWord_96081) baseStart_96081 baseEnd_96081 := by
    simpa [prefixWord, tailWord_96081, baseEnd_96081] using wordTrace_append hprefix tailTrace_96081
  have hstable : (prefixWord ++ tailWord_96081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96081).length < 2 ^ (prefixWord ++ tailWord_96081).sum := by decide
  have hdescent : baseEnd_96081 < baseStart_96081 := by decide
  rcases family_descends (prefixWord ++ tailWord_96081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96085 : List Nat := [1, 3, 2, 2, 2, 2, 4, 2, 1, 3]
def baseStart_96085 : Nat := 118140960795 + 96085 * 2 ^ 59
def prefixEnd_96085 : Nat := 4983230072969 + 3 ^ 40 * 96085 * 2
def baseEnd_96085 : Nat := 32891859124907867130413

theorem tailTrace_96085 : CollatzResearch.WordTrace tailWord_96085 prefixEnd_96085 32891859124907867130413 := by
  unfold tailWord_96085
  simp only [CollatzResearch.WordTrace]
  refine ⟨3504507856907929856641709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2336338571271953237761139 3504507856907929856641709)
  ·
    refine ⟨1314190446340473696240641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3504507856907929856641709 1314190446340473696240641)
    ·
      refine ⟨985642834755355272180481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1314190446340473696240641 985642834755355272180481)
      ·
        refine ⟨739232126066516454135361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 985642834755355272180481 739232126066516454135361)
        ·
          refine ⟨554424094549887340601521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 739232126066516454135361 554424094549887340601521)
          ·
            refine ⟨415818070912415505451141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 554424094549887340601521 415818070912415505451141)
            ·
              refine ⟨77965888296077907272089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 415818070912415505451141 77965888296077907272089)
              ·
                refine ⟨58474416222058430454067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77965888296077907272089 58474416222058430454067)
                ·
                  refine ⟨87711624333087645681101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58474416222058430454067 87711624333087645681101)
                  ·
                    refine ⟨32891859124907867130413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87711624333087645681101 32891859124907867130413)
                    ·
                      rfl

theorem cell22_96085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_96085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96085 prefixEnd_96085 := by exact prefixLift 96085
  have htrace : WordTrace (prefixWord ++ tailWord_96085) baseStart_96085 baseEnd_96085 := by
    simpa [prefixWord, tailWord_96085, baseEnd_96085] using wordTrace_append hprefix tailTrace_96085
  have hstable : (prefixWord ++ tailWord_96085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96085).length < 2 ^ (prefixWord ++ tailWord_96085).sum := by decide
  have hdescent : baseEnd_96085 < baseStart_96085 := by decide
  rcases family_descends (prefixWord ++ tailWord_96085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96109 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 8]
def baseStart_96109 : Nat := 118140960795 + 96109 * 2 ^ 59
def prefixEnd_96109 : Nat := 4983230072969 + 3 ^ 40 * 96109 * 2
def baseEnd_96109 : Nat := 10966691605126601510113

theorem tailTrace_96109 : CollatzResearch.WordTrace tailWord_96109 prefixEnd_96109 10966691605126601510113 := by
  unfold tailWord_96109
  simp only [CollatzResearch.WordTrace]
  refine ⟨3505383208820981955515381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2336922139213987970343587 3505383208820981955515381)
  ·
    refine ⟨328629675826967058329567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3505383208820981955515381 328629675826967058329567)
    ·
      refine ⟨492944513740450587494351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328629675826967058329567 492944513740450587494351)
      ·
        refine ⟨739416770610675881241527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492944513740450587494351 739416770610675881241527)
        ·
          refine ⟨1109125155916013821862291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739416770610675881241527 1109125155916013821862291)
          ·
            refine ⟨1663687733874020732793437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1109125155916013821862291 1663687733874020732793437)
            ·
              refine ⟨623882900202757774797539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1663687733874020732793437 623882900202757774797539)
              ·
                refine ⟨935824350304136662196309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623882900202757774797539 935824350304136662196309)
                ·
                  refine ⟨10966691605126601510113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 935824350304136662196309 10966691605126601510113)
                  ·
                    rfl

theorem cell22_96109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_96109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96109 prefixEnd_96109 := by exact prefixLift 96109
  have htrace : WordTrace (prefixWord ++ tailWord_96109) baseStart_96109 baseEnd_96109 := by
    simpa [prefixWord, tailWord_96109, baseEnd_96109] using wordTrace_append hprefix tailTrace_96109
  have hstable : (prefixWord ++ tailWord_96109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96109).length < 2 ^ (prefixWord ++ tailWord_96109).sum := by decide
  have hdescent : baseEnd_96109 < baseStart_96109 := by decide
  rcases family_descends (prefixWord ++ tailWord_96109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96139 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 4, 4]
def baseStart_96139 : Nat := 118140960795 + 96139 * 2 ^ 59
def prefixEnd_96139 : Nat := 4983230072969 + 3 ^ 40 * 96139 * 2
def baseEnd_96139 : Nat := 32910344428469726280247

theorem tailTrace_96139 : CollatzResearch.WordTrace tailWord_96139 prefixEnd_96139 32910344428469726280247 := by
  unfold tailWord_96139
  simp only [CollatzResearch.WordTrace]
  refine ⟨3506477398712297079107471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2337651599141531386071647 3506477398712297079107471)
  ·
    refine ⟨5259716098068445618661207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3506477398712297079107471 5259716098068445618661207)
    ·
      refine ⟨7889574147102668427991811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5259716098068445618661207 7889574147102668427991811)
      ·
        refine ⟨11834361220654002641987717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7889574147102668427991811 11834361220654002641987717)
        ·
          refine ⟨2218942728872625495372697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11834361220654002641987717 2218942728872625495372697)
          ·
            refine ⟨1664207046654469121529523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2218942728872625495372697 1664207046654469121529523)
            ·
              refine ⟨2496310569981703682294285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1664207046654469121529523 2496310569981703682294285)
              ·
                refine ⟨936116463743138880860357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2496310569981703682294285 936116463743138880860357)
                ·
                  refine ⟨175521836951838540161317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 936116463743138880860357 175521836951838540161317)
                  ·
                    refine ⟨32910344428469726280247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 175521836951838540161317 32910344428469726280247)
                    ·
                      rfl

theorem cell22_96139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 4].length) (baseStart_96139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96139 prefixEnd_96139 := by exact prefixLift 96139
  have htrace : WordTrace (prefixWord ++ tailWord_96139) baseStart_96139 baseEnd_96139 := by
    simpa [prefixWord, tailWord_96139, baseEnd_96139] using wordTrace_append hprefix tailTrace_96139
  have hstable : (prefixWord ++ tailWord_96139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96139).length < 2 ^ (prefixWord ++ tailWord_96139).sum := by decide
  have hdescent : baseEnd_96139 < baseStart_96139 := by decide
  rcases family_descends (prefixWord ++ tailWord_96139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96156 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 1, 6]
def baseStart_96156 : Nat := 118140960795 + 96156 * 2 ^ 59
def prefixEnd_96156 : Nat := 4983230072969 + 3 ^ 40 * 96156 * 2
def baseEnd_96156 : Nat := 32916163875887348605195

theorem tailTrace_96156 : CollatzResearch.WordTrace tailWord_96156 prefixEnd_96156 32916163875887348605195 := by
  unfold tailWord_96156
  simp only [CollatzResearch.WordTrace]
  refine ⟨1753548719825354491238161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2338064959767139321650881 1753548719825354491238161)
  ·
    refine ⟨1315161539869015868428621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1753548719825354491238161 1315161539869015868428621)
    ·
      refine ⟨493185577450880950660733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1315161539869015868428621 493185577450880950660733)
      ·
        refine ⟨184944591544080356497775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 493185577450880950660733 184944591544080356497775)
        ·
          refine ⟨277416887316120534746663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184944591544080356497775 277416887316120534746663)
          ·
            refine ⟨416125330974180802119995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277416887316120534746663 416125330974180802119995)
            ·
              refine ⟨624187996461271203179993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416125330974180802119995 624187996461271203179993)
              ·
                refine ⟨468140997345953402384995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 624187996461271203179993 468140997345953402384995)
                ·
                  refine ⟨702211496018930103577493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 468140997345953402384995 702211496018930103577493)
                  ·
                    refine ⟨32916163875887348605195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 702211496018930103577493 32916163875887348605195)
                    ·
                      rfl

theorem cell22_96156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_96156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96156 prefixEnd_96156 := by exact prefixLift 96156
  have htrace : WordTrace (prefixWord ++ tailWord_96156) baseStart_96156 baseEnd_96156 := by
    simpa [prefixWord, tailWord_96156, baseEnd_96156] using wordTrace_append hprefix tailTrace_96156
  have hstable : (prefixWord ++ tailWord_96156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96156).length < 2 ^ (prefixWord ++ tailWord_96156).sum := by decide
  have hdescent : baseEnd_96156 < baseStart_96156 := by decide
  rcases family_descends (prefixWord ++ tailWord_96156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96188 : List Nat := [2, 2, 2, 5, 1, 2, 8]
def baseStart_96188 : Nat := 118140960795 + 96188 * 2 ^ 59
def prefixEnd_96188 : Nat := 4983230072969 + 3 ^ 40 * 96188 * 2
def baseEnd_96188 : Nat := 1219522893698145622411

theorem tailTrace_96188 : CollatzResearch.WordTrace tailWord_96188 prefixEnd_96188 1219522893698145622411 := by
  unfold tailWord_96188
  simp only [CollatzResearch.WordTrace]
  refine ⟨1754132287767389223820609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2338843050356518965094145 1754132287767389223820609)
  ·
    refine ⟨1315599215825541917865457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1754132287767389223820609 1315599215825541917865457)
    ·
      refine ⟨986699411869156438399093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1315599215825541917865457 986699411869156438399093)
      ·
        refine ⟨92503069862733416099915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 986699411869156438399093 92503069862733416099915)
        ·
          refine ⟨138754604794100124149873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92503069862733416099915 138754604794100124149873)
          ·
            refine ⟨104065953595575093112405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138754604794100124149873 104065953595575093112405)
            ·
              refine ⟨1219522893698145622411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 104065953595575093112405 1219522893698145622411)
              ·
                rfl

theorem cell22_96188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 8].length) (baseStart_96188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96188 prefixEnd_96188 := by exact prefixLift 96188
  have htrace : WordTrace (prefixWord ++ tailWord_96188) baseStart_96188 baseEnd_96188 := by
    simpa [prefixWord, tailWord_96188, baseEnd_96188] using wordTrace_append hprefix tailTrace_96188
  have hstable : (prefixWord ++ tailWord_96188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96188).length < 2 ^ (prefixWord ++ tailWord_96188).sum := by decide
  have hdescent : baseEnd_96188 < baseStart_96188 := by decide
  rcases family_descends (prefixWord ++ tailWord_96188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96216 : List Nat := [2, 1, 2, 2, 2, 2, 3, 3, 5]
def baseStart_96216 : Nat := 118140960795 + 96216 * 2 ^ 59
def prefixEnd_96216 : Nat := 4983230072969 + 3 ^ 40 * 96216 * 2
def baseEnd_96216 : Nat := 10978901034022397368337

theorem tailTrace_96216 : CollatzResearch.WordTrace tailWord_96216 prefixEnd_96216 10978901034022397368337 := by
  unfold tailWord_96216
  simp only [CollatzResearch.WordTrace]
  refine ⟨1754642909716669614830251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2339523879622226153107001 1754642909716669614830251)
  ·
    refine ⟨2631964364575004422245377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1754642909716669614830251 2631964364575004422245377)
    ·
      refine ⟨1973973273431253316684033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2631964364575004422245377 1973973273431253316684033)
      ·
        refine ⟨1480479955073439987513025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1973973273431253316684033 1480479955073439987513025)
        ·
          refine ⟨1110359966305079990634769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1480479955073439987513025 1110359966305079990634769)
          ·
            refine ⟨832769974728809992976077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1110359966305079990634769 832769974728809992976077)
            ·
              refine ⟨312288740523303747366029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 832769974728809992976077 312288740523303747366029)
              ·
                refine ⟨117108277696238905262261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312288740523303747366029 117108277696238905262261)
                ·
                  refine ⟨10978901034022397368337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117108277696238905262261 10978901034022397368337)
                  ·
                    rfl

theorem cell22_96216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 5].length) (baseStart_96216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96216 prefixEnd_96216 := by exact prefixLift 96216
  have htrace : WordTrace (prefixWord ++ tailWord_96216) baseStart_96216 baseEnd_96216 := by
    simpa [prefixWord, tailWord_96216, baseEnd_96216] using wordTrace_append hprefix tailTrace_96216
  have hstable : (prefixWord ++ tailWord_96216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96216).length < 2 ^ (prefixWord ++ tailWord_96216).sum := by decide
  have hdescent : baseEnd_96216 < baseStart_96216 := by decide
  rcases family_descends (prefixWord ++ tailWord_96216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96254 : List Nat := [4, 2, 2, 2, 1, 1, 4, 2, 1, 3]
def baseStart_96254 : Nat := 118140960795 + 96254 * 2 ^ 59
def prefixEnd_96254 : Nat := 4983230072969 + 3 ^ 40 * 96254 * 2
def baseEnd_96254 : Nat := 32949711278647759654895

theorem tailTrace_96254 : CollatzResearch.WordTrace tailWord_96254 prefixEnd_96254 32949711278647759654895 := by
  unfold tailWord_96254
  simp only [CollatzResearch.WordTrace]
  refine ⟨438833974161958964942977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2340447862197114479695877 438833974161958964942977)
  ·
    refine ⟨329125480621469223707233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 438833974161958964942977 329125480621469223707233)
    ·
      refine ⟨246844110466101917780425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329125480621469223707233 246844110466101917780425)
      ·
        refine ⟨185133082849576438335319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246844110466101917780425 185133082849576438335319)
        ·
          refine ⟨277699624274364657502979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185133082849576438335319 277699624274364657502979)
          ·
            refine ⟨416549436411546986254469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277699624274364657502979 416549436411546986254469)
            ·
              refine ⟨78103019327165059922713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 416549436411546986254469 78103019327165059922713)
              ·
                refine ⟨58577264495373794942035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78103019327165059922713 58577264495373794942035)
                ·
                  refine ⟨87865896743060692413053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58577264495373794942035 87865896743060692413053)
                  ·
                    refine ⟨32949711278647759654895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87865896743060692413053 32949711278647759654895)
                    ·
                      rfl

theorem cell22_96254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_96254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96254 prefixEnd_96254 := by exact prefixLift 96254
  have htrace : WordTrace (prefixWord ++ tailWord_96254) baseStart_96254 baseEnd_96254 := by
    simpa [prefixWord, tailWord_96254, baseEnd_96254] using wordTrace_append hprefix tailTrace_96254
  have hstable : (prefixWord ++ tailWord_96254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96254).length < 2 ^ (prefixWord ++ tailWord_96254).sum := by decide
  have hdescent : baseEnd_96254 < baseStart_96254 := by decide
  rcases family_descends (prefixWord ++ tailWord_96254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96291 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 1, 6]
def baseStart_96291 : Nat := 118140960795 + 96291 * 2 ^ 59
def prefixEnd_96291 : Nat := 4983230072969 + 3 ^ 40 * 96291 * 2
def baseEnd_96291 : Nat := 32962377134791996479781

theorem tailTrace_96291 : CollatzResearch.WordTrace tailWord_96291 prefixEnd_96291 32962377134791996479781 := by
  unfold tailWord_96291
  simp only [CollatzResearch.WordTrace]
  refine ⟨3512021294161627038640727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2341347529441084692427151 3512021294161627038640727)
  ·
    refine ⟨5268031941242440557961091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3512021294161627038640727 5268031941242440557961091)
    ·
      refine ⟨7902047911863660836941637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5268031941242440557961091 7902047911863660836941637)
      ·
        refine ⟨1481633983474436406926557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7902047911863660836941637 1481633983474436406926557)
        ·
          refine ⟨555612743802913652597459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1481633983474436406926557 555612743802913652597459)
          ·
            refine ⟨833419115704370478896189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555612743802913652597459 833419115704370478896189)
            ·
              refine ⟨312532168389138929586071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 833419115704370478896189 312532168389138929586071)
              ·
                refine ⟨468798252583708394379107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312532168389138929586071 468798252583708394379107)
                ·
                  refine ⟨703197378875562591568661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 468798252583708394379107 703197378875562591568661)
                  ·
                    refine ⟨32962377134791996479781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 703197378875562591568661 32962377134791996479781)
                    ·
                      rfl

theorem cell22_96291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 6].length) (baseStart_96291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96291 prefixEnd_96291 := by exact prefixLift 96291
  have htrace : WordTrace (prefixWord ++ tailWord_96291) baseStart_96291 baseEnd_96291 := by
    simpa [prefixWord, tailWord_96291, baseEnd_96291] using wordTrace_append hprefix tailTrace_96291
  have hstable : (prefixWord ++ tailWord_96291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96291).length < 2 ^ (prefixWord ++ tailWord_96291).sum := by decide
  have hdescent : baseEnd_96291 < baseStart_96291 := by decide
  rcases family_descends (prefixWord ++ tailWord_96291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96306 : List Nat := [3, 2, 1, 1, 2, 4, 9]
def baseStart_96306 : Nat := 118140960795 + 96306 * 2 ^ 59
def prefixEnd_96306 : Nat := 4983230072969 + 3 ^ 40 * 96306 * 2
def baseEnd_96306 : Nat := 1221018960790257679805

theorem tailTrace_96306 : CollatzResearch.WordTrace tailWord_96306 prefixEnd_96306 1221018960790257679805 := by
  unfold tailWord_96306
  simp only [CollatzResearch.WordTrace]
  refine ⟨878142097276821150109193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2341712259404856400291181 878142097276821150109193)
  ·
    refine ⟨658606572957615862581895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 878142097276821150109193 658606572957615862581895)
    ·
      refine ⟨987909859436423793872843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 658606572957615862581895 987909859436423793872843)
      ·
        refine ⟨1481864789154635690809265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 987909859436423793872843 1481864789154635690809265)
        ·
          refine ⟨1111398591865976768106949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1481864789154635690809265 1111398591865976768106949)
          ·
            refine ⟨208387235974870644020053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1111398591865976768106949 208387235974870644020053)
            ·
              refine ⟨1221018960790257679805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 208387235974870644020053 1221018960790257679805)
              ·
                rfl

theorem cell22_96306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 9].length) (baseStart_96306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96306 prefixEnd_96306 := by exact prefixLift 96306
  have htrace : WordTrace (prefixWord ++ tailWord_96306) baseStart_96306 baseEnd_96306 := by
    simpa [prefixWord, tailWord_96306, baseEnd_96306] using wordTrace_append hprefix tailTrace_96306
  have hstable : (prefixWord ++ tailWord_96306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96306).length < 2 ^ (prefixWord ++ tailWord_96306).sum := by decide
  have hdescent : baseEnd_96306 < baseStart_96306 := by decide
  rcases family_descends (prefixWord ++ tailWord_96306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96310 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 4, 3]
def baseStart_96310 : Nat := 118140960795 + 96310 * 2 ^ 59
def prefixEnd_96310 : Nat := 4983230072969 + 3 ^ 40 * 96310 * 2
def baseEnd_96310 : Nat := 32968881223082280254723

theorem tailTrace_96310 : CollatzResearch.WordTrace tailWord_96310 prefixEnd_96310 32968881223082280254723 := by
  unfold tailWord_96310
  simp only [CollatzResearch.WordTrace]
  refine ⟨219544642568299580223899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2341809520728528855721589 219544642568299580223899)
  ·
    refine ⟨329316963852449370335849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219544642568299580223899 329316963852449370335849)
    ·
      refine ⟨246987722889337027751887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329316963852449370335849 246987722889337027751887)
      ·
        refine ⟨370481584334005541627831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246987722889337027751887 370481584334005541627831)
        ·
          refine ⟨555722376501008312441747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370481584334005541627831 555722376501008312441747)
          ·
            refine ⟨833583564751512468662621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555722376501008312441747 833583564751512468662621)
            ·
              refine ⟨312593836781817175748483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 833583564751512468662621 312593836781817175748483)
              ·
                refine ⟨468890755172725763622725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312593836781817175748483 468890755172725763622725)
                ·
                  refine ⟨87917016594886080679261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 468890755172725763622725 87917016594886080679261)
                  ·
                    refine ⟨32968881223082280254723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87917016594886080679261 32968881223082280254723)
                    ·
                      rfl

theorem cell22_96310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_96310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96310 prefixEnd_96310 := by exact prefixLift 96310
  have htrace : WordTrace (prefixWord ++ tailWord_96310) baseStart_96310 baseEnd_96310 := by
    simpa [prefixWord, tailWord_96310, baseEnd_96310] using wordTrace_append hprefix tailTrace_96310
  have hstable : (prefixWord ++ tailWord_96310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96310).length < 2 ^ (prefixWord ++ tailWord_96310).sum := by decide
  have hdescent : baseEnd_96310 < baseStart_96310 := by decide
  rcases family_descends (prefixWord ++ tailWord_96310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96385 : List Nat := [1, 2, 4, 2, 3, 1, 1, 3, 5]
def baseStart_96385 : Nat := 118140960795 + 96385 * 2 ^ 59
def prefixEnd_96385 : Nat := 4983230072969 + 3 ^ 40 * 96385 * 2
def baseEnd_96385 : Nat := 10998185085269028209831

theorem tailTrace_96385 : CollatzResearch.WordTrace tailWord_96385 prefixEnd_96385 10998185085269028209831 := by
  unfold tailWord_96385
  simp only [CollatzResearch.WordTrace]
  refine ⟨3515449755821081092562609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2343633170547387395041739 3515449755821081092562609)
  ·
    refine ⟨2636587316865810819421957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3515449755821081092562609 2636587316865810819421957)
    ·
      refine ⟨494360121912339528641617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2636587316865810819421957 494360121912339528641617)
      ·
        refine ⟨370770091434254646481213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 494360121912339528641617 370770091434254646481213)
        ·
          refine ⟨139038784287845492430455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 370770091434254646481213 139038784287845492430455)
          ·
            refine ⟨208558176431768238645683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139038784287845492430455 208558176431768238645683)
            ·
              refine ⟨312837264647652357968525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208558176431768238645683 312837264647652357968525)
              ·
                refine ⟨117313974242869634238197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312837264647652357968525 117313974242869634238197)
                ·
                  refine ⟨10998185085269028209831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117313974242869634238197 10998185085269028209831)
                  ·
                    rfl

theorem cell22_96385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 5].length) (baseStart_96385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96385 prefixEnd_96385 := by exact prefixLift 96385
  have htrace : WordTrace (prefixWord ++ tailWord_96385) baseStart_96385 baseEnd_96385 := by
    simpa [prefixWord, tailWord_96385, baseEnd_96385] using wordTrace_append hprefix tailTrace_96385
  have hstable : (prefixWord ++ tailWord_96385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96385).length < 2 ^ (prefixWord ++ tailWord_96385).sum := by decide
  have hdescent : baseEnd_96385 < baseStart_96385 := by decide
  rcases family_descends (prefixWord ++ tailWord_96385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96423 : List Nat := [1, 1, 6, 2, 3, 1, 2, 2, 1, 3]
def baseStart_96423 : Nat := 118140960795 + 96423 * 2 ^ 59
def prefixEnd_96423 : Nat := 4983230072969 + 3 ^ 40 * 96423 * 2
def baseEnd_96423 : Nat := 33007563432387652179377

theorem tailTrace_96423 : CollatzResearch.WordTrace tailWord_96423 prefixEnd_96423 33007563432387652179377 := by
  unfold tailWord_96423
  simp only [CollatzResearch.WordTrace]
  refine ⟨3516835729683413582445923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2344557153122275721630615 3516835729683413582445923)
  ·
    refine ⟨5275253594525120373668885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3516835729683413582445923 5275253594525120373668885)
    ·
      refine ⟨247277512243365017515729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5275253594525120373668885 247277512243365017515729)
      ·
        refine ⟨185458134182523763136797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247277512243365017515729 185458134182523763136797)
        ·
          refine ⟨69546800318446411176299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185458134182523763136797 69546800318446411176299)
          ·
            refine ⟨104320200477669616764449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69546800318446411176299 104320200477669616764449)
            ·
              refine ⟨78240150358252212573337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104320200477669616764449 78240150358252212573337)
              ·
                refine ⟨58680112768689159430003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78240150358252212573337 58680112768689159430003)
                ·
                  refine ⟨88020169153033739145005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58680112768689159430003 88020169153033739145005)
                  ·
                    refine ⟨33007563432387652179377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88020169153033739145005 33007563432387652179377)
                    ·
                      rfl

theorem cell22_96423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_96423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96423 prefixEnd_96423 := by exact prefixLift 96423
  have htrace : WordTrace (prefixWord ++ tailWord_96423) baseStart_96423 baseEnd_96423 := by
    simpa [prefixWord, tailWord_96423, baseEnd_96423] using wordTrace_append hprefix tailTrace_96423
  have hstable : (prefixWord ++ tailWord_96423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96423).length < 2 ^ (prefixWord ++ tailWord_96423).sum := by decide
  have hdescent : baseEnd_96423 < baseStart_96423 := by decide
  rcases family_descends (prefixWord ++ tailWord_96423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96428 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 8, 3]
def baseStart_96428 : Nat := 118140960795 + 96428 * 2 ^ 59
def prefixEnd_96428 : Nat := 4983230072969 + 3 ^ 40 * 96428 * 2
def baseEnd_96428 : Nat := 33009275034569305804361

theorem tailTrace_96428 : CollatzResearch.WordTrace tailWord_96428 prefixEnd_96428 33009275034569305804361 := by
  unfold tailWord_96428
  simp only [CollatzResearch.WordTrace]
  refine ⟨1758509047332649718188969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2344678729776866290918625 1758509047332649718188969)
  ·
    refine ⟨1318881785499487288641727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1758509047332649718188969 1318881785499487288641727)
    ·
      refine ⟨1978322678249230932962591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1318881785499487288641727 1978322678249230932962591)
      ·
        refine ⟨2967484017373846399443887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1978322678249230932962591 2967484017373846399443887)
        ·
          refine ⟨4451226026060769599165831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2967484017373846399443887 4451226026060769599165831)
          ·
            refine ⟨6676839039091154398748747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4451226026060769599165831 6676839039091154398748747)
            ·
              refine ⟨10015258558636731598123121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6676839039091154398748747 10015258558636731598123121)
              ·
                refine ⟨7511443918977548698592341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10015258558636731598123121 7511443918977548698592341)
                ·
                  refine ⟨88024733425518148811629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7511443918977548698592341 88024733425518148811629)
                  ·
                    refine ⟨33009275034569305804361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88024733425518148811629 33009275034569305804361)
                    ·
                      rfl

theorem cell22_96428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 3].length) (baseStart_96428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96428 prefixEnd_96428 := by exact prefixLift 96428
  have htrace : WordTrace (prefixWord ++ tailWord_96428) baseStart_96428 baseEnd_96428 := by
    simpa [prefixWord, tailWord_96428, baseEnd_96428] using wordTrace_append hprefix tailTrace_96428
  have hstable : (prefixWord ++ tailWord_96428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96428).length < 2 ^ (prefixWord ++ tailWord_96428).sum := by decide
  have hdescent : baseEnd_96428 < baseStart_96428 := by decide
  rcases family_descends (prefixWord ++ tailWord_96428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96541 : List Nat := [1, 4, 2, 3, 3, 1, 1, 1, 3, 3]
def baseStart_96541 : Nat := 118140960795 + 96541 * 2 ^ 59
def prefixEnd_96541 : Nat := 4983230072969 + 3 ^ 40 * 96541 * 2
def baseEnd_96541 : Nat := 33047957243874677729015

theorem tailTrace_96541 : CollatzResearch.WordTrace tailWord_96541 prefixEnd_96541 33047957243874677729015 := by
  unfold tailWord_96541
  simp only [CollatzResearch.WordTrace]
  refine ⟨3521139543255919735241477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2347426362170613156827651 3521139543255919735241477)
  ·
    refine ⟨660213664360484950357777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3521139543255919735241477 660213664360484950357777)
    ·
      refine ⟨495160248270363712768333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 660213664360484950357777 495160248270363712768333)
      ·
        refine ⟨185685093101386392288125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 495160248270363712768333 185685093101386392288125)
        ·
          refine ⟨69631909913019897108047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185685093101386392288125 69631909913019897108047)
          ·
            refine ⟨104447864869529845662071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69631909913019897108047 104447864869529845662071)
            ·
              refine ⟨156671797304294768493107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104447864869529845662071 156671797304294768493107)
              ·
                refine ⟨235007695956442152739661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156671797304294768493107 235007695956442152739661)
                ·
                  refine ⟨88127885983665807277373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 235007695956442152739661 88127885983665807277373)
                  ·
                    refine ⟨33047957243874677729015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88127885983665807277373 33047957243874677729015)
                    ·
                      rfl

theorem cell22_96541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_96541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96541 prefixEnd_96541 := by exact prefixLift 96541
  have htrace : WordTrace (prefixWord ++ tailWord_96541) baseStart_96541 baseEnd_96541 := by
    simpa [prefixWord, tailWord_96541, baseEnd_96541] using wordTrace_append hprefix tailTrace_96541
  have hstable : (prefixWord ++ tailWord_96541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96541).length < 2 ^ (prefixWord ++ tailWord_96541).sum := by decide
  have hdescent : baseEnd_96541 < baseStart_96541 := by decide
  rcases family_descends (prefixWord ++ tailWord_96541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96593 : List Nat := [1, 2, 2, 1, 4, 12]
def baseStart_96593 : Nat := 118140960795 + 96593 * 2 ^ 59
def prefixEnd_96593 : Nat := 4983230072969 + 3 ^ 40 * 96593 * 2
def baseEnd_96593 : Nat := 408219233414368832455

theorem tailTrace_96593 : CollatzResearch.WordTrace tailWord_96593 prefixEnd_96593 408219233414368832455 := by
  unfold tailWord_96593
  simp only [CollatzResearch.WordTrace]
  refine ⟨3523036139067532616134433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2348690759378355077422955 3523036139067532616134433)
  ·
    refine ⟨2642277104300649462100825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3523036139067532616134433 2642277104300649462100825)
    ·
      refine ⟨1981707828225487096575619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2642277104300649462100825 1981707828225487096575619)
      ·
        refine ⟨2972561742338230644863429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1981707828225487096575619 2972561742338230644863429)
        ·
          refine ⟨557355326688418245911893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2972561742338230644863429 557355326688418245911893)
          ·
            refine ⟨408219233414368832455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 557355326688418245911893 408219233414368832455)
            ·
              rfl

theorem cell22_96593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 12].length) (baseStart_96593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96593 prefixEnd_96593 := by exact prefixLift 96593
  have htrace : WordTrace (prefixWord ++ tailWord_96593) baseStart_96593 baseEnd_96593 := by
    simpa [prefixWord, tailWord_96593, baseEnd_96593] using wordTrace_append hprefix tailTrace_96593
  have hstable : (prefixWord ++ tailWord_96593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96593).length < 2 ^ (prefixWord ++ tailWord_96593).sum := by decide
  have hdescent : baseEnd_96593 < baseStart_96593 := by decide
  rcases family_descends (prefixWord ++ tailWord_96593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96629 : List Nat := [1, 3, 4, 1, 2, 3, 1, 1, 2, 4]
def baseStart_96629 : Nat := 118140960795 + 96629 * 2 ^ 59
def prefixEnd_96629 : Nat := 4983230072969 + 3 ^ 40 * 96629 * 2
def baseEnd_96629 : Nat := 33078081442271781528745

theorem tailTrace_96629 : CollatzResearch.WordTrace tailWord_96629 prefixEnd_96629 33078081442271781528745 := by
  unfold tailWord_96629
  simp only [CollatzResearch.WordTrace]
  refine ⟨3524349166937110764444941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2349566111291407176296627 3524349166937110764444941)
  ·
    refine ⟨1321630937601416536666853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3524349166937110764444941 1321630937601416536666853)
    ·
      refine ⟨247805800800265600625035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1321630937601416536666853 247805800800265600625035)
      ·
        refine ⟨371708701200398400937553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247805800800265600625035 371708701200398400937553)
        ·
          refine ⟨278781525900298800703165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371708701200398400937553 278781525900298800703165)
          ·
            refine ⟨104543072212612050263687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278781525900298800703165 104543072212612050263687)
            ·
              refine ⟨156814608318918075395531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104543072212612050263687 156814608318918075395531)
              ·
                refine ⟨235221912478377113093297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156814608318918075395531 235221912478377113093297)
                ·
                  refine ⟨176416434358782834819973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235221912478377113093297 176416434358782834819973)
                  ·
                    refine ⟨33078081442271781528745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 176416434358782834819973 33078081442271781528745)
                    ·
                      rfl

theorem cell22_96629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_96629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96629 prefixEnd_96629 := by exact prefixLift 96629
  have htrace : WordTrace (prefixWord ++ tailWord_96629) baseStart_96629 baseEnd_96629 := by
    simpa [prefixWord, tailWord_96629, baseEnd_96629] using wordTrace_append hprefix tailTrace_96629
  have hstable : (prefixWord ++ tailWord_96629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96629).length < 2 ^ (prefixWord ++ tailWord_96629).sum := by decide
  have hdescent : baseEnd_96629 < baseStart_96629 := by decide
  rcases family_descends (prefixWord ++ tailWord_96629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96693 : List Nat := [1, 3, 3, 2, 3, 2, 1, 3, 1, 3]
def baseStart_96693 : Nat := 118140960795 + 96693 * 2 ^ 59
def prefixEnd_96693 : Nat := 4983230072969 + 3 ^ 40 * 96693 * 2
def baseEnd_96693 : Nat := 33099989950196947928549

theorem tailTrace_96693 : CollatzResearch.WordTrace tailWord_96693 prefixEnd_96693 33099989950196947928549 := by
  unfold tailWord_96693
  simp only [CollatzResearch.WordTrace]
  refine ⟨3526683438705249694774733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2351122292470166463183155 3526683438705249694774733)
  ·
    refine ⟨1322506289514468635540525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3526683438705249694774733 1322506289514468635540525)
    ·
      refine ⟨495939858567925738327697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1322506289514468635540525 495939858567925738327697)
      ·
        refine ⟨371954893925944303745773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 495939858567925738327697 371954893925944303745773)
        ·
          refine ⟨139483085222229113904665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 371954893925944303745773 139483085222229113904665)
          ·
            refine ⟨104612313916671835428499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139483085222229113904665 104612313916671835428499)
            ·
              refine ⟨156918470875007753142749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104612313916671835428499 156918470875007753142749)
              ·
                refine ⟨58844426578127907428531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156918470875007753142749 58844426578127907428531)
                ·
                  refine ⟨88266639867191861142797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58844426578127907428531 88266639867191861142797)
                  ·
                    refine ⟨33099989950196947928549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88266639867191861142797 33099989950196947928549)
                    ·
                      rfl

theorem cell22_96693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_96693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96693 prefixEnd_96693 := by exact prefixLift 96693
  have htrace : WordTrace (prefixWord ++ tailWord_96693) baseStart_96693 baseEnd_96693 := by
    simpa [prefixWord, tailWord_96693, baseEnd_96693] using wordTrace_append hprefix tailTrace_96693
  have hstable : (prefixWord ++ tailWord_96693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96693).length < 2 ^ (prefixWord ++ tailWord_96693).sum := by decide
  have hdescent : baseEnd_96693 < baseStart_96693 := by decide
  rcases family_descends (prefixWord ++ tailWord_96693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96747 : List Nat := [1, 1, 1, 1, 2, 3, 6, 1, 2, 4]
def baseStart_96747 : Nat := 118140960795 + 96747 * 2 ^ 59
def prefixEnd_96747 : Nat := 4983230072969 + 3 ^ 40 * 96747 * 2
def baseEnd_96747 : Nat := 33118475253758807078383

theorem tailTrace_96747 : CollatzResearch.WordTrace tailWord_96747 prefixEnd_96747 33118475253758807078383 := by
  unfold tailWord_96747
  simp only [CollatzResearch.WordTrace]
  refine ⟨3528652980509616917240495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2352435320339744611493663 3528652980509616917240495)
  ·
    refine ⟨5292979470764425375860743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3528652980509616917240495 5292979470764425375860743)
    ·
      refine ⟨7939469206146638063791115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5292979470764425375860743 7939469206146638063791115)
      ·
        refine ⟨11909203809219957095686673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7939469206146638063791115 11909203809219957095686673)
        ·
          refine ⟨8931902856914967821765005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11909203809219957095686673 8931902856914967821765005)
          ·
            refine ⟨3349463571343112933161877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8931902856914967821765005 3349463571343112933161877)
            ·
              refine ⟨157006104906708418741963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3349463571343112933161877 157006104906708418741963)
              ·
                refine ⟨235509157360062628112945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157006104906708418741963 235509157360062628112945)
                ·
                  refine ⟨176631868020046971084709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235509157360062628112945 176631868020046971084709)
                  ·
                    refine ⟨33118475253758807078383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 176631868020046971084709 33118475253758807078383)
                    ·
                      rfl

theorem cell22_96747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 4].length) (baseStart_96747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96747 prefixEnd_96747 := by exact prefixLift 96747
  have htrace : WordTrace (prefixWord ++ tailWord_96747) baseStart_96747 baseEnd_96747 := by
    simpa [prefixWord, tailWord_96747, baseEnd_96747] using wordTrace_append hprefix tailTrace_96747
  have hstable : (prefixWord ++ tailWord_96747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96747).length < 2 ^ (prefixWord ++ tailWord_96747).sum := by decide
  have hdescent : baseEnd_96747 < baseStart_96747 := by decide
  rcases family_descends (prefixWord ++ tailWord_96747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96749 : List Nat := [1, 5, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_96749 : Nat := 118140960795 + 96749 * 2 ^ 59
def prefixEnd_96749 : Nat := 4983230072969 + 3 ^ 40 * 96749 * 2
def baseEnd_96749 : Nat := 33119159894631468528377

theorem tailTrace_96749 : CollatzResearch.WordTrace tailWord_96749 prefixEnd_96749 33119159894631468528377 := by
  unfold tailWord_96749
  simp only [CollatzResearch.WordTrace]
  refine ⟨3528725926502371258813301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2352483951001580839208867 3528725926502371258813301)
  ·
    refine ⟨330818055609597305513747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3528725926502371258813301 330818055609597305513747)
    ·
      refine ⟨496227083414395958270621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330818055609597305513747 496227083414395958270621)
      ·
        refine ⟨186085156280398484351483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 496227083414395958270621 186085156280398484351483)
        ·
          refine ⟨279127734420597726527225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186085156280398484351483 279127734420597726527225)
          ·
            refine ⟨209345800815448294895419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279127734420597726527225 209345800815448294895419)
            ·
              refine ⟨314018701223172442343129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209345800815448294895419 314018701223172442343129)
              ·
                refine ⟨235514025917379331757347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314018701223172442343129 235514025917379331757347)
                ·
                  refine ⟨353271038876068997636021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235514025917379331757347 353271038876068997636021)
                  ·
                    refine ⟨33119159894631468528377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 353271038876068997636021 33119159894631468528377)
                    ·
                      rfl

theorem cell22_96749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_96749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96749 prefixEnd_96749 := by exact prefixLift 96749
  have htrace : WordTrace (prefixWord ++ tailWord_96749) baseStart_96749 baseEnd_96749 := by
    simpa [prefixWord, tailWord_96749, baseEnd_96749] using wordTrace_append hprefix tailTrace_96749
  have hstable : (prefixWord ++ tailWord_96749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96749).length < 2 ^ (prefixWord ++ tailWord_96749).sum := by decide
  have hdescent : baseEnd_96749 < baseStart_96749 := by decide
  rcases family_descends (prefixWord ++ tailWord_96749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96867 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 3, 5]
def baseStart_96867 : Nat := 118140960795 + 96867 * 2 ^ 59
def prefixEnd_96867 : Nat := 4983230072969 + 3 ^ 40 * 96867 * 2
def baseEnd_96867 : Nat := 33159553706118494078015

theorem tailTrace_96867 : CollatzResearch.WordTrace tailWord_96867 prefixEnd_96867 33159553706118494078015 := by
  unfold tailWord_96867
  simp only [CollatzResearch.WordTrace]
  refine ⟨3533029740074877411608855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2355353160049918274405903 3533029740074877411608855)
  ·
    refine ⟨5299544610112316117413283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3533029740074877411608855 5299544610112316117413283)
    ·
      refine ⟨7949316915168474176119925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5299544610112316117413283 7949316915168474176119925)
      ·
        refine ⟨745248460797044454011243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7949316915168474176119925 745248460797044454011243)
        ·
          refine ⟨1117872691195566681016865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745248460797044454011243 1117872691195566681016865)
          ·
            refine ⟨838404518396675010762649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1117872691195566681016865 838404518396675010762649)
            ·
              refine ⟨628803388797506258071987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 838404518396675010762649 628803388797506258071987)
              ·
                refine ⟨943205083196259387107981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628803388797506258071987 943205083196259387107981)
                ·
                  refine ⟨353701906198597270165493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 943205083196259387107981 353701906198597270165493)
                  ·
                    refine ⟨33159553706118494078015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 353701906198597270165493 33159553706118494078015)
                    ·
                      rfl

theorem cell22_96867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 5].length) (baseStart_96867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96867 prefixEnd_96867 := by exact prefixLift 96867
  have htrace : WordTrace (prefixWord ++ tailWord_96867) baseStart_96867 baseEnd_96867 := by
    simpa [prefixWord, tailWord_96867, baseEnd_96867] using wordTrace_append hprefix tailTrace_96867
  have hstable : (prefixWord ++ tailWord_96867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96867).length < 2 ^ (prefixWord ++ tailWord_96867).sum := by decide
  have hdescent : baseEnd_96867 < baseStart_96867 := by decide
  rcases family_descends (prefixWord ++ tailWord_96867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96901 : List Nat := [1, 3, 1, 1, 4, 3, 1, 3, 2, 3]
def baseStart_96901 : Nat := 118140960795 + 96901 * 2 ^ 59
def prefixEnd_96901 : Nat := 4983230072969 + 3 ^ 40 * 96901 * 2
def baseEnd_96901 : Nat := 33171192600953738727911

theorem tailTrace_96901 : CollatzResearch.WordTrace tailWord_96901 prefixEnd_96901 33171192600953738727911 := by
  unfold tailWord_96901
  simp only [CollatzResearch.WordTrace]
  refine ⟨3534269821951701218346557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2356179881301134145564371 3534269821951701218346557)
  ·
    refine ⟨1325351183231887956879959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3534269821951701218346557 1325351183231887956879959)
    ·
      refine ⟨1988026774847831935319939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1325351183231887956879959 1988026774847831935319939)
      ·
        refine ⟨2982040162271747902979909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1988026774847831935319939 2982040162271747902979909)
        ·
          refine ⟨559132530425952731808733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2982040162271747902979909 559132530425952731808733)
          ·
            refine ⟨209674698909732274428275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 559132530425952731808733 209674698909732274428275)
            ·
              refine ⟨314512048364598411642413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209674698909732274428275 314512048364598411642413)
              ·
                refine ⟨117942018136724404365905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 314512048364598411642413 117942018136724404365905)
                ·
                  refine ⟨88456513602543303274429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117942018136724404365905 88456513602543303274429)
                  ·
                    refine ⟨33171192600953738727911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88456513602543303274429 33171192600953738727911)
                    ·
                      rfl

theorem cell22_96901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 3].length) (baseStart_96901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96901 prefixEnd_96901 := by exact prefixLift 96901
  have htrace : WordTrace (prefixWord ++ tailWord_96901) baseStart_96901 baseEnd_96901 := by
    simpa [prefixWord, tailWord_96901, baseEnd_96901] using wordTrace_append hprefix tailTrace_96901
  have hstable : (prefixWord ++ tailWord_96901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96901).length < 2 ^ (prefixWord ++ tailWord_96901).sum := by decide
  have hdescent : baseEnd_96901 < baseStart_96901 := by decide
  rcases family_descends (prefixWord ++ tailWord_96901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96914 : List Nat := [3, 2, 3, 1, 2, 1, 2, 8]
def baseStart_96914 : Nat := 118140960795 + 96914 * 2 ^ 59
def prefixEnd_96914 : Nat := 4983230072969 + 3 ^ 40 * 96914 * 2
def baseEnd_96914 : Nat := 3686182529625115350319

theorem tailTrace_96914 : CollatzResearch.WordTrace tailWord_96914 prefixEnd_96914 3686182529625115350319 := by
  unfold tailWord_96914
  simp only [CollatzResearch.WordTrace]
  refine ⟨883685992726151109642449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2356495980603069625713197 883685992726151109642449)
  ·
    refine ⟨662764494544613332231837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 883685992726151109642449 662764494544613332231837)
    ·
      refine ⟨248536685454229999586939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 662764494544613332231837 248536685454229999586939)
      ·
        refine ⟨372805028181344999380409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248536685454229999586939 372805028181344999380409)
        ·
          refine ⟨279603771136008749535307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372805028181344999380409 279603771136008749535307)
          ·
            refine ⟨419405656704013124302961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279603771136008749535307 419405656704013124302961)
            ·
              refine ⟨314554242528009843227221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 419405656704013124302961 314554242528009843227221)
              ·
                refine ⟨3686182529625115350319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 314554242528009843227221 3686182529625115350319)
                ·
                  rfl

theorem cell22_96914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 8].length) (baseStart_96914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96914 prefixEnd_96914 := by exact prefixLift 96914
  have htrace : WordTrace (prefixWord ++ tailWord_96914) baseStart_96914 baseEnd_96914 := by
    simpa [prefixWord, tailWord_96914, baseEnd_96914] using wordTrace_append hprefix tailTrace_96914
  have hstable : (prefixWord ++ tailWord_96914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96914).length < 2 ^ (prefixWord ++ tailWord_96914).sum := by decide
  have hdescent : baseEnd_96914 < baseStart_96914 := by decide
  rcases family_descends (prefixWord ++ tailWord_96914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96916 : List Nat := [2, 4, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_96916 : Nat := 118140960795 + 96916 * 2 ^ 59
def prefixEnd_96916 : Nat := 4983230072969 + 3 ^ 40 * 96916 * 2
def baseEnd_96916 : Nat := 33176327407498699602865

theorem tailTrace_96916 : CollatzResearch.WordTrace tailWord_96916 prefixEnd_96916 33176327407498699602865 := by
  unfold tailWord_96916
  simp only [CollatzResearch.WordTrace]
  refine ⟨1767408458448679390071301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2356544611264905853428401 1767408458448679390071301)
  ·
    refine ⟨331389085959127385638369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1767408458448679390071301 331389085959127385638369)
    ·
      refine ⟨248541814469345539228777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331389085959127385638369 248541814469345539228777)
      ·
        refine ⟨186406360852009154421583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248541814469345539228777 186406360852009154421583)
        ·
          refine ⟨279609541278013731632375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186406360852009154421583 279609541278013731632375)
          ·
            refine ⟨419414311917020597448563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279609541278013731632375 419414311917020597448563)
            ·
              refine ⟨629121467875530896172845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419414311917020597448563 629121467875530896172845)
              ·
                refine ⟨235920550453324086064817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 629121467875530896172845 235920550453324086064817)
                ·
                  refine ⟨176940412839993064548613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235920550453324086064817 176940412839993064548613)
                  ·
                    refine ⟨33176327407498699602865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 176940412839993064548613 33176327407498699602865)
                    ·
                      rfl

theorem cell22_96916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_96916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96916 prefixEnd_96916 := by exact prefixLift 96916
  have htrace : WordTrace (prefixWord ++ tailWord_96916) baseStart_96916 baseEnd_96916 := by
    simpa [prefixWord, tailWord_96916, baseEnd_96916] using wordTrace_append hprefix tailTrace_96916
  have hstable : (prefixWord ++ tailWord_96916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96916).length < 2 ^ (prefixWord ++ tailWord_96916).sum := by decide
  have hdescent : baseEnd_96916 < baseStart_96916 := by decide
  rcases family_descends (prefixWord ++ tailWord_96916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96935 : List Nat := [1, 1, 6, 3, 1, 1, 2, 2, 2, 3]
def baseStart_96935 : Nat := 118140960795 + 96935 * 2 ^ 59
def prefixEnd_96935 : Nat := 4983230072969 + 3 ^ 40 * 96935 * 2
def baseEnd_96935 : Nat := 33182831495788983377807

theorem tailTrace_96935 : CollatzResearch.WordTrace tailWord_96935 prefixEnd_96935 33182831495788983377807 := by
  unfold tailWord_96935
  simp only [CollatzResearch.WordTrace]
  refine ⟨3535509903828525025084259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2357006602552350016722839 3535509903828525025084259)
  ·
    refine ⟨5303264855742787537626389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3535509903828525025084259 5303264855742787537626389)
    ·
      refine ⟨248590540112943165826237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5303264855742787537626389 248590540112943165826237)
      ·
        refine ⟨93221452542353687184839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248590540112943165826237 93221452542353687184839)
        ·
          refine ⟨139832178813530530777259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93221452542353687184839 139832178813530530777259)
          ·
            refine ⟨209748268220295796165889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139832178813530530777259 209748268220295796165889)
            ·
              refine ⟨157311201165221847124417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209748268220295796165889 157311201165221847124417)
              ·
                refine ⟨117983400873916385343313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157311201165221847124417 117983400873916385343313)
                ·
                  refine ⟨88487550655437289007485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117983400873916385343313 88487550655437289007485)
                  ·
                    refine ⟨33182831495788983377807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88487550655437289007485 33182831495788983377807)
                    ·
                      rfl

theorem cell22_96935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_96935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96935 prefixEnd_96935 := by exact prefixLift 96935
  have htrace : WordTrace (prefixWord ++ tailWord_96935) baseStart_96935 baseEnd_96935 := by
    simpa [prefixWord, tailWord_96935, baseEnd_96935] using wordTrace_append hprefix tailTrace_96935
  have hstable : (prefixWord ++ tailWord_96935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96935).length < 2 ^ (prefixWord ++ tailWord_96935).sum := by decide
  have hdescent : baseEnd_96935 < baseStart_96935 := by decide
  rcases family_descends (prefixWord ++ tailWord_96935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96959 : List Nat := [1, 1, 2, 2, 2, 4, 2, 3, 5]
def baseStart_96959 : Nat := 118140960795 + 96959 * 2 ^ 59
def prefixEnd_96959 : Nat := 4983230072969 + 3 ^ 40 * 96959 * 2
def baseEnd_96959 : Nat := 11063682395420306925911

theorem tailTrace_96959 : CollatzResearch.WordTrace tailWord_96959 prefixEnd_96959 11063682395420306925911 := by
  unfold tailWord_96959
  simp only [CollatzResearch.WordTrace]
  refine ⟨3536385255741577123957931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2357590170494384749305287 3536385255741577123957931)
  ·
    refine ⟨5304577883612365685936897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3536385255741577123957931 5304577883612365685936897)
    ·
      refine ⟨3978433412709274264452673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5304577883612365685936897 3978433412709274264452673)
      ·
        refine ⟨2983825059531955698339505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3978433412709274264452673 2983825059531955698339505)
        ·
          refine ⟨2237868794648966773754629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2983825059531955698339505 2237868794648966773754629)
          ·
            refine ⟨419600398996681270078993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2237868794648966773754629 419600398996681270078993)
            ·
              refine ⟨314700299247510952559245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 419600398996681270078993 314700299247510952559245)
              ·
                refine ⟨118012612217816607209717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 314700299247510952559245 118012612217816607209717)
                ·
                  refine ⟨11063682395420306925911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118012612217816607209717 11063682395420306925911)
                  ·
                    rfl

theorem cell22_96959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 5].length) (baseStart_96959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_96959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_96959 prefixEnd_96959 := by exact prefixLift 96959
  have htrace : WordTrace (prefixWord ++ tailWord_96959) baseStart_96959 baseEnd_96959 := by
    simpa [prefixWord, tailWord_96959, baseEnd_96959] using wordTrace_append hprefix tailTrace_96959
  have hstable : (prefixWord ++ tailWord_96959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96959).length < 2 ^ (prefixWord ++ tailWord_96959).sum := by decide
  have hdescent : baseEnd_96959 < baseStart_96959 := by decide
  rcases family_descends (prefixWord ++ tailWord_96959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97034 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 1, 6]
def baseStart_97034 : Nat := 118140960795 + 97034 * 2 ^ 59
def prefixEnd_97034 : Nat := 4983230072969 + 3 ^ 40 * 97034 * 2
def baseEnd_97034 : Nat := 33216721218985725152503

theorem tailTrace_97034 : CollatzResearch.WordTrace tailWord_97034 prefixEnd_97034 33216721218985725152503 := by
  unfold tailWord_97034
  simp only [CollatzResearch.WordTrace]
  refine ⟨884780182617466233234539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2359413820313243288625437 884780182617466233234539)
  ·
    refine ⟨1327170273926199349851809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 884780182617466233234539 1327170273926199349851809)
    ·
      refine ⟨995377705444649512388857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1327170273926199349851809 995377705444649512388857)
      ·
        refine ⟨746533279083487134291643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 995377705444649512388857 746533279083487134291643)
        ·
          refine ⟨1119799918625230701437465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 746533279083487134291643 1119799918625230701437465)
          ·
            refine ⟨839849938968923026078099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1119799918625230701437465 839849938968923026078099)
            ·
              refine ⟨1259774908453384539117149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 839849938968923026078099 1259774908453384539117149)
              ·
                refine ⟨472415590670019202168931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1259774908453384539117149 472415590670019202168931)
                ·
                  refine ⟨708623386005028803253397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 472415590670019202168931 708623386005028803253397)
                  ·
                    refine ⟨33216721218985725152503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 708623386005028803253397 33216721218985725152503)
                    ·
                      rfl

theorem cell22_97034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_97034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97034 prefixEnd_97034 := by exact prefixLift 97034
  have htrace : WordTrace (prefixWord ++ tailWord_97034) baseStart_97034 baseEnd_97034 := by
    simpa [prefixWord, tailWord_97034, baseEnd_97034] using wordTrace_append hprefix tailTrace_97034
  have hstable : (prefixWord ++ tailWord_97034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97034).length < 2 ^ (prefixWord ++ tailWord_97034).sum := by decide
  have hdescent : baseEnd_97034 < baseStart_97034 := by decide
  rcases family_descends (prefixWord ++ tailWord_97034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97070 : List Nat := [4, 1, 3, 2, 1, 2, 1, 3, 2, 3]
def baseStart_97070 : Nat := 118140960795 + 97070 * 2 ^ 59
def prefixEnd_97070 : Nat := 4983230072969 + 3 ^ 40 * 97070 * 2
def baseEnd_97070 : Nat := 33229044754693631252393

theorem tailTrace_97070 : CollatzResearch.WordTrace tailWord_97070 prefixEnd_97070 33229044754693631252393 := by
  unfold tailWord_97070
  simp only [CollatzResearch.WordTrace]
  refine ⟨442554219792430385156083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2360289172226295387499109 442554219792430385156083)
  ·
    refine ⟨663831329688645577734125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 442554219792430385156083 663831329688645577734125)
    ·
      refine ⟨248936748633242091650297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 663831329688645577734125 248936748633242091650297)
      ·
        refine ⟨186702561474931568737723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248936748633242091650297 186702561474931568737723)
        ·
          refine ⟨280053842212397353106585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186702561474931568737723 280053842212397353106585)
          ·
            refine ⟨210040381659298014829939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280053842212397353106585 210040381659298014829939)
            ·
              refine ⟨315060572488947022244909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210040381659298014829939 315060572488947022244909)
              ·
                refine ⟨118147714683355133341841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 315060572488947022244909 118147714683355133341841)
                ·
                  refine ⟨88610786012516350006381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118147714683355133341841 88610786012516350006381)
                  ·
                    refine ⟨33229044754693631252393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88610786012516350006381 33229044754693631252393)
                    ·
                      rfl

theorem cell22_97070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_97070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97070 prefixEnd_97070 := by exact prefixLift 97070
  have htrace : WordTrace (prefixWord ++ tailWord_97070) baseStart_97070 baseEnd_97070 := by
    simpa [prefixWord, tailWord_97070, baseEnd_97070] using wordTrace_append hprefix tailTrace_97070
  have hstable : (prefixWord ++ tailWord_97070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97070).length < 2 ^ (prefixWord ++ tailWord_97070).sum := by decide
  have hdescent : baseEnd_97070 < baseStart_97070 := by decide
  rcases family_descends (prefixWord ++ tailWord_97070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97111 : List Nat := [1, 1, 3, 2, 4, 1, 1, 4, 5]
def baseStart_97111 : Nat := 118140960795 + 97111 * 2 ^ 59
def prefixEnd_97111 : Nat := 4983230072969 + 3 ^ 40 * 97111 * 2
def baseEnd_97111 : Nat := 11081026630861063659089

theorem tailTrace_97111 : CollatzResearch.WordTrace tailWord_97111 prefixEnd_97111 11081026630861063659089 := by
  unfold tailWord_97111
  simp only [CollatzResearch.WordTrace]
  refine ⟨3541929151190907083491187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2361286100793938055660791 3541929151190907083491187)
  ·
    refine ⟨5312893726786360625236781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3541929151190907083491187 5312893726786360625236781)
    ·
      refine ⟨1992335147544885234463793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5312893726786360625236781 1992335147544885234463793)
      ·
        refine ⟨1494251360658663925847845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1992335147544885234463793 1494251360658663925847845)
        ·
          refine ⟨280172130123499486096471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1494251360658663925847845 280172130123499486096471)
          ·
            refine ⟨420258195185249229144707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280172130123499486096471 420258195185249229144707)
            ·
              refine ⟨630387292777873843717061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420258195185249229144707 630387292777873843717061)
              ·
                refine ⟨118197617395851345696949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 630387292777873843717061 118197617395851345696949)
                ·
                  refine ⟨11081026630861063659089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118197617395851345696949 11081026630861063659089)
                  ·
                    rfl

theorem cell22_97111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 5].length) (baseStart_97111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97111 prefixEnd_97111 := by exact prefixLift 97111
  have htrace : WordTrace (prefixWord ++ tailWord_97111) baseStart_97111 baseEnd_97111 := by
    simpa [prefixWord, tailWord_97111, baseEnd_97111] using wordTrace_append hprefix tailTrace_97111
  have hstable : (prefixWord ++ tailWord_97111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97111).length < 2 ^ (prefixWord ++ tailWord_97111).sum := by decide
  have hdescent : baseEnd_97111 < baseStart_97111 := by decide
  rcases family_descends (prefixWord ++ tailWord_97111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97139 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 8]
def baseStart_97139 : Nat := 118140960795 + 97139 * 2 ^ 59
def prefixEnd_97139 : Nat := 4983230072969 + 3 ^ 40 * 97139 * 2
def baseEnd_97139 : Nat := 11084221621600150425727

theorem tailTrace_97139 : CollatzResearch.WordTrace tailWord_97139 prefixEnd_97139 11084221621600150425727 := by
  unfold tailWord_97139
  simp only [CollatzResearch.WordTrace]
  refine ⟨3542950395089467865510471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2361966930059645243673647 3542950395089467865510471)
  ·
    refine ⟨5314425592634201798265707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3542950395089467865510471 5314425592634201798265707)
    ·
      refine ⟨7971638388951302697398561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5314425592634201798265707 7971638388951302697398561)
      ·
        refine ⟨5978728791713477023048921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7971638388951302697398561 5978728791713477023048921)
        ·
          refine ⟨4484046593785107767286691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5978728791713477023048921 4484046593785107767286691)
          ·
            refine ⟨6726069890677661650930037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4484046593785107767286691 6726069890677661650930037)
            ·
              refine ⟨630569052251030779774691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6726069890677661650930037 630569052251030779774691)
              ·
                refine ⟨945853578376546169662037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 630569052251030779774691 945853578376546169662037)
                ·
                  refine ⟨11084221621600150425727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 945853578376546169662037 11084221621600150425727)
                  ·
                    rfl

theorem cell22_97139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 8].length) (baseStart_97139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97139 prefixEnd_97139 := by exact prefixLift 97139
  have htrace : WordTrace (prefixWord ++ tailWord_97139) baseStart_97139 baseEnd_97139 := by
    simpa [prefixWord, tailWord_97139, baseEnd_97139] using wordTrace_append hprefix tailTrace_97139
  have hstable : (prefixWord ++ tailWord_97139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97139).length < 2 ^ (prefixWord ++ tailWord_97139).sum := by decide
  have hdescent : baseEnd_97139 < baseStart_97139 := by decide
  rcases family_descends (prefixWord ++ tailWord_97139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97173 : List Nat := [1, 3, 2, 1, 1, 4, 2, 4, 4]
def baseStart_97173 : Nat := 118140960795 + 97173 * 2 ^ 59
def prefixEnd_97173 : Nat := 4983230072969 + 3 ^ 40 * 97173 * 2
def baseEnd_97173 : Nat := 11088101253211898642359

theorem tailTrace_97173 : CollatzResearch.WordTrace tailWord_97173 prefixEnd_97173 11088101253211898642359 := by
  unfold tailWord_97173
  simp only [CollatzResearch.WordTrace]
  refine ⟨3544190476966291672248173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2362793651310861114832115 3544190476966291672248173)
  ·
    refine ⟨1329071428862359377093065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3544190476966291672248173 1329071428862359377093065)
    ·
      refine ⟨996803571646769532819799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1329071428862359377093065 996803571646769532819799)
      ·
        refine ⟨1495205357470154299229699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 996803571646769532819799 1495205357470154299229699)
        ·
          refine ⟨2242808036205231448844549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1495205357470154299229699 2242808036205231448844549)
          ·
            refine ⟨420526506788480896658353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2242808036205231448844549 420526506788480896658353)
            ·
              refine ⟨315394880091360672493765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420526506788480896658353 315394880091360672493765)
              ·
                refine ⟨59136540017130126092581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 315394880091360672493765 59136540017130126092581)
                ·
                  refine ⟨11088101253211898642359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59136540017130126092581 11088101253211898642359)
                  ·
                    rfl

theorem cell22_97173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 4].length) (baseStart_97173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97173 prefixEnd_97173 := by exact prefixLift 97173
  have htrace : WordTrace (prefixWord ++ tailWord_97173) baseStart_97173 baseEnd_97173 := by
    simpa [prefixWord, tailWord_97173, baseEnd_97173] using wordTrace_append hprefix tailTrace_97173
  have hstable : (prefixWord ++ tailWord_97173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97173).length < 2 ^ (prefixWord ++ tailWord_97173).sum := by decide
  have hdescent : baseEnd_97173 < baseStart_97173 := by decide
  rcases family_descends (prefixWord ++ tailWord_97173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97323 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 4, 3]
def baseStart_97323 : Nat := 118140960795 + 97323 * 2 ^ 59
def prefixEnd_97323 : Nat := 4983230072969 + 3 ^ 40 * 97323 * 2
def baseEnd_97323 : Nat := 33315651825085304676617

theorem tailTrace_97323 : CollatzResearch.WordTrace tailWord_97323 prefixEnd_97323 33315651825085304676617 := by
  unfold tailWord_97323
  simp only [CollatzResearch.WordTrace]
  refine ⟨3549661426422867290208623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2366440950948578193472415 3549661426422867290208623)
  ·
    refine ⟨5324492139634300935312935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3549661426422867290208623 5324492139634300935312935)
    ·
      refine ⟨7986738209451451402969403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5324492139634300935312935 7986738209451451402969403)
      ·
        refine ⟨11980107314177177104454105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7986738209451451402969403 11980107314177177104454105)
        ·
          refine ⟨8985080485632882828340579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11980107314177177104454105 8985080485632882828340579)
          ·
            refine ⟨13477620728449324242510869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8985080485632882828340579 13477620728449324242510869)
            ·
              refine ⟨631763471646062073867697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13477620728449324242510869 631763471646062073867697)
              ·
                refine ⟨473822603734546555400773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631763471646062073867697 473822603734546555400773)
                ·
                  refine ⟨88841738200227479137645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 473822603734546555400773 88841738200227479137645)
                  ·
                    refine ⟨33315651825085304676617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88841738200227479137645 33315651825085304676617)
                    ·
                      rfl

theorem cell22_97323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 3].length) (baseStart_97323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97323 prefixEnd_97323 := by exact prefixLift 97323
  have htrace : WordTrace (prefixWord ++ tailWord_97323) baseStart_97323 baseEnd_97323 := by
    simpa [prefixWord, tailWord_97323, baseEnd_97323] using wordTrace_append hprefix tailTrace_97323
  have hstable : (prefixWord ++ tailWord_97323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97323).length < 2 ^ (prefixWord ++ tailWord_97323).sum := by decide
  have hdescent : baseEnd_97323 < baseStart_97323 := by decide
  rcases family_descends (prefixWord ++ tailWord_97323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97338 : List Nat := [3, 1, 1, 1, 3, 1, 2, 4, 2, 4]
def baseStart_97338 : Nat := 118140960795 + 97338 * 2 ^ 59
def prefixEnd_97338 : Nat := 4983230072969 + 3 ^ 40 * 97338 * 2
def baseEnd_97338 : Nat := 33320786631630265551571

theorem tailTrace_97338 : CollatzResearch.WordTrace tailWord_97338 prefixEnd_97338 33320786631630265551571 := by
  unfold tailWord_97338
  simp only [CollatzResearch.WordTrace]
  refine ⟨887552130342131213001167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2366805680912349901336445 887552130342131213001167)
  ·
    refine ⟨1331328195513196819501751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 887552130342131213001167 1331328195513196819501751)
    ·
      refine ⟨1996992293269795229252627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1331328195513196819501751 1996992293269795229252627)
      ·
        refine ⟨2995488439904692843878941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1996992293269795229252627 2995488439904692843878941)
        ·
          refine ⟨1123308164964259816454603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2995488439904692843878941 1123308164964259816454603)
          ·
            refine ⟨1684962247446389724681905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123308164964259816454603 1684962247446389724681905)
            ·
              refine ⟨1263721685584792293511429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1684962247446389724681905 1263721685584792293511429)
              ·
                refine ⟨236947816047148555033393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1263721685584792293511429 236947816047148555033393)
                ·
                  refine ⟨177710862035361416275045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236947816047148555033393 177710862035361416275045)
                  ·
                    refine ⟨33320786631630265551571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 177710862035361416275045 33320786631630265551571)
                    ·
                      rfl

theorem cell22_97338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_97338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97338 prefixEnd_97338 := by exact prefixLift 97338
  have htrace : WordTrace (prefixWord ++ tailWord_97338) baseStart_97338 baseEnd_97338 := by
    simpa [prefixWord, tailWord_97338, baseEnd_97338] using wordTrace_append hprefix tailTrace_97338
  have hstable : (prefixWord ++ tailWord_97338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97338).length < 2 ^ (prefixWord ++ tailWord_97338).sum := by decide
  have hdescent : baseEnd_97338 < baseStart_97338 := by decide
  rcases family_descends (prefixWord ++ tailWord_97338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97340 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 4, 3]
def baseStart_97340 : Nat := 118140960795 + 97340 * 2 ^ 59
def prefixEnd_97340 : Nat := 4983230072969 + 3 ^ 40 * 97340 * 2
def baseEnd_97340 : Nat := 33321471272502927001565

theorem tailTrace_97340 : CollatzResearch.WordTrace tailWord_97340 prefixEnd_97340 33321471272502927001565 := by
  unfold tailWord_97340
  simp only [CollatzResearch.WordTrace]
  refine ⟨1775140733680639596788737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2366854311574186129051649 1775140733680639596788737)
  ·
    refine ⟨1331355550260479697591553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1775140733680639596788737 1331355550260479697591553)
    ·
      refine ⟨998516662695359773193665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1331355550260479697591553 998516662695359773193665)
      ·
        refine ⟨748887497021519829895249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 998516662695359773193665 748887497021519829895249)
        ·
          refine ⟨561665622766139872421437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 748887497021519829895249 561665622766139872421437)
          ·
            refine ⟨210624608537302452158039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 561665622766139872421437 210624608537302452158039)
            ·
              refine ⟨315936912805953678237059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210624608537302452158039 315936912805953678237059)
              ·
                refine ⟨473905369208930517355589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315936912805953678237059 473905369208930517355589)
                ·
                  refine ⟨88857256726674472004173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 473905369208930517355589 88857256726674472004173)
                  ·
                    refine ⟨33321471272502927001565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88857256726674472004173 33321471272502927001565)
                    ·
                      rfl

theorem cell22_97340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_97340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97340 prefixEnd_97340 := by exact prefixLift 97340
  have htrace : WordTrace (prefixWord ++ tailWord_97340) baseStart_97340 baseEnd_97340 := by
    simpa [prefixWord, tailWord_97340, baseEnd_97340] using wordTrace_append hprefix tailTrace_97340
  have hstable : (prefixWord ++ tailWord_97340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97340).length < 2 ^ (prefixWord ++ tailWord_97340).sum := by decide
  have hdescent : baseEnd_97340 < baseStart_97340 := by decide
  rcases family_descends (prefixWord ++ tailWord_97340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97342 : List Nat := [4, 2, 1, 3, 1, 1, 2, 4, 4]
def baseStart_97342 : Nat := 118140960795 + 97342 * 2 ^ 59
def prefixEnd_97342 : Nat := 4983230072969 + 3 ^ 40 * 97342 * 2
def baseEnd_97342 : Nat := 11107385304458529483853

theorem tailTrace_97342 : CollatzResearch.WordTrace tailWord_97342 prefixEnd_97342 11107385304458529483853 := by
  unfold tailWord_97342
  simp only [CollatzResearch.WordTrace]
  refine ⟨443794301669254191893785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2366902942236022356766853 443794301669254191893785)
  ·
    refine ⟨332845726251940643920339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 443794301669254191893785 332845726251940643920339)
    ·
      refine ⟨499268589377910965880509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332845726251940643920339 499268589377910965880509)
      ·
        refine ⟨187225721016716612205191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 499268589377910965880509 187225721016716612205191)
        ·
          refine ⟨280838581525074918307787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187225721016716612205191 280838581525074918307787)
          ·
            refine ⟨421257872287612377461681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280838581525074918307787 421257872287612377461681)
            ·
              refine ⟨315943404215709283096261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 421257872287612377461681 315943404215709283096261)
              ·
                refine ⟨59239388290445490580549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 315943404215709283096261 59239388290445490580549)
                ·
                  refine ⟨11107385304458529483853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59239388290445490580549 11107385304458529483853)
                  ·
                    rfl

theorem cell22_97342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_97342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97342 prefixEnd_97342 := by exact prefixLift 97342
  have htrace : WordTrace (prefixWord ++ tailWord_97342) baseStart_97342 baseEnd_97342 := by
    simpa [prefixWord, tailWord_97342, baseEnd_97342] using wordTrace_append hprefix tailTrace_97342
  have hstable : (prefixWord ++ tailWord_97342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97342).length < 2 ^ (prefixWord ++ tailWord_97342).sum := by decide
  have hdescent : baseEnd_97342 < baseStart_97342 := by decide
  rcases family_descends (prefixWord ++ tailWord_97342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97357 : List Nat := [1, 6, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_97357 : Nat := 118140960795 + 97357 * 2 ^ 59
def prefixEnd_97357 : Nat := 4983230072969 + 3 ^ 40 * 97357 * 2
def baseEnd_97357 : Nat := 33327290719920549326513

theorem tailTrace_97357 : CollatzResearch.WordTrace tailWord_97357 prefixEnd_97357 33327290719920549326513 := by
  unfold tailWord_97357
  simp only [CollatzResearch.WordTrace]
  refine ⟨3550901508299691096946325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2367267672199794064630883 3550901508299691096946325)
  ·
    refine ⟨166448508201548020169359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3550901508299691096946325 166448508201548020169359)
    ·
      refine ⟨249672762302322030254039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166448508201548020169359 249672762302322030254039)
      ·
        refine ⟨374509143453483045381059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249672762302322030254039 374509143453483045381059)
        ·
          refine ⟨561763715180224568071589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374509143453483045381059 561763715180224568071589)
          ·
            refine ⟨105330696596292106513423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 561763715180224568071589 105330696596292106513423)
            ·
              refine ⟨157996044894438159770135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105330696596292106513423 157996044894438159770135)
              ·
                refine ⟨236994067341657239655203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157996044894438159770135 236994067341657239655203)
                ·
                  refine ⟨355491101012485859482805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236994067341657239655203 355491101012485859482805)
                  ·
                    refine ⟨33327290719920549326513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 355491101012485859482805 33327290719920549326513)
                    ·
                      rfl

theorem cell22_97357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_97357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97357 prefixEnd_97357 := by exact prefixLift 97357
  have htrace : WordTrace (prefixWord ++ tailWord_97357) baseStart_97357 baseEnd_97357 := by
    simpa [prefixWord, tailWord_97357, baseEnd_97357] using wordTrace_append hprefix tailTrace_97357
  have hstable : (prefixWord ++ tailWord_97357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97357).length < 2 ^ (prefixWord ++ tailWord_97357).sum := by decide
  have hdescent : baseEnd_97357 < baseStart_97357 := by decide
  rcases family_descends (prefixWord ++ tailWord_97357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97374 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_97374 : Nat := 118140960795 + 97374 * 2 ^ 59
def prefixEnd_97374 : Nat := 4983230072969 + 3 ^ 40 * 97374 * 2
def baseEnd_97374 : Nat := 33333110167338171651461

theorem tailTrace_97374 : CollatzResearch.WordTrace tailWord_97374 prefixEnd_97374 33333110167338171651461 := by
  unfold tailWord_97374
  simp only [CollatzResearch.WordTrace]
  refine ⟨443940193654762875039397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2367681032825402000210117 443940193654762875039397)
  ·
    refine ⟨83238786310268039069887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 443940193654762875039397 83238786310268039069887)
    ·
      refine ⟨124858179465402058604831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83238786310268039069887 124858179465402058604831)
      ·
        refine ⟨187287269198103087907247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124858179465402058604831 187287269198103087907247)
        ·
          refine ⟨280930903797154631860871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187287269198103087907247 280930903797154631860871)
          ·
            refine ⟨421396355695731947791307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280930903797154631860871 421396355695731947791307)
            ·
              refine ⟨632094533543597921686961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421396355695731947791307 632094533543597921686961)
              ·
                refine ⟨474070900157698441265221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 632094533543597921686961 474070900157698441265221)
                ·
                  refine ⟨88888293779568457737229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 474070900157698441265221 88888293779568457737229)
                  ·
                    refine ⟨33333110167338171651461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88888293779568457737229 33333110167338171651461)
                    ·
                      rfl

theorem cell22_97374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_97374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97374 prefixEnd_97374 := by exact prefixLift 97374
  have htrace : WordTrace (prefixWord ++ tailWord_97374) baseStart_97374 baseEnd_97374 := by
    simpa [prefixWord, tailWord_97374, baseEnd_97374] using wordTrace_append hprefix tailTrace_97374
  have hstable : (prefixWord ++ tailWord_97374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97374).length < 2 ^ (prefixWord ++ tailWord_97374).sum := by decide
  have hdescent : baseEnd_97374 < baseStart_97374 := by decide
  rcases family_descends (prefixWord ++ tailWord_97374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97453 : List Nat := [1, 5, 2, 1, 3, 2, 2, 2, 1, 3]
def baseStart_97453 : Nat := 118140960795 + 97453 * 2 ^ 59
def prefixEnd_97453 : Nat := 4983230072969 + 3 ^ 40 * 97453 * 2
def baseEnd_97453 : Nat := 33360153481808298926219

theorem tailTrace_97453 : CollatzResearch.WordTrace tailWord_97453 prefixEnd_97453 33360153481808298926219 := by
  unfold tailWord_97453
  simp only [CollatzResearch.WordTrace]
  refine ⟨3554402915951899492441013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2369601943967932994960675 3554402915951899492441013)
  ·
    refine ⟨333225273370490577416345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3554402915951899492441013 333225273370490577416345)
    ·
      refine ⟨249918955027867933062259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333225273370490577416345 249918955027867933062259)
      ·
        refine ⟨374878432541801899593389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249918955027867933062259 374878432541801899593389)
        ·
          refine ⟨140579412203175712347521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374878432541801899593389 140579412203175712347521)
          ·
            refine ⟨105434559152381784260641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140579412203175712347521 105434559152381784260641)
            ·
              refine ⟨79075919364286338195481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105434559152381784260641 79075919364286338195481)
              ·
                refine ⟨59306939523214753646611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79075919364286338195481 59306939523214753646611)
                ·
                  refine ⟨88960409284822130469917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59306939523214753646611 88960409284822130469917)
                  ·
                    refine ⟨33360153481808298926219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88960409284822130469917 33360153481808298926219)
                    ·
                      rfl

theorem cell22_97453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_97453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97453 prefixEnd_97453 := by exact prefixLift 97453
  have htrace : WordTrace (prefixWord ++ tailWord_97453) baseStart_97453 baseEnd_97453 := by
    simpa [prefixWord, tailWord_97453, baseEnd_97453] using wordTrace_append hprefix tailTrace_97453
  have hstable : (prefixWord ++ tailWord_97453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97453).length < 2 ^ (prefixWord ++ tailWord_97453).sum := by decide
  have hdescent : baseEnd_97453 < baseStart_97453 := by decide
  rcases family_descends (prefixWord ++ tailWord_97453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97490 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 1, 6]
def baseStart_97490 : Nat := 118140960795 + 97490 * 2 ^ 59
def prefixEnd_97490 : Nat := 4983230072969 + 3 ^ 40 * 97490 * 2
def baseEnd_97490 : Nat := 33372819337952535751105

theorem tailTrace_97490 : CollatzResearch.WordTrace tailWord_97490 prefixEnd_97490 33372819337952535751105 := by
  unfold tailWord_97490
  simp only [CollatzResearch.WordTrace]
  refine ⟨888938104204463702884481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2370501611211903207691949 888938104204463702884481)
  ·
    refine ⟨666703578153347777163361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 888938104204463702884481 666703578153347777163361)
    ·
      refine ⟨500027683615010832872521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 666703578153347777163361 500027683615010832872521)
      ·
        refine ⟨375020762711258124654391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 500027683615010832872521 375020762711258124654391)
        ·
          refine ⟨562531144066887186981587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375020762711258124654391 562531144066887186981587)
          ·
            refine ⟨843796716100330780472381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562531144066887186981587 843796716100330780472381)
            ·
              refine ⟨316423768537624042677143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 843796716100330780472381 316423768537624042677143)
              ·
                refine ⟨474635652806436064015715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316423768537624042677143 474635652806436064015715)
                ·
                  refine ⟨711953479209654096023573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 474635652806436064015715 711953479209654096023573)
                  ·
                    refine ⟨33372819337952535751105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 711953479209654096023573 33372819337952535751105)
                    ·
                      rfl

theorem cell22_97490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_97490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97490 prefixEnd_97490 := by exact prefixLift 97490
  have htrace : WordTrace (prefixWord ++ tailWord_97490) baseStart_97490 baseEnd_97490 := by
    simpa [prefixWord, tailWord_97490, baseEnd_97490] using wordTrace_append hprefix tailTrace_97490
  have hstable : (prefixWord ++ tailWord_97490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97490).length < 2 ^ (prefixWord ++ tailWord_97490).sum := by decide
  have hdescent : baseEnd_97490 < baseStart_97490 := by decide
  rcases family_descends (prefixWord ++ tailWord_97490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97496 : List Nat := [2, 1, 2, 2, 6, 1, 2, 1, 1, 4]
def baseStart_97496 : Nat := 118140960795 + 97496 * 2 ^ 59
def prefixEnd_97496 : Nat := 4983230072969 + 3 ^ 40 * 97496 * 2
def baseEnd_97496 : Nat := 33374873260570520101087

theorem tailTrace_97496 : CollatzResearch.WordTrace tailWord_97496 prefixEnd_97496 33374873260570520101087 := by
  unfold tailWord_97496
  simp only [CollatzResearch.WordTrace]
  refine ⟨1777985627398058918128171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2370647503197411890837561 1777985627398058918128171)
  ·
    refine ⟨2666978441097088377192257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1777985627398058918128171 2666978441097088377192257)
    ·
      refine ⟨2000233830822816282894193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2666978441097088377192257 2000233830822816282894193)
      ·
        refine ⟨1500175373117112212170645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2000233830822816282894193 1500175373117112212170645)
        ·
          refine ⟨70320720614864634945499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1500175373117112212170645 70320720614864634945499)
          ·
            refine ⟨105481080922296952418249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70320720614864634945499 105481080922296952418249)
            ·
              refine ⟨79110810691722714313687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105481080922296952418249 79110810691722714313687)
              ·
                refine ⟨118666216037584071470531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79110810691722714313687 118666216037584071470531)
                ·
                  refine ⟨177999324056376107205797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118666216037584071470531 177999324056376107205797)
                  ·
                    refine ⟨33374873260570520101087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 177999324056376107205797 33374873260570520101087)
                    ·
                      rfl

theorem cell22_97496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 1, 4].length) (baseStart_97496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97496 prefixEnd_97496 := by exact prefixLift 97496
  have htrace : WordTrace (prefixWord ++ tailWord_97496) baseStart_97496 baseEnd_97496 := by
    simpa [prefixWord, tailWord_97496, baseEnd_97496] using wordTrace_append hprefix tailTrace_97496
  have hstable : (prefixWord ++ tailWord_97496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97496).length < 2 ^ (prefixWord ++ tailWord_97496).sum := by decide
  have hdescent : baseEnd_97496 < baseStart_97496 := by decide
  rcases family_descends (prefixWord ++ tailWord_97496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97537 : List Nat := [1, 2, 4, 1, 1, 3, 2, 2, 3, 3]
def baseStart_97537 : Nat := 118140960795 + 97537 * 2 ^ 59
def prefixEnd_97537 : Nat := 4983230072969 + 3 ^ 40 * 97537 * 2
def baseEnd_97537 : Nat := 33388908398460079825961

theorem tailTrace_97537 : CollatzResearch.WordTrace tailWord_97537 prefixEnd_97537 33388908398460079825961 := by
  unfold tailWord_97537
  simp only [CollatzResearch.WordTrace]
  refine ⟨3557466647647581838498865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2371644431765054558999243 3557466647647581838498865)
  ·
    refine ⟨2668099985735686378874149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3557466647647581838498865 2668099985735686378874149)
    ·
      refine ⟨500268747325441196038903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2668099985735686378874149 500268747325441196038903)
      ·
        refine ⟨750403120988161794058355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500268747325441196038903 750403120988161794058355)
        ·
          refine ⟨1125604681482242691087533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750403120988161794058355 1125604681482242691087533)
          ·
            refine ⟨422101755555841009157825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1125604681482242691087533 422101755555841009157825)
            ·
              refine ⟨316576316666880756868369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 422101755555841009157825 316576316666880756868369)
              ·
                refine ⟨237432237500160567651277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 316576316666880756868369 237432237500160567651277)
                ·
                  refine ⟨89037089062560212869229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 237432237500160567651277 89037089062560212869229)
                  ·
                    refine ⟨33388908398460079825961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89037089062560212869229 33388908398460079825961)
                    ·
                      rfl

theorem cell22_97537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_97537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97537 prefixEnd_97537 := by exact prefixLift 97537
  have htrace : WordTrace (prefixWord ++ tailWord_97537) baseStart_97537 baseEnd_97537 := by
    simpa [prefixWord, tailWord_97537, baseEnd_97537] using wordTrace_append hprefix tailTrace_97537
  have hstable : (prefixWord ++ tailWord_97537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97537).length < 2 ^ (prefixWord ++ tailWord_97537).sum := by decide
  have hdescent : baseEnd_97537 < baseStart_97537 := by decide
  rcases family_descends (prefixWord ++ tailWord_97537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97550 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 7]
def baseStart_97550 : Nat := 118140960795 + 97550 * 2 ^ 59
def prefixEnd_97550 : Nat := 4983230072969 + 3 ^ 40 * 97550 * 2
def baseEnd_97550 : Nat := 11131119521377459750307

theorem tailTrace_97550 : CollatzResearch.WordTrace tailWord_97550 prefixEnd_97550 11131119521377459750307 := by
  unfold tailWord_97550
  simp only [CollatzResearch.WordTrace]
  refine ⟨444742599575060632340263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2371960531066990039148069 444742599575060632340263)
  ·
    refine ⟨667113899362590948510395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 444742599575060632340263 667113899362590948510395)
    ·
      refine ⟨1000670849043886422765593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 667113899362590948510395 1000670849043886422765593)
      ·
        refine ⟨750503136782914817074195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1000670849043886422765593 750503136782914817074195)
        ·
          refine ⟨1125754705174372225611293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750503136782914817074195 1125754705174372225611293)
          ·
            refine ⟨422158014440389584604235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1125754705174372225611293 422158014440389584604235)
            ·
              refine ⟨633237021660584376906353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422158014440389584604235 633237021660584376906353)
              ·
                refine ⟨474927766245438282679765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 633237021660584376906353 474927766245438282679765)
                ·
                  refine ⟨11131119521377459750307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 474927766245438282679765 11131119521377459750307)
                  ·
                    rfl

theorem cell22_97550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_97550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97550 prefixEnd_97550 := by exact prefixLift 97550
  have htrace : WordTrace (prefixWord ++ tailWord_97550) baseStart_97550 baseEnd_97550 := by
    simpa [prefixWord, tailWord_97550, baseEnd_97550] using wordTrace_append hprefix tailTrace_97550
  have hstable : (prefixWord ++ tailWord_97550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97550).length < 2 ^ (prefixWord ++ tailWord_97550).sum := by decide
  have hdescent : baseEnd_97550 < baseStart_97550 := by decide
  rcases family_descends (prefixWord ++ tailWord_97550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
