import V185TrunkScan23Chunk1134

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6723232 : List Nat := [2, 1, 1, 4, 3, 2, 2, 2, 2, 4]
def baseStart_6723232 : Nat := 118140960795 + 6723232 * 2 ^ 59
def prefixEnd_6723232 : Nat := 4983230072969 + 3 ^ 40 * 6723232 * 2
def baseEnd_6723232 : Nat := 1150749855896381519193475

theorem tailTrace_6723232 : CollatzResearch.WordTrace tailWord_6723232 prefixEnd_6723232 1150749855896381519193475 := by
  unfold tailWord_6723232
  simp only [CollatzResearch.WordTrace]
  refine ⟨122608208189443087727461975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163477610919257450303282633 122608208189443087727461975)
  ·
    refine ⟨183912312284164631591192963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122608208189443087727461975 183912312284164631591192963)
    ·
      refine ⟨275868468426246947386789445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183912312284164631591192963 275868468426246947386789445)
      ·
        refine ⟨51725337829921302635023021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275868468426246947386789445 51725337829921302635023021)
        ·
          refine ⟨19397001686220488488133633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51725337829921302635023021 19397001686220488488133633)
          ·
            refine ⟨14547751264665366366100225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19397001686220488488133633 14547751264665366366100225)
            ·
              refine ⟨10910813448499024774575169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14547751264665366366100225 10910813448499024774575169)
              ·
                refine ⟨8183110086374268580931377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10910813448499024774575169 8183110086374268580931377)
                ·
                  refine ⟨6137332564780701435698533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8183110086374268580931377 6137332564780701435698533)
                  ·
                    refine ⟨1150749855896381519193475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6137332564780701435698533 1150749855896381519193475)
                    ·
                      rfl

theorem cell23_6723232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 2, 4].length) (baseStart_6723232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723232 prefixEnd_6723232 := by exact prefixLift 6723232
  have htrace : WordTrace (prefixWord ++ tailWord_6723232) baseStart_6723232 baseEnd_6723232 := by
    simpa [prefixWord, tailWord_6723232, baseEnd_6723232] using wordTrace_append hprefix tailTrace_6723232
  have hstable : (prefixWord ++ tailWord_6723232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723232).length < 2 ^ (prefixWord ++ tailWord_6723232).sum := by decide
  have hdescent : baseEnd_6723232 < baseStart_6723232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723255 : List Nat := [1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 3]
def baseStart_6723255 : Nat := 118140960795 + 6723255 * 2 ^ 59
def prefixEnd_6723255 : Nat := 4983230072969 + 3 ^ 40 * 6723255 * 2
def baseEnd_6723255 : Nat := 3452261377744197967592819

theorem tailTrace_6723255 : CollatzResearch.WordTrace tailWord_6723255 prefixEnd_6723255 3452261377744197967592819 := by
  unfold tailWord_6723255
  simp only [CollatzResearch.WordTrace]
  refine ⟨245217255257802850383011219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163478170171868566922007479 245217255257802850383011219)
  ·
    refine ⟨367825882886704275574516829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245217255257802850383011219 367825882886704275574516829)
    ·
      refine ⟨137934706082514103340443811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 367825882886704275574516829 137934706082514103340443811)
      ·
        refine ⟨206902059123771155010665717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137934706082514103340443811 206902059123771155010665717)
        ·
          refine ⟨19397068042853545782249911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 206902059123771155010665717 19397068042853545782249911)
          ·
            refine ⟨29095602064280318673374867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19397068042853545782249911 29095602064280318673374867)
            ·
              refine ⟨43643403096420478010062301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29095602064280318673374867 43643403096420478010062301)
              ·
                refine ⟨16366276161157679253773363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43643403096420478010062301 16366276161157679253773363)
                ·
                  refine ⟨24549414241736518880660045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16366276161157679253773363 24549414241736518880660045)
                  ·
                    refine ⟨9206030340651194580247517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24549414241736518880660045 9206030340651194580247517)
                    ·
                      refine ⟨3452261377744197967592819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9206030340651194580247517 3452261377744197967592819)
                      ·
                        rfl

theorem cell23_6723255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 3].length) (baseStart_6723255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723255 prefixEnd_6723255 := by exact prefixLift 6723255
  have htrace : WordTrace (prefixWord ++ tailWord_6723255) baseStart_6723255 baseEnd_6723255 := by
    simpa [prefixWord, tailWord_6723255, baseEnd_6723255] using wordTrace_append hprefix tailTrace_6723255
  have hstable : (prefixWord ++ tailWord_6723255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723255).length < 2 ^ (prefixWord ++ tailWord_6723255).sum := by decide
  have hdescent : baseEnd_6723255 < baseStart_6723255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723276 : List Nat := [2, 2, 1, 5, 2, 2, 2, 1, 1, 2, 3]
def baseStart_6723276 : Nat := 118140960795 + 6723276 * 2 ^ 59
def prefixEnd_6723276 : Nat := 4983230072969 + 3 ^ 40 * 6723276 * 2
def baseEnd_6723276 : Nat := 3452272160837942385430223

theorem tailTrace_6723276 : CollatzResearch.WordTrace tailWord_6723276 prefixEnd_6723276 3452272160837942385430223 := by
  unfold tailWord_6723276
  simp only [CollatzResearch.WordTrace]
  refine ⟨122609010595363385484762841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163478680793817847313017121 122609010595363385484762841)
  ·
    refine ⟨91956757946522539113572131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122609010595363385484762841 91956757946522539113572131)
    ·
      refine ⟨137935136919783808670358197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91956757946522539113572131 137935136919783808670358197)
      ·
        refine ⟨12931419086229732062846081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137935136919783808670358197 12931419086229732062846081)
        ·
          refine ⟨9698564314672299047134561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12931419086229732062846081 9698564314672299047134561)
          ·
            refine ⟨7273923236004224285350921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9698564314672299047134561 7273923236004224285350921)
            ·
              refine ⟨5455442427003168214013191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7273923236004224285350921 5455442427003168214013191)
              ·
                refine ⟨8183163640504752321019787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5455442427003168214013191 8183163640504752321019787)
                ·
                  refine ⟨12274745460757128481529681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8183163640504752321019787 12274745460757128481529681)
                  ·
                    refine ⟨9206059095567846361147261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12274745460757128481529681 9206059095567846361147261)
                    ·
                      refine ⟨3452272160837942385430223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9206059095567846361147261 3452272160837942385430223)
                      ·
                        rfl

theorem cell23_6723276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_6723276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723276 prefixEnd_6723276 := by exact prefixLift 6723276
  have htrace : WordTrace (prefixWord ++ tailWord_6723276) baseStart_6723276 baseEnd_6723276 := by
    simpa [prefixWord, tailWord_6723276, baseEnd_6723276] using wordTrace_append hprefix tailTrace_6723276
  have hstable : (prefixWord ++ tailWord_6723276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723276).length < 2 ^ (prefixWord ++ tailWord_6723276).sum := by decide
  have hdescent : baseEnd_6723276 < baseStart_6723276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723288 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 4, 6]
def baseStart_6723288 : Nat := 118140960795 + 6723288 * 2 ^ 59
def prefixEnd_6723288 : Nat := 4983230072969 + 3 ^ 40 * 6723288 * 2
def baseEnd_6723288 : Nat := 1150759440868598779493389

theorem tailTrace_6723288 : CollatzResearch.WordTrace tailWord_6723288 prefixEnd_6723288 1150759440868598779493389 := by
  unfold tailWord_6723288
  simp only [CollatzResearch.WordTrace]
  refine ⟨122609229433341648509481259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163478972577788864679308345 122609229433341648509481259)
  ·
    refine ⟨183913844150012472764221889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122609229433341648509481259 183913844150012472764221889)
    ·
      refine ⟨137935383112509354573166417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183913844150012472764221889 137935383112509354573166417)
      ·
        refine ⟨103451537334382015929874813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137935383112509354573166417 103451537334382015929874813)
        ·
          refine ⟨38794326500393255973703055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103451537334382015929874813 38794326500393255973703055)
          ·
            refine ⟨58191489750589883960554583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38794326500393255973703055 58191489750589883960554583)
            ·
              refine ⟨87287234625884825940831875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58191489750589883960554583 87287234625884825940831875)
              ·
                refine ⟨130930851938827238911247813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87287234625884825940831875 130930851938827238911247813)
                ·
                  refine ⟨24549534738530107295858965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130930851938827238911247813 24549534738530107295858965)
                  ·
                    refine ⟨1150759440868598779493389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24549534738530107295858965 1150759440868598779493389)
                    ·
                      rfl

theorem cell23_6723288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_6723288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723288 prefixEnd_6723288 := by exact prefixLift 6723288
  have htrace : WordTrace (prefixWord ++ tailWord_6723288) baseStart_6723288 baseEnd_6723288 := by
    simpa [prefixWord, tailWord_6723288, baseEnd_6723288] using wordTrace_append hprefix tailTrace_6723288
  have hstable : (prefixWord ++ tailWord_6723288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723288).length < 2 ^ (prefixWord ++ tailWord_6723288).sum := by decide
  have hdescent : baseEnd_6723288 < baseStart_6723288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723289 : List Nat := [1, 2, 1, 2, 3, 5, 1, 2, 2, 1, 3]
def baseStart_6723289 : Nat := 118140960795 + 6723289 * 2 ^ 59
def prefixEnd_6723289 : Nat := 4983230072969 + 3 ^ 40 * 6723289 * 2
def baseEnd_6723289 : Nat := 3452278836086450834567663

theorem tailTrace_6723289 : CollatzResearch.WordTrace tailWord_6723289 prefixEnd_6723289 3452278836086450834567663 := by
  unfold tailWord_6723289
  simp only [CollatzResearch.WordTrace]
  refine ⟨245218495339679674189748921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163478996893119782793165947 245218495339679674189748921)
  ·
    refine ⟨183913871504759755642311691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245218495339679674189748921 183913871504759755642311691)
    ·
      refine ⟨275870807257139633463467537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183913871504759755642311691 275870807257139633463467537)
      ·
        refine ⟨206903105442854725097600653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275870807257139633463467537 206903105442854725097600653)
        ·
          refine ⟨77588664541070521911600245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206903105442854725097600653 77588664541070521911600245)
          ·
            refine ⟨7273937300725361429212523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77588664541070521911600245 7273937300725361429212523)
            ·
              refine ⟨10910905951088042143818785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7273937300725361429212523 10910905951088042143818785)
              ·
                refine ⟨8183179463316031607864089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10910905951088042143818785 8183179463316031607864089)
                ·
                  refine ⟨6137384597487023705898067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8183179463316031607864089 6137384597487023705898067)
                  ·
                    refine ⟨9206076896230535558847101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6137384597487023705898067 9206076896230535558847101)
                    ·
                      refine ⟨3452278836086450834567663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9206076896230535558847101 3452278836086450834567663)
                      ·
                        rfl

theorem cell23_6723289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 1, 3].length) (baseStart_6723289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723289 prefixEnd_6723289 := by exact prefixLift 6723289
  have htrace : WordTrace (prefixWord ++ tailWord_6723289) baseStart_6723289 baseEnd_6723289 := by
    simpa [prefixWord, tailWord_6723289, baseEnd_6723289] using wordTrace_append hprefix tailTrace_6723289
  have hstable : (prefixWord ++ tailWord_6723289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723289).length < 2 ^ (prefixWord ++ tailWord_6723289).sum := by decide
  have hdescent : baseEnd_6723289 < baseStart_6723289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723346 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_6723346 : Nat := 118140960795 + 6723346 * 2 ^ 59
def prefixEnd_6723346 : Nat := 4983230072969 + 3 ^ 40 * 6723346 * 2
def baseEnd_6723346 : Nat := 3452308104483757111554901

theorem tailTrace_6723346 : CollatzResearch.WordTrace tailWord_6723346 prefixEnd_6723346 3452308104483757111554901 := by
  unfold tailWord_6723346
  simp only [CollatzResearch.WordTrace]
  refine ⟨61305143575118293231143473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163480382866982115283049261 61305143575118293231143473)
  ·
    refine ⟨45978857681338719923357605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61305143575118293231143473 45978857681338719923357605)
    ·
      refine ⟨8621035815251009985629551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45978857681338719923357605 8621035815251009985629551)
      ·
        refine ⟨12931553722876514978444327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8621035815251009985629551 12931553722876514978444327)
        ·
          refine ⟨19397330584314772467666491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12931553722876514978444327 19397330584314772467666491)
          ·
            refine ⟨29095995876472158701499737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19397330584314772467666491 29095995876472158701499737)
            ·
              refine ⟨21821996907354119026124803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29095995876472158701499737 21821996907354119026124803)
              ·
                refine ⟨32732995361031178539187205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21821996907354119026124803 32732995361031178539187205)
                ·
                  refine ⟨6137436630193345976097601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32732995361031178539187205 6137436630193345976097601)
                  ·
                    refine ⟨4603077472645009482073201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6137436630193345976097601 4603077472645009482073201)
                    ·
                      refine ⟨3452308104483757111554901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4603077472645009482073201 3452308104483757111554901)
                      ·
                        rfl

theorem cell23_6723346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_6723346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723346 prefixEnd_6723346 := by exact prefixLift 6723346
  have htrace : WordTrace (prefixWord ++ tailWord_6723346) baseStart_6723346 baseEnd_6723346 := by
    simpa [prefixWord, tailWord_6723346, baseEnd_6723346] using wordTrace_append hprefix tailTrace_6723346
  have hstable : (prefixWord ++ tailWord_6723346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723346).length < 2 ^ (prefixWord ++ tailWord_6723346).sum := by decide
  have hdescent : baseEnd_6723346 < baseStart_6723346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723355 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 1, 7, 2]
def baseStart_6723355 : Nat := 118140960795 + 6723355 * 2 ^ 59
def prefixEnd_6723355 : Nat := 4983230072969 + 3 ^ 40 * 6723355 * 2
def baseEnd_6723355 : Nat := 3452312725809647576342359

theorem tailTrace_6723355 : CollatzResearch.WordTrace tailWord_6723355 prefixEnd_6723355 3452312725809647576342359 := by
  unfold tailWord_6723355
  simp only [CollatzResearch.WordTrace]
  refine ⟨245220902557440567461651519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163480601704960378307767679 245220902557440567461651519)
  ·
    refine ⟨367831353836160851192477279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245220902557440567461651519 367831353836160851192477279)
    ·
      refine ⟨551747030754241276788715919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367831353836160851192477279 551747030754241276788715919)
      ·
        refine ⟨827620546131361915183073879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551747030754241276788715919 827620546131361915183073879)
        ·
          refine ⟨1241430819197042872774610819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 827620546131361915183073879 1241430819197042872774610819)
          ·
            refine ⟨1862146228795564309161916229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1241430819197042872774610819 1862146228795564309161916229)
            ·
              refine ⟨349152417899168307967859293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1862146228795564309161916229 349152417899168307967859293)
              ·
                refine ⟨130932156712188115487947235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 349152417899168307967859293 130932156712188115487947235)
                ·
                  refine ⟨196398235068282173231920853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130932156712188115487947235 196398235068282173231920853)
                  ·
                    refine ⟨4603083634412863435123145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 196398235068282173231920853 4603083634412863435123145)
                    ·
                      refine ⟨3452312725809647576342359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4603083634412863435123145 3452312725809647576342359)
                      ·
                        rfl

theorem cell23_6723355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 7, 2].length) (baseStart_6723355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723355 prefixEnd_6723355 := by exact prefixLift 6723355
  have htrace : WordTrace (prefixWord ++ tailWord_6723355) baseStart_6723355 baseEnd_6723355 := by
    simpa [prefixWord, tailWord_6723355, baseEnd_6723355] using wordTrace_append hprefix tailTrace_6723355
  have hstable : (prefixWord ++ tailWord_6723355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723355).length < 2 ^ (prefixWord ++ tailWord_6723355).sum := by decide
  have hdescent : baseEnd_6723355 < baseStart_6723355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723402 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 2, 4, 2]
def baseStart_6723402 : Nat := 118140960795 + 6723402 * 2 ^ 59
def prefixEnd_6723402 : Nat := 4983230072969 + 3 ^ 40 * 6723402 * 2
def baseEnd_6723402 : Nat := 3452336859400408892454643

theorem tailTrace_6723402 : CollatzResearch.WordTrace tailWord_6723402 prefixEnd_6723402 3452336859400408892454643 := by
  unfold tailWord_6723402
  simp only [CollatzResearch.WordTrace]
  refine ⟨61305654197067573622153115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163481744525513529659074973 61305654197067573622153115)
  ·
    refine ⟨91958481295601360433229673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61305654197067573622153115 91958481295601360433229673)
    ·
      refine ⟨68968860971701020324922255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91958481295601360433229673 68968860971701020324922255)
      ·
        refine ⟨103453291457551530487383383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68968860971701020324922255 103453291457551530487383383)
        ·
          refine ⟨155179937186327295731075075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103453291457551530487383383 155179937186327295731075075)
          ·
            refine ⟨232769905779490943596612613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155179937186327295731075075 232769905779490943596612613)
            ·
              refine ⟨43644357333654551924364865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232769905779490943596612613 43644357333654551924364865)
              ·
                refine ⟨32733268000240913943273649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43644357333654551924364865 32733268000240913943273649)
                ·
                  refine ⟨24549951000180685457455237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32733268000240913943273649 24549951000180685457455237)
                  ·
                    refine ⟨4603115812533878523272857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24549951000180685457455237 4603115812533878523272857)
                    ·
                      refine ⟨3452336859400408892454643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4603115812533878523272857 3452336859400408892454643)
                      ·
                        rfl

theorem cell23_6723402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 2, 4, 2].length) (baseStart_6723402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723402 prefixEnd_6723402 := by exact prefixLift 6723402
  have htrace : WordTrace (prefixWord ++ tailWord_6723402) baseStart_6723402 baseEnd_6723402 := by
    simpa [prefixWord, tailWord_6723402, baseEnd_6723402] using wordTrace_append hprefix tailTrace_6723402
  have hstable : (prefixWord ++ tailWord_6723402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723402).length < 2 ^ (prefixWord ++ tailWord_6723402).sum := by decide
  have hdescent : baseEnd_6723402 < baseStart_6723402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723425 : List Nat := [1, 2, 3, 1, 1, 1, 3, 5, 6]
def baseStart_6723425 : Nat := 118140960795 + 6723425 * 2 ^ 59
def prefixEnd_6723425 : Nat := 4983230072969 + 3 ^ 40 * 6723425 * 2
def baseEnd_6723425 : Nat := 383594296606162478051893

theorem tailTrace_6723425 : CollatzResearch.WordTrace tailWord_6723425 prefixEnd_6723425 383594296606162478051893 := by
  unfold tailWord_6723425
  simp only [CollatzResearch.WordTrace]
  refine ⟨245223455667186969416699729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163482303778124646277799819 245223455667186969416699729)
  ·
    refine ⟨183917591750390227062524797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245223455667186969416699729 183917591750390227062524797)
    ·
      refine ⟨68969096906396335148446799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183917591750390227062524797 68969096906396335148446799)
      ·
        refine ⟨103453645359594502722670199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68969096906396335148446799 103453645359594502722670199)
        ·
          refine ⟨155180468039391754084005299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103453645359594502722670199 155180468039391754084005299)
          ·
            refine ⟨232770702059087631126007949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155180468039391754084005299 232770702059087631126007949)
            ·
              refine ⟨87289013272157861672252981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232770702059087631126007949 87289013272157861672252981)
              ·
                refine ⟨8183344994264799531773717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87289013272157861672252981 8183344994264799531773717)
                ·
                  refine ⟨383594296606162478051893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8183344994264799531773717 383594296606162478051893)
                  ·
                    rfl

theorem cell23_6723425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 6].length) (baseStart_6723425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723425 prefixEnd_6723425 := by exact prefixLift 6723425
  have htrace : WordTrace (prefixWord ++ tailWord_6723425) baseStart_6723425 baseEnd_6723425 := by
    simpa [prefixWord, tailWord_6723425, baseEnd_6723425] using wordTrace_append hprefix tailTrace_6723425
  have hstable : (prefixWord ++ tailWord_6723425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723425).length < 2 ^ (prefixWord ++ tailWord_6723425).sum := by decide
  have hdescent : baseEnd_6723425 < baseStart_6723425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723509 : List Nat := [1, 3, 3, 2, 1, 2, 2, 3, 1, 1, 4]
def baseStart_6723509 : Nat := 118140960795 + 6723509 * 2 ^ 59
def prefixEnd_6723509 : Nat := 4983230072969 + 3 ^ 40 * 6723509 * 2
def baseEnd_6723509 : Nat := 3452391801830439973816651

theorem tailTrace_6723509 : CollatzResearch.WordTrace tailWord_6723509 prefixEnd_6723509 3452391801830439973816651 := by
  unfold tailWord_6723509
  simp only [CollatzResearch.WordTrace]
  refine ⟨245226519398882651762757581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163484346265921767841838387 245226519398882651762757581)
  ·
    refine ⟨91959944774580994411034093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245226519398882651762757581 91959944774580994411034093)
    ·
      refine ⟨34484979290467872904137785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91959944774580994411034093 34484979290467872904137785)
      ·
        refine ⟨25863734467850904678103339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34484979290467872904137785 25863734467850904678103339)
        ·
          refine ⟨38795601701776357017155009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25863734467850904678103339 38795601701776357017155009)
          ·
            refine ⟨29096701276332267762866257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38795601701776357017155009 29096701276332267762866257)
            ·
              refine ⟨21822525957249200822149693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29096701276332267762866257 21822525957249200822149693)
              ·
                refine ⟨8183447233968450308306135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21822525957249200822149693 8183447233968450308306135)
                ·
                  refine ⟨12275170850952675462459203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8183447233968450308306135 12275170850952675462459203)
                  ·
                    refine ⟨18412756276429013193688805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12275170850952675462459203 18412756276429013193688805)
                    ·
                      refine ⟨3452391801830439973816651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18412756276429013193688805 3452391801830439973816651)
                      ·
                        rfl

theorem cell23_6723509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_6723509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723509 prefixEnd_6723509 := by exact prefixLift 6723509
  have htrace : WordTrace (prefixWord ++ tailWord_6723509) baseStart_6723509 baseEnd_6723509 := by
    simpa [prefixWord, tailWord_6723509, baseEnd_6723509] using wordTrace_append hprefix tailTrace_6723509
  have hstable : (prefixWord ++ tailWord_6723509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723509).length < 2 ^ (prefixWord ++ tailWord_6723509).sum := by decide
  have hdescent : baseEnd_6723509 < baseStart_6723509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723512 : List Nat := [2, 1, 2, 1, 2, 3, 4, 1, 1, 1, 5]
def baseStart_6723512 : Nat := 118140960795 + 6723512 * 2 ^ 59
def prefixEnd_6723512 : Nat := 4983230072969 + 3 ^ 40 * 6723512 * 2
def baseEnd_6723512 : Nat := 3452393342272403462079137

theorem tailTrace_6723512 : CollatzResearch.WordTrace tailWord_6723512 prefixEnd_6723512 3452393342272403462079137 := by
  unfold tailWord_6723512
  simp only [CollatzResearch.WordTrace]
  refine ⟨122613314408935891637558395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163484419211914522183411193 122613314408935891637558395)
  ·
    refine ⟨183919971613403837456337593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122613314408935891637558395 183919971613403837456337593)
    ·
      refine ⟨137939978710052878092253195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183919971613403837456337593 137939978710052878092253195)
      ·
        refine ⟨206909968065079317138379793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137939978710052878092253195 206909968065079317138379793)
        ·
          refine ⟨155182476048809487853784845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206909968065079317138379793 155182476048809487853784845)
          ·
            refine ⟨58193428518303557945169317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155182476048809487853784845 58193428518303557945169317)
            ·
              refine ⟨10911267847181917114719247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58193428518303557945169317 10911267847181917114719247)
              ·
                refine ⟨16366901770772875672078871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10911267847181917114719247 16366901770772875672078871)
                ·
                  refine ⟨24550352656159313508118307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16366901770772875672078871 24550352656159313508118307)
                  ·
                    refine ⟨36825528984238970262177461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24550352656159313508118307 36825528984238970262177461)
                    ·
                      refine ⟨3452393342272403462079137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36825528984238970262177461 3452393342272403462079137)
                      ·
                        rfl

theorem cell23_6723512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 1, 1, 5].length) (baseStart_6723512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723512 prefixEnd_6723512 := by exact prefixLift 6723512
  have htrace : WordTrace (prefixWord ++ tailWord_6723512) baseStart_6723512 baseEnd_6723512 := by
    simpa [prefixWord, tailWord_6723512, baseEnd_6723512] using wordTrace_append hprefix tailTrace_6723512
  have hstable : (prefixWord ++ tailWord_6723512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723512).length < 2 ^ (prefixWord ++ tailWord_6723512).sum := by decide
  have hdescent : baseEnd_6723512 < baseStart_6723512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723532 : List Nat := [2, 2, 1, 4, 1, 3, 2, 8]
def baseStart_6723532 : Nat := 118140960795 + 6723532 * 2 ^ 59
def prefixEnd_6723532 : Nat := 4983230072969 + 3 ^ 40 * 6723532 * 2
def baseEnd_6723532 : Nat := 127866800440203458660335

theorem tailTrace_6723532 : CollatzResearch.WordTrace tailWord_6723532 prefixEnd_6723532 127866800440203458660335 := by
  unfold tailWord_6723532
  simp only [CollatzResearch.WordTrace]
  refine ⟨122613679138899663345422425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163484905518532884460563233 122613679138899663345422425)
  ·
    refine ⟨91960259354174747509066819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122613679138899663345422425 91960259354174747509066819)
    ·
      refine ⟨137940389031262121263600229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91960259354174747509066819 137940389031262121263600229)
      ·
        refine ⟨25863822943361647736925043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137940389031262121263600229 25863822943361647736925043)
        ·
          refine ⟨38795734415042471605387565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25863822943361647736925043 38795734415042471605387565)
          ·
            refine ⟨14548400405640926852020337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38795734415042471605387565 14548400405640926852020337)
            ·
              refine ⟨10911300304230695139015253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14548400405640926852020337 10911300304230695139015253)
              ·
                refine ⟨127866800440203458660335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10911300304230695139015253 127866800440203458660335)
                ·
                  rfl

theorem cell23_6723532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 8].length) (baseStart_6723532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723532 prefixEnd_6723532 := by exact prefixLift 6723532
  have htrace : WordTrace (prefixWord ++ tailWord_6723532) baseStart_6723532 baseEnd_6723532 := by
    simpa [prefixWord, tailWord_6723532, baseEnd_6723532] using wordTrace_append hprefix tailTrace_6723532
  have hstable : (prefixWord ++ tailWord_6723532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723532).length < 2 ^ (prefixWord ++ tailWord_6723532).sum := by decide
  have hdescent : baseEnd_6723532 < baseStart_6723532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723535 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 6]
def baseStart_6723535 : Nat := 118140960795 + 6723535 * 2 ^ 59
def prefixEnd_6723535 : Nat := 4983230072969 + 3 ^ 40 * 6723535 * 2
def baseEnd_6723535 : Nat := 3452405152327456872091531

theorem tailTrace_6723535 : CollatzResearch.WordTrace tailWord_6723535 prefixEnd_6723535 3452405152327456872091531 := by
  unfold tailWord_6723535
  simp only [CollatzResearch.WordTrace]
  refine ⟨245227467696788458203204059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163484978464525638802136039 245227467696788458203204059)
  ·
    refine ⟨367841201545182687304806089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245227467696788458203204059 367841201545182687304806089)
    ·
      refine ⟨275880901158887015478604567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367841201545182687304806089 275880901158887015478604567)
      ·
        refine ⟨413821351738330523217906851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275880901158887015478604567 413821351738330523217906851)
        ·
          refine ⟨620732027607495784826860277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413821351738330523217906851 620732027607495784826860277)
          ·
            refine ⟨58193627588202729827518151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 620732027607495784826860277 58193627588202729827518151)
            ·
              refine ⟨87290441382304094741277227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58193627588202729827518151 87290441382304094741277227)
              ·
                refine ⟨130935662073456142111915841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87290441382304094741277227 130935662073456142111915841)
                ·
                  refine ⟨98201746555092106583936881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130935662073456142111915841 98201746555092106583936881)
                  ·
                    refine ⟨73651309916319079937952661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98201746555092106583936881 73651309916319079937952661)
                    ·
                      refine ⟨3452405152327456872091531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73651309916319079937952661 3452405152327456872091531)
                      ·
                        rfl

theorem cell23_6723535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_6723535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723535 prefixEnd_6723535 := by exact prefixLift 6723535
  have htrace : WordTrace (prefixWord ++ tailWord_6723535) baseStart_6723535 baseEnd_6723535 := by
    simpa [prefixWord, tailWord_6723535, baseEnd_6723535] using wordTrace_append hprefix tailTrace_6723535
  have hstable : (prefixWord ++ tailWord_6723535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723535).length < 2 ^ (prefixWord ++ tailWord_6723535).sum := by decide
  have hdescent : baseEnd_6723535 < baseStart_6723535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723575 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 5, 8]
def baseStart_6723575 : Nat := 118140960795 + 6723575 * 2 ^ 59
def prefixEnd_6723575 : Nat := 4983230072969 + 3 ^ 40 * 6723575 * 2
def baseEnd_6723575 : Nat := 1150808563851212238530449

theorem tailTrace_6723575 : CollatzResearch.WordTrace tailWord_6723575 prefixEnd_6723575 1150808563851212238530449 := by
  unfold tailWord_6723575
  simp only [CollatzResearch.WordTrace]
  refine ⟨245228926616643545034660179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163485951077762363356440119 245228926616643545034660179)
  ·
    refine ⟨367843389924965317551990269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245228926616643545034660179 367843389924965317551990269)
    ·
      refine ⟨137941271221861994081996351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 367843389924965317551990269 137941271221861994081996351)
      ·
        refine ⟨206911906832792991122994527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137941271221861994081996351 206911906832792991122994527)
        ·
          refine ⟨310367860249189486684491791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206911906832792991122994527 310367860249189486684491791)
          ·
            refine ⟨465551790373784230026737687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310367860249189486684491791 465551790373784230026737687)
            ·
              refine ⟨698327685560676345040106531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465551790373784230026737687 698327685560676345040106531)
              ·
                refine ⟨1047491528341014517560159797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698327685560676345040106531 1047491528341014517560159797)
                ·
                  refine ⟨98202330781970111021264981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1047491528341014517560159797 98202330781970111021264981)
                  ·
                    refine ⟨1150808563851212238530449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98202330781970111021264981 1150808563851212238530449)
                    ·
                      rfl

theorem cell23_6723575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_6723575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723575 prefixEnd_6723575 := by exact prefixLift 6723575
  have htrace : WordTrace (prefixWord ++ tailWord_6723575) baseStart_6723575 baseEnd_6723575 := by
    simpa [prefixWord, tailWord_6723575, baseEnd_6723575] using wordTrace_append hprefix tailTrace_6723575
  have hstable : (prefixWord ++ tailWord_6723575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723575).length < 2 ^ (prefixWord ++ tailWord_6723575).sum := by decide
  have hdescent : baseEnd_6723575 < baseStart_6723575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723592 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 2, 6]
def baseStart_6723592 : Nat := 118140960795 + 6723592 * 2 ^ 59
def prefixEnd_6723592 : Nat := 4983230072969 + 3 ^ 40 * 6723592 * 2
def baseEnd_6723592 : Nat := 1150811473574921049692923

theorem tailTrace_6723592 : CollatzResearch.WordTrace tailWord_6723592 prefixEnd_6723592 1150811473574921049692923 := by
  unfold tailWord_6723592
  simp only [CollatzResearch.WordTrace]
  refine ⟨122614773328790978469014515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163486364438387971292019353 122614773328790978469014515)
  ·
    refine ⟨183922159993186467703521773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122614773328790978469014515 183922159993186467703521773)
    ·
      refine ⟨68970809997444925388820665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183922159993186467703521773 68970809997444925388820665)
      ·
        refine ⟨51728107498083694041615499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68970809997444925388820665 51728107498083694041615499)
        ·
          refine ⟨77592161247125541062423249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51728107498083694041615499 77592161247125541062423249)
          ·
            refine ⟨58194120935344155796817437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77592161247125541062423249 58194120935344155796817437)
            ·
              refine ⟨21822795350754058423806539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58194120935344155796817437 21822795350754058423806539)
              ·
                refine ⟨32734193026131087635709809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21822795350754058423806539 32734193026131087635709809)
                ·
                  refine ⟨24550644769598315726782357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32734193026131087635709809 24550644769598315726782357)
                  ·
                    refine ⟨1150811473574921049692923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24550644769598315726782357 1150811473574921049692923)
                    ·
                      rfl

theorem cell23_6723592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_6723592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723592 prefixEnd_6723592 := by exact prefixLift 6723592
  have htrace : WordTrace (prefixWord ++ tailWord_6723592) baseStart_6723592 baseEnd_6723592 := by
    simpa [prefixWord, tailWord_6723592, baseEnd_6723592] using wordTrace_append hprefix tailTrace_6723592
  have hstable : (prefixWord ++ tailWord_6723592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723592).length < 2 ^ (prefixWord ++ tailWord_6723592).sum := by decide
  have hdescent : baseEnd_6723592 < baseStart_6723592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723633 : List Nat := [1, 2, 2, 3, 1, 3, 3, 2, 2, 2, 2]
def baseStart_6723633 : Nat := 118140960795 + 6723633 * 2 ^ 59
def prefixEnd_6723633 : Nat := 4983230072969 + 3 ^ 40 * 6723633 * 2
def baseEnd_6723633 : Nat := 3452455473431597488666081

theorem tailTrace_6723633 : CollatzResearch.WordTrace tailWord_6723633 prefixEnd_6723633 3452455473431597488666081 := by
  unfold tailWord_6723633
  simp only [CollatzResearch.WordTrace]
  refine ⟨245231042050433420940271553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163487361366955613960181035 245231042050433420940271553)
  ·
    refine ⟨183923281537825065705203665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245231042050433420940271553 183923281537825065705203665)
    ·
      refine ⟨137942461153368799278902749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183923281537825065705203665 137942461153368799278902749)
      ·
        refine ⟨51728422932513299729588531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137942461153368799278902749 51728422932513299729588531)
        ·
          refine ⟨77592634398769949594382797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51728422932513299729588531 77592634398769949594382797)
          ·
            refine ⟨29097237899538731097893549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77592634398769949594382797 29097237899538731097893549)
            ·
              refine ⟨10911464212327024161710081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29097237899538731097893549 10911464212327024161710081)
              ·
                refine ⟨8183598159245268121282561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10911464212327024161710081 8183598159245268121282561)
                ·
                  refine ⟨6137698619433951090961921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8183598159245268121282561 6137698619433951090961921)
                  ·
                    refine ⟨4603273964575463318221441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6137698619433951090961921 4603273964575463318221441)
                    ·
                      refine ⟨3452455473431597488666081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4603273964575463318221441 3452455473431597488666081)
                      ·
                        rfl

theorem cell23_6723633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_6723633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723633 prefixEnd_6723633 := by exact prefixLift 6723633
  have htrace : WordTrace (prefixWord ++ tailWord_6723633) baseStart_6723633 baseEnd_6723633 := by
    simpa [prefixWord, tailWord_6723633, baseEnd_6723633] using wordTrace_append hprefix tailTrace_6723633
  have hstable : (prefixWord ++ tailWord_6723633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723633).length < 2 ^ (prefixWord ++ tailWord_6723633).sum := by decide
  have hdescent : baseEnd_6723633 < baseStart_6723633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723639 : List Nat := [1, 1, 3, 1, 2, 2, 4, 4, 5]
def baseStart_6723639 : Nat := 118140960795 + 6723639 * 2 ^ 59
def prefixEnd_6723639 : Nat := 4983230072969 + 3 ^ 40 * 6723639 * 2
def baseEnd_6723639 : Nat := 383606506035058273910117

theorem tailTrace_6723639 : CollatzResearch.WordTrace tailWord_6723639 prefixEnd_6723639 383606506035058273910117 := by
  unfold tailWord_6723639
  simp only [CollatzResearch.WordTrace]
  refine ⟨245231260888411683964989971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163487507258941122643326647 245231260888411683964989971)
  ·
    refine ⟨367846891332617525947484957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245231260888411683964989971 367846891332617525947484957)
    ·
      refine ⟨137942584249731572230306859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 367846891332617525947484957 137942584249731572230306859)
      ·
        refine ⟨206913876374597358345460289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137942584249731572230306859 206913876374597358345460289)
        ·
          refine ⟨155185407280948018759095217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206913876374597358345460289 155185407280948018759095217)
          ·
            refine ⟨116389055460711014069321413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155185407280948018759095217 116389055460711014069321413)
            ·
              refine ⟨21822947898883315137997765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116389055460711014069321413 21822947898883315137997765)
              ·
                refine ⟨4091802731040621588374581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21822947898883315137997765 4091802731040621588374581)
                ·
                  refine ⟨383606506035058273910117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4091802731040621588374581 383606506035058273910117)
                  ·
                    rfl

theorem cell23_6723639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 5].length) (baseStart_6723639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723639 prefixEnd_6723639 := by exact prefixLift 6723639
  have htrace : WordTrace (prefixWord ++ tailWord_6723639) baseStart_6723639 baseEnd_6723639 := by
    simpa [prefixWord, tailWord_6723639, baseEnd_6723639] using wordTrace_append hprefix tailTrace_6723639
  have hstable : (prefixWord ++ tailWord_6723639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723639).length < 2 ^ (prefixWord ++ tailWord_6723639).sum := by decide
  have hdescent : baseEnd_6723639 < baseStart_6723639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723689 : List Nat := [1, 2, 1, 1, 1, 5, 3, 2, 2, 1, 4]
def baseStart_6723689 : Nat := 118140960795 + 6723689 * 2 ^ 59
def prefixEnd_6723689 : Nat := 4983230072969 + 3 ^ 40 * 6723689 * 2
def baseEnd_6723689 : Nat := 3452484228348249269565823

theorem tailTrace_6723689 : CollatzResearch.WordTrace tailWord_6723689 prefixEnd_6723689 3452484228348249269565823 := by
  unfold tailWord_6723689
  simp only [CollatzResearch.WordTrace]
  refine ⟨245233084538230542504310121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163488723025487028336206747 245233084538230542504310121)
  ·
    refine ⟨183924813403672906878232591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245233084538230542504310121 183924813403672906878232591)
    ·
      refine ⟨275887220105509360317348887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183924813403672906878232591 275887220105509360317348887)
      ·
        refine ⟨413830830158264040476023331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275887220105509360317348887 413830830158264040476023331)
        ·
          refine ⟨620746245237396060714034997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413830830158264040476023331 620746245237396060714034997)
          ·
            refine ⟨58194960491005880691940781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 620746245237396060714034997 58194960491005880691940781)
            ·
              refine ⟨21823110184127205259477793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58194960491005880691940781 21823110184127205259477793)
              ·
                refine ⟨16367332638095403944608345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21823110184127205259477793 16367332638095403944608345)
                ·
                  refine ⟨12275499478571552958456259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16367332638095403944608345 12275499478571552958456259)
                  ·
                    refine ⟨18413249217857329437684389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12275499478571552958456259 18413249217857329437684389)
                    ·
                      refine ⟨3452484228348249269565823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18413249217857329437684389 3452484228348249269565823)
                      ·
                        rfl

theorem cell23_6723689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 1, 4].length) (baseStart_6723689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723689 prefixEnd_6723689 := by exact prefixLift 6723689
  have htrace : WordTrace (prefixWord ++ tailWord_6723689) baseStart_6723689 baseEnd_6723689 := by
    simpa [prefixWord, tailWord_6723689, baseEnd_6723689] using wordTrace_append hprefix tailTrace_6723689
  have hstable : (prefixWord ++ tailWord_6723689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723689).length < 2 ^ (prefixWord ++ tailWord_6723689).sum := by decide
  have hdescent : baseEnd_6723689 < baseStart_6723689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723746 : List Nat := [3, 3, 1, 3, 1, 1, 1, 4, 6]
def baseStart_6723746 : Nat := 118140960795 + 6723746 * 2 ^ 59
def prefixEnd_6723746 : Nat := 4983230072969 + 3 ^ 40 * 6723746 * 2
def baseEnd_6723746 : Nat := 383612610749506171839229

theorem tailTrace_6723746 : CollatzResearch.WordTrace tailWord_6723746 prefixEnd_6723746 383612610749506171839229 := by
  unfold tailWord_6723746
  simp only [CollatzResearch.WordTrace]
  refine ⟨61308790874756010309783773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163490108999349360826090061 61308790874756010309783773)
  ·
    refine ⟨22990796578033503866168915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61308790874756010309783773 22990796578033503866168915)
    ·
      refine ⟨34486194867050255799253373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22990796578033503866168915 34486194867050255799253373)
      ·
        refine ⟨12932323075143845924720015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34486194867050255799253373 12932323075143845924720015)
        ·
          refine ⟨19398484612715768887080023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12932323075143845924720015 19398484612715768887080023)
          ·
            refine ⟨29097726919073653330620035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19398484612715768887080023 29097726919073653330620035)
            ·
              refine ⟨43646590378610479995930053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29097726919073653330620035 43646590378610479995930053)
              ·
                refine ⟨8183735695989464999236885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43646590378610479995930053 8183735695989464999236885)
                ·
                  refine ⟨383612610749506171839229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8183735695989464999236885 383612610749506171839229)
                  ·
                    rfl

theorem cell23_6723746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_6723746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723746 prefixEnd_6723746 := by exact prefixLift 6723746
  have htrace : WordTrace (prefixWord ++ tailWord_6723746) baseStart_6723746 baseEnd_6723746 := by
    simpa [prefixWord, tailWord_6723746, baseEnd_6723746] using wordTrace_append hprefix tailTrace_6723746
  have hstable : (prefixWord ++ tailWord_6723746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723746).length < 2 ^ (prefixWord ++ tailWord_6723746).sum := by decide
  have hdescent : baseEnd_6723746 < baseStart_6723746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723777 : List Nat := [1, 2, 6, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_6723777 : Nat := 118140960795 + 6723777 * 2 ^ 59
def prefixEnd_6723777 : Nat := 4983230072969 + 3 ^ 40 * 6723777 * 2
def baseEnd_6723777 : Nat := 3452529414645844925265419

theorem tailTrace_6723777 : CollatzResearch.WordTrace tailWord_6723777 prefixEnd_6723777 3452529414645844925265419 := by
  unfold tailWord_6723777
  simp only [CollatzResearch.WordTrace]
  refine ⟨245236294161911733533513585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163490862774607822355675723 245236294161911733533513585)
  ·
    refine ⟨183927220621433800150135189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245236294161911733533513585 183927220621433800150135189)
    ·
      refine ⟨8621588466629709382037587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 183927220621433800150135189 8621588466629709382037587)
      ·
        refine ⟨12932382699944564073056381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8621588466629709382037587 12932382699944564073056381)
        ·
          refine ⟨4849643512479211527396143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12932382699944564073056381 4849643512479211527396143)
          ·
            refine ⟨7274465268718817291094215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4849643512479211527396143 7274465268718817291094215)
            ·
              refine ⟨10911697903078225936641323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7274465268718817291094215 10911697903078225936641323)
              ·
                refine ⟨16367546854617338904961985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10911697903078225936641323 16367546854617338904961985)
                ·
                  refine ⟨12275660140963004178721489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16367546854617338904961985 12275660140963004178721489)
                  ·
                    refine ⟨9206745105722253134041117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12275660140963004178721489 9206745105722253134041117)
                    ·
                      refine ⟨3452529414645844925265419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9206745105722253134041117 3452529414645844925265419)
                      ·
                        rfl

theorem cell23_6723777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_6723777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723777 prefixEnd_6723777 := by exact prefixLift 6723777
  have htrace : WordTrace (prefixWord ++ tailWord_6723777) baseStart_6723777 baseEnd_6723777 := by
    simpa [prefixWord, tailWord_6723777, baseEnd_6723777] using wordTrace_append hprefix tailTrace_6723777
  have hstable : (prefixWord ++ tailWord_6723777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723777).length < 2 ^ (prefixWord ++ tailWord_6723777).sum := by decide
  have hdescent : baseEnd_6723777 < baseStart_6723777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723790 : List Nat := [4, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3]
def baseStart_6723790 : Nat := 118140960795 + 6723790 * 2 ^ 59
def prefixEnd_6723790 : Nat := 4983230072969 + 3 ^ 40 * 6723790 * 2
def baseEnd_6723790 : Nat := 3452536089894353374402859

theorem tailTrace_6723790 : CollatzResearch.WordTrace tailWord_6723790 prefixEnd_6723790 3452536089894353374402859 := by
  unfold tailWord_6723790
  simp only [CollatzResearch.WordTrace]
  refine ⟨30654596038858079594217103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163491178873909757835824549 30654596038858079594217103)
  ·
    refine ⟨45981894058287119391325655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30654596038858079594217103 45981894058287119391325655)
    ·
      refine ⟨68972841087430679086988483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45981894058287119391325655 68972841087430679086988483)
      ·
        refine ⟨103459261631146018630482725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68972841087430679086988483 103459261631146018630482725)
        ·
          refine ⟨19398611555839878493215511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103459261631146018630482725 19398611555839878493215511)
          ·
            refine ⟨29097917333759817739823267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19398611555839878493215511 29097917333759817739823267)
            ·
              refine ⟨43646876000639726609734901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29097917333759817739823267 43646876000639726609734901)
              ·
                refine ⟨4091894625059974369662647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43646876000639726609734901 4091894625059974369662647)
                ·
                  refine ⟨6137841937589961554493971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4091894625059974369662647 6137841937589961554493971)
                  ·
                    refine ⟨9206762906384942331740957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6137841937589961554493971 9206762906384942331740957)
                    ·
                      refine ⟨3452536089894353374402859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9206762906384942331740957 3452536089894353374402859)
                      ·
                        rfl

theorem cell23_6723790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3].length) (baseStart_6723790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723790 prefixEnd_6723790 := by exact prefixLift 6723790
  have htrace : WordTrace (prefixWord ++ tailWord_6723790) baseStart_6723790 baseEnd_6723790 := by
    simpa [prefixWord, tailWord_6723790, baseEnd_6723790] using wordTrace_append hprefix tailTrace_6723790
  have hstable : (prefixWord ++ tailWord_6723790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723790).length < 2 ^ (prefixWord ++ tailWord_6723790).sum := by decide
  have hdescent : baseEnd_6723790 < baseStart_6723790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723799 : List Nat := [1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 5]
def baseStart_6723799 : Nat := 118140960795 + 6723799 * 2 ^ 59
def prefixEnd_6723799 : Nat := 4983230072969 + 3 ^ 40 * 6723799 * 2
def baseEnd_6723799 : Nat := 3452540711220243839190317

theorem tailTrace_6723799 : CollatzResearch.WordTrace tailWord_6723799 prefixEnd_6723799 3452540711220243839190317 := by
  unfold tailWord_6723799
  simp only [CollatzResearch.WordTrace]
  refine ⟨245237096567832031290814451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163491397711888020860542967 245237096567832031290814451)
  ·
    refine ⟨367855644851748046936221677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245237096567832031290814451 367855644851748046936221677)
    ·
      refine ⟨137945866819405517601083129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 367855644851748046936221677 137945866819405517601083129)
      ·
        refine ⟨103459400114554138200812347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137945866819405517601083129 103459400114554138200812347)
        ·
          refine ⟨155189100171831207301218521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103459400114554138200812347 155189100171831207301218521)
          ·
            refine ⟨116391825128873405475913891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155189100171831207301218521 116391825128873405475913891)
            ·
              refine ⟨174587737693310108213870837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116391825128873405475913891 174587737693310108213870837)
              ·
                refine ⟨16367600408747822645050391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 174587737693310108213870837 16367600408747822645050391)
                ·
                  refine ⟨24551400613121733967575587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16367600408747822645050391 24551400613121733967575587)
                  ·
                    refine ⟨36827100919682600951363381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24551400613121733967575587 36827100919682600951363381)
                    ·
                      refine ⟨3452540711220243839190317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36827100919682600951363381 3452540711220243839190317)
                      ·
                        rfl

theorem cell23_6723799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_6723799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723799 prefixEnd_6723799 := by exact prefixLift 6723799
  have htrace : WordTrace (prefixWord ++ tailWord_6723799) baseStart_6723799 baseEnd_6723799 := by
    simpa [prefixWord, tailWord_6723799, baseEnd_6723799] using wordTrace_append hprefix tailTrace_6723799
  have hstable : (prefixWord ++ tailWord_6723799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723799).length < 2 ^ (prefixWord ++ tailWord_6723799).sum := by decide
  have hdescent : baseEnd_6723799 < baseStart_6723799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723809 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 1, 1, 6]
def baseStart_6723809 : Nat := 118140960795 + 6723809 * 2 ^ 59
def prefixEnd_6723809 : Nat := 4983230072969 + 3 ^ 40 * 6723809 * 2
def baseEnd_6723809 : Nat := 3452545846026788800065271

theorem tailTrace_6723809 : CollatzResearch.WordTrace tailWord_6723809 prefixEnd_6723809 3452545846026788800065271 := by
  unfold tailWord_6723809
  simp only [CollatzResearch.WordTrace]
  refine ⟨245237461297795802998678481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163491640865197201999118987 245237461297795802998678481)
  ·
    refine ⟨183928095973346852249008861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245237461297795802998678481 183928095973346852249008861)
    ·
      refine ⟨68973035990005069593378323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183928095973346852249008861 68973035990005069593378323)
      ·
        refine ⟨103459553985007604390067485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68973035990005069593378323 103459553985007604390067485)
        ·
          refine ⟨38797332744377851646275307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103459553985007604390067485 38797332744377851646275307)
          ·
            refine ⟨58195999116566777469412961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38797332744377851646275307 58195999116566777469412961)
            ·
              refine ⟨43646999337425083102059721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58195999116566777469412961 43646999337425083102059721)
              ·
                refine ⟨32735249503068812326544791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43646999337425083102059721 32735249503068812326544791)
                ·
                  refine ⟨49102874254603218489817187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32735249503068812326544791 49102874254603218489817187)
                  ·
                    refine ⟨73654311381904827734725781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49102874254603218489817187 73654311381904827734725781)
                    ·
                      refine ⟨3452545846026788800065271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73654311381904827734725781 3452545846026788800065271)
                      ·
                        rfl

theorem cell23_6723809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_6723809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723809 prefixEnd_6723809 := by exact prefixLift 6723809
  have htrace : WordTrace (prefixWord ++ tailWord_6723809) baseStart_6723809 baseEnd_6723809 := by
    simpa [prefixWord, tailWord_6723809, baseEnd_6723809] using wordTrace_append hprefix tailTrace_6723809
  have hstable : (prefixWord ++ tailWord_6723809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723809).length < 2 ^ (prefixWord ++ tailWord_6723809).sum := by decide
  have hdescent : baseEnd_6723809 < baseStart_6723809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723816 : List Nat := [2, 1, 4, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_6723816 : Nat := 118140960795 + 6723816 * 2 ^ 59
def prefixEnd_6723816 : Nat := 4983230072969 + 3 ^ 40 * 6723816 * 2
def baseEnd_6723816 : Nat := 3452549440391370272677739

theorem tailTrace_6723816 : CollatzResearch.WordTrace tailWord_6723816 prefixEnd_6723816 3452549440391370272677739 := by
  unfold tailWord_6723816
  simp only [CollatzResearch.WordTrace]
  refine ⟨122618858304385221597091651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163491811072513628796122201 122618858304385221597091651)
  ·
    refine ⟨183928287456577832395637477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122618858304385221597091651 183928287456577832395637477)
    ·
      refine ⟨34486553898108343574182027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183928287456577832395637477 34486553898108343574182027)
      ·
        refine ⟨51729830847162515361273041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34486553898108343574182027 51729830847162515361273041)
        ·
          refine ⟨38797373135371886520954781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51729830847162515361273041 38797373135371886520954781)
          ·
            refine ⟨14549014925764457445358043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38797373135371886520954781 14549014925764457445358043)
            ·
              refine ⟨21823522388646686168037065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14549014925764457445358043 21823522388646686168037065)
              ·
                refine ⟨16367641791485014626027799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21823522388646686168037065 16367641791485014626027799)
                ·
                  refine ⟨24551462687227521939041699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16367641791485014626027799 24551462687227521939041699)
                  ·
                    refine ⟨36827194030841282908562549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24551462687227521939041699 36827194030841282908562549)
                    ·
                      refine ⟨3452549440391370272677739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36827194030841282908562549 3452549440391370272677739)
                      ·
                        rfl

theorem cell23_6723816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_6723816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723816 prefixEnd_6723816 := by exact prefixLift 6723816
  have htrace : WordTrace (prefixWord ++ tailWord_6723816) baseStart_6723816 baseEnd_6723816 := by
    simpa [prefixWord, tailWord_6723816, baseEnd_6723816] using wordTrace_append hprefix tailTrace_6723816
  have hstable : (prefixWord ++ tailWord_6723816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723816).length < 2 ^ (prefixWord ++ tailWord_6723816).sum := by decide
  have hdescent : baseEnd_6723816 < baseStart_6723816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723826 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 1, 1, 6]
def baseStart_6723826 : Nat := 118140960795 + 6723826 * 2 ^ 59
def prefixEnd_6723826 : Nat := 4983230072969 + 3 ^ 40 * 6723826 * 2
def baseEnd_6723826 : Nat := 3452554575197915233552693

theorem tailTrace_6723826 : CollatzResearch.WordTrace tailWord_6723826 prefixEnd_6723826 3452554575197915233552693 := by
  unfold tailWord_6723826
  simp only [CollatzResearch.WordTrace]
  refine ⟨61309520334683553725511833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163492054225822809934698221 61309520334683553725511833)
  ·
    refine ⟨45982140251012665294133875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61309520334683553725511833 45982140251012665294133875)
    ·
      refine ⟨68973210376518997941200813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45982140251012665294133875 68973210376518997941200813)
      ·
        refine ⟨25864953891194624227950305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68973210376518997941200813 25864953891194624227950305)
        ·
          refine ⟨19398715418395968170962729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25864953891194624227950305 19398715418395968170962729)
          ·
            refine ⟨14549036563796976128222047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19398715418395968170962729 14549036563796976128222047)
            ·
              refine ⟨21823554845695464192333071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14549036563796976128222047 21823554845695464192333071)
              ·
                refine ⟨32735332268543196288499607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21823554845695464192333071 32735332268543196288499607)
                ·
                  refine ⟨49102998402814794432749411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32735332268543196288499607 49102998402814794432749411)
                  ·
                    refine ⟨73654497604222191649124117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49102998402814794432749411 73654497604222191649124117)
                    ·
                      refine ⟨3452554575197915233552693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73654497604222191649124117 3452554575197915233552693)
                      ·
                        rfl

theorem cell23_6723826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_6723826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723826 prefixEnd_6723826 := by exact prefixLift 6723826
  have htrace : WordTrace (prefixWord ++ tailWord_6723826) baseStart_6723826 baseEnd_6723826 := by
    simpa [prefixWord, tailWord_6723826, baseEnd_6723826] using wordTrace_append hprefix tailTrace_6723826
  have hstable : (prefixWord ++ tailWord_6723826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723826).length < 2 ^ (prefixWord ++ tailWord_6723826).sum := by decide
  have hdescent : baseEnd_6723826 < baseStart_6723826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723830 : List Nat := [5, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2]
def baseStart_6723830 : Nat := 118140960795 + 6723830 * 2 ^ 59
def prefixEnd_6723830 : Nat := 4983230072969 + 3 ^ 40 * 6723830 * 2
def baseEnd_6723830 : Nat := 3452556629120533217902675

theorem tailTrace_6723830 : CollatzResearch.WordTrace tailWord_6723830 prefixEnd_6723830 3452556629120533217902675 := by
  unfold tailWord_6723830
  simp only [CollatzResearch.WordTrace]
  refine ⟨15327389201919982724074559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163492151487146482390128629 15327389201919982724074559)
  ·
    refine ⟨22991083802879974086111839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15327389201919982724074559 22991083802879974086111839)
    ·
      refine ⟨34486625704319961129167759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22991083802879974086111839 34486625704319961129167759)
      ·
        refine ⟨51729938556479941693751639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34486625704319961129167759 51729938556479941693751639)
        ·
          refine ⟨77594907834719912540627459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51729938556479941693751639 77594907834719912540627459)
          ·
            refine ⟨116392361752079868810941189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77594907834719912540627459 116392361752079868810941189)
            ·
              refine ⟨21823567828514975402051473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116392361752079868810941189 21823567828514975402051473)
              ·
                refine ⟨16367675871386231551538605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21823567828514975402051473 16367675871386231551538605)
                ·
                  refine ⟨6137878451769836831826977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16367675871386231551538605 6137878451769836831826977)
                  ·
                    refine ⟨4603408838827377623870233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6137878451769836831826977 4603408838827377623870233)
                    ·
                      refine ⟨3452556629120533217902675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4603408838827377623870233 3452556629120533217902675)
                      ·
                        rfl

theorem cell23_6723830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_6723830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723830 prefixEnd_6723830 := by exact prefixLift 6723830
  have htrace : WordTrace (prefixWord ++ tailWord_6723830) baseStart_6723830 baseEnd_6723830 := by
    simpa [prefixWord, tailWord_6723830, baseEnd_6723830] using wordTrace_append hprefix tailTrace_6723830
  have hstable : (prefixWord ++ tailWord_6723830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723830).length < 2 ^ (prefixWord ++ tailWord_6723830).sum := by decide
  have hdescent : baseEnd_6723830 < baseStart_6723830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723836 : List Nat := [2, 2, 2, 1, 4, 1, 4, 7]
def baseStart_6723836 : Nat := 118140960795 + 6723836 * 2 ^ 59
def prefixEnd_6723836 : Nat := 4983230072969 + 3 ^ 40 * 6723836 * 2
def baseEnd_6723836 : Nat := 127872581852017044238061

theorem tailTrace_6723836 : CollatzResearch.WordTrace tailWord_6723836 prefixEnd_6723836 127872581852017044238061 := by
  unfold tailWord_6723836
  simp only [CollatzResearch.WordTrace]
  refine ⟨122619223034348993304955681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163492297379131991073274241 122619223034348993304955681)
  ·
    refine ⟨91964417275761744978716761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122619223034348993304955681 91964417275761744978716761)
    ·
      refine ⟨68973312956821308734037571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91964417275761744978716761 68973312956821308734037571)
      ·
        refine ⟨103459969435231963101056357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68973312956821308734037571 103459969435231963101056357)
        ·
          refine ⟨19398744269105993081448067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103459969435231963101056357 19398744269105993081448067)
          ·
            refine ⟨29098116403658989622172101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19398744269105993081448067 29098116403658989622172101)
            ·
              refine ⟨5455896825686060554157269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29098116403658989622172101 5455896825686060554157269)
              ·
                refine ⟨127872581852017044238061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5455896825686060554157269 127872581852017044238061)
                ·
                  rfl

theorem cell23_6723836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 7].length) (baseStart_6723836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723836 prefixEnd_6723836 := by exact prefixLift 6723836
  have htrace : WordTrace (prefixWord ++ tailWord_6723836) baseStart_6723836 baseEnd_6723836 := by
    simpa [prefixWord, tailWord_6723836, baseEnd_6723836] using wordTrace_append hprefix tailTrace_6723836
  have hstable : (prefixWord ++ tailWord_6723836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723836).length < 2 ^ (prefixWord ++ tailWord_6723836).sum := by decide
  have hdescent : baseEnd_6723836 < baseStart_6723836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723863 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 4, 1, 3]
def baseStart_6723863 : Nat := 118140960795 + 6723863 * 2 ^ 59
def prefixEnd_6723863 : Nat := 4983230072969 + 3 ^ 40 * 6723863 * 2
def baseEnd_6723863 : Nat := 3452573573982131588790023

theorem tailTrace_6723863 : CollatzResearch.WordTrace tailWord_6723863 prefixEnd_6723863 3452573573982131588790023 := by
  unfold tailWord_6723863
  simp only [CollatzResearch.WordTrace]
  refine ⟨245239430839600170221144243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163492953893066780147429495 245239430839600170221144243)
  ·
    refine ⟨367859146259400255331716365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245239430839600170221144243 367859146259400255331716365)
    ·
      refine ⟨137947179847275095749393637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 367859146259400255331716365 137947179847275095749393637)
      ·
        refine ⟨25865096221364080453011307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137947179847275095749393637 25865096221364080453011307)
        ·
          refine ⟨38797644332046120679516961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25865096221364080453011307 38797644332046120679516961)
          ·
            refine ⟨29098233249034590509637721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38797644332046120679516961 29098233249034590509637721)
            ·
              refine ⟨21823674936775942882228291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29098233249034590509637721 21823674936775942882228291)
              ·
                refine ⟨32735512405163914323342437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21823674936775942882228291 32735512405163914323342437)
                ·
                  refine ⟨6137908575968233935626707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32735512405163914323342437 6137908575968233935626707)
                  ·
                    refine ⟨9206862863952350903440061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6137908575968233935626707 9206862863952350903440061)
                    ·
                      refine ⟨3452573573982131588790023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9206862863952350903440061 3452573573982131588790023)
                      ·
                        rfl

theorem cell23_6723863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_6723863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723863 prefixEnd_6723863 := by exact prefixLift 6723863
  have htrace : WordTrace (prefixWord ++ tailWord_6723863) baseStart_6723863 baseEnd_6723863 := by
    simpa [prefixWord, tailWord_6723863, baseEnd_6723863] using wordTrace_append hprefix tailTrace_6723863
  have hstable : (prefixWord ++ tailWord_6723863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723863).length < 2 ^ (prefixWord ++ tailWord_6723863).sum := by decide
  have hdescent : baseEnd_6723863 < baseStart_6723863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723890 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2]
def baseStart_6723890 : Nat := 118140960795 + 6723890 * 2 ^ 59
def prefixEnd_6723890 : Nat := 4983230072969 + 3 ^ 40 * 6723890 * 2
def baseEnd_6723890 : Nat := 3452587437959802983152399

theorem tailTrace_6723890 : CollatzResearch.WordTrace tailWord_6723890 prefixEnd_6723890 3452587437959802983152399 := by
  unfold tailWord_6723890
  simp only [CollatzResearch.WordTrace]
  refine ⟨61310103902625588458094281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163493610407001569221584749 61310103902625588458094281)
  ·
    refine ⟨45982577926969191343570711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61310103902625588458094281 45982577926969191343570711)
    ·
      refine ⟨68973866890453787015356067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45982577926969191343570711 68973866890453787015356067)
      ·
        refine ⟨103460800335680680523034101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68973866890453787015356067 103460800335680680523034101)
        ·
          refine ⟨9699450031470063799034447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103460800335680680523034101 9699450031470063799034447)
          ·
            refine ⟨14549175047205095698551671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9699450031470063799034447 14549175047205095698551671)
            ·
              refine ⟨21823762570807643547827507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14549175047205095698551671 21823762570807643547827507)
              ·
                refine ⟨32735643856211465321741261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21823762570807643547827507 32735643856211465321741261)
                ·
                  refine ⟨12275866446079299495652973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32735643856211465321741261 12275866446079299495652973)
                  ·
                    refine ⟨4603449917279737310869865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12275866446079299495652973 4603449917279737310869865)
                    ·
                      refine ⟨3452587437959802983152399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4603449917279737310869865 3452587437959802983152399)
                      ·
                        rfl

theorem cell23_6723890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2].length) (baseStart_6723890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723890 prefixEnd_6723890 := by exact prefixLift 6723890
  have htrace : WordTrace (prefixWord ++ tailWord_6723890) baseStart_6723890 baseEnd_6723890 := by
    simpa [prefixWord, tailWord_6723890, baseEnd_6723890] using wordTrace_append hprefix tailTrace_6723890
  have hstable : (prefixWord ++ tailWord_6723890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723890).length < 2 ^ (prefixWord ++ tailWord_6723890).sum := by decide
  have hdescent : baseEnd_6723890 < baseStart_6723890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723903 : List Nat := [1, 1, 2, 2, 4, 1, 3, 2, 1, 4, 2]
def baseStart_6723903 : Nat := 118140960795 + 6723903 * 2 ^ 59
def prefixEnd_6723903 : Nat := 4983230072969 + 3 ^ 40 * 6723903 * 2
def baseEnd_6723903 : Nat := 3452594113208311432289839

theorem tailTrace_6723903 : CollatzResearch.WordTrace tailWord_6723903 prefixEnd_6723903 3452594113208311432289839 := by
  unfold tailWord_6723903
  simp only [CollatzResearch.WordTrace]
  refine ⟨245240889759455257052600363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163493926506303504701733575 245240889759455257052600363)
  ·
    refine ⟨367861334639182885578900545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245240889759455257052600363 367861334639182885578900545)
    ·
      refine ⟨275896000979387164184175409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367861334639182885578900545 275896000979387164184175409)
      ·
        refine ⟨206922000734540373138131557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275896000979387164184175409 206922000734540373138131557)
        ·
          refine ⟨38797875137726319963399667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206922000734540373138131557 38797875137726319963399667)
          ·
            refine ⟨58196812706589479945099501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38797875137726319963399667 58196812706589479945099501)
            ·
              refine ⟨21823804764971054979412313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58196812706589479945099501 21823804764971054979412313)
              ·
                refine ⟨16367853573728291234559235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21823804764971054979412313 16367853573728291234559235)
                ·
                  refine ⟨24551780360592436851838853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16367853573728291234559235 24551780360592436851838853)
                  ·
                    refine ⟨4603458817611081909719785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24551780360592436851838853 4603458817611081909719785)
                    ·
                      refine ⟨3452594113208311432289839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4603458817611081909719785 3452594113208311432289839)
                      ·
                        rfl

theorem cell23_6723903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 4, 2].length) (baseStart_6723903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723903 prefixEnd_6723903 := by exact prefixLift 6723903
  have htrace : WordTrace (prefixWord ++ tailWord_6723903) baseStart_6723903 baseEnd_6723903 := by
    simpa [prefixWord, tailWord_6723903, baseEnd_6723903] using wordTrace_append hprefix tailTrace_6723903
  have hstable : (prefixWord ++ tailWord_6723903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723903).length < 2 ^ (prefixWord ++ tailWord_6723903).sum := by decide
  have hdescent : baseEnd_6723903 < baseStart_6723903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723916 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 2, 2, 4]
def baseStart_6723916 : Nat := 118140960795 + 6723916 * 2 ^ 59
def prefixEnd_6723916 : Nat := 4983230072969 + 3 ^ 40 * 6723916 * 2
def baseEnd_6723916 : Nat := 3452600788456819881427279

theorem tailTrace_6723916 : CollatzResearch.WordTrace tailWord_6723916 prefixEnd_6723916 3452600788456819881427279 := by
  unfold tailWord_6723916
  simp only [CollatzResearch.WordTrace]
  refine ⟨122620681954204080136411801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163494242605605440181882401 122620681954204080136411801)
  ·
    refine ⟨91965511465653060102308851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122620681954204080136411801 91965511465653060102308851)
    ·
      refine ⟨137948267198479590153463277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91965511465653060102308851 137948267198479590153463277)
      ·
        refine ⟨51730600199429846307548729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137948267198479590153463277 51730600199429846307548729)
        ·
          refine ⟨38797950149572384730661547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51730600199429846307548729 38797950149572384730661547)
          ·
            refine ⟨58196925224358577095992321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38797950149572384730661547 58196925224358577095992321)
            ·
              refine ⟨43647693918268932821994241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58196925224358577095992321 43647693918268932821994241)
              ·
                refine ⟨32735770438701699616495681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43647693918268932821994241 32735770438701699616495681)
                ·
                  refine ⟨24551827829026274712371761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32735770438701699616495681 24551827829026274712371761)
                  ·
                    refine ⟨18413870871769706034278821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24551827829026274712371761 18413870871769706034278821)
                    ·
                      refine ⟨3452600788456819881427279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18413870871769706034278821 3452600788456819881427279)
                      ·
                        rfl

theorem cell23_6723916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_6723916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723916 prefixEnd_6723916 := by exact prefixLift 6723916
  have htrace : WordTrace (prefixWord ++ tailWord_6723916) baseStart_6723916 baseEnd_6723916 := by
    simpa [prefixWord, tailWord_6723916, baseEnd_6723916] using wordTrace_append hprefix tailTrace_6723916
  have hstable : (prefixWord ++ tailWord_6723916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723916).length < 2 ^ (prefixWord ++ tailWord_6723916).sum := by decide
  have hdescent : baseEnd_6723916 < baseStart_6723916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723920 : List Nat := [2, 1, 1, 1, 1, 6, 1, 4, 2, 2, 2]
def baseStart_6723920 : Nat := 118140960795 + 6723920 * 2 ^ 59
def prefixEnd_6723920 : Nat := 4983230072969 + 3 ^ 40 * 6723920 * 2
def baseEnd_6723920 : Nat := 3452602842379437865777261

theorem tailTrace_6723920 : CollatzResearch.WordTrace tailWord_6723920 prefixEnd_6723920 3452602842379437865777261 := by
  unfold tailWord_6723920
  simp only [CollatzResearch.WordTrace]
  refine ⟨122620754900196834477984607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163494339866929112637312809 122620754900196834477984607)
  ·
    refine ⟨183931132350295251716976911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122620754900196834477984607 183931132350295251716976911)
    ·
      refine ⟨275896698525442877575465367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183931132350295251716976911 275896698525442877575465367)
      ·
        refine ⟨413845047788164316363198051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275896698525442877575465367 413845047788164316363198051)
        ·
          refine ⟨620767571682246474544797077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413845047788164316363198051 620767571682246474544797077)
          ·
            refine ⟨29098479922605303494287363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 620767571682246474544797077 29098479922605303494287363)
            ·
              refine ⟨43647719883907955241431045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29098479922605303494287363 43647719883907955241431045)
              ·
                refine ⟨8183947478232741607768321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43647719883907955241431045 8183947478232741607768321)
                ·
                  refine ⟨6137960608674556205826241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8183947478232741607768321 6137960608674556205826241)
                  ·
                    refine ⟨4603470456505917154369681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6137960608674556205826241 4603470456505917154369681)
                    ·
                      refine ⟨3452602842379437865777261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4603470456505917154369681 3452602842379437865777261)
                      ·
                        rfl

theorem cell23_6723920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 2, 2, 2].length) (baseStart_6723920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723920 prefixEnd_6723920 := by exact prefixLift 6723920
  have htrace : WordTrace (prefixWord ++ tailWord_6723920) baseStart_6723920 baseEnd_6723920 := by
    simpa [prefixWord, tailWord_6723920, baseEnd_6723920] using wordTrace_append hprefix tailTrace_6723920
  have hstable : (prefixWord ++ tailWord_6723920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723920).length < 2 ^ (prefixWord ++ tailWord_6723920).sum := by decide
  have hdescent : baseEnd_6723920 < baseStart_6723920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723929 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 8]
def baseStart_6723929 : Nat := 118140960795 + 6723929 * 2 ^ 59
def prefixEnd_6723929 : Nat := 4983230072969 + 3 ^ 40 * 6723929 * 2
def baseEnd_6723929 : Nat := 3452607463705328330564719

theorem tailTrace_6723929 : CollatzResearch.WordTrace tailWord_6723929 prefixEnd_6723929 3452607463705328330564719 := by
  unfold tailWord_6723929
  simp only [CollatzResearch.WordTrace]
  refine ⟨245241838057361063493046841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163494558704907375662031227 245241838057361063493046841)
  ·
    refine ⟨183931378543020797619785131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245241838057361063493046841 183931378543020797619785131)
    ·
      refine ⟨275897067814531196429677697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183931378543020797619785131 275897067814531196429677697)
      ·
        refine ⟨206922800860898397322258273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275897067814531196429677697 206922800860898397322258273)
        ·
          refine ⟨155192100645673797991693705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206922800860898397322258273 155192100645673797991693705)
          ·
            refine ⟨116394075484255348493770279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155192100645673797991693705 116394075484255348493770279)
            ·
              refine ⟨174591113226383022740655419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116394075484255348493770279 174591113226383022740655419)
              ·
                refine ⟨261886669839574534110983129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174591113226383022740655419 261886669839574534110983129)
                ·
                  refine ⟨196415002379680900583237347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261886669839574534110983129 196415002379680900583237347)
                  ·
                    refine ⟨294622503569521350874856021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 196415002379680900583237347 294622503569521350874856021)
                    ·
                      refine ⟨3452607463705328330564719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 294622503569521350874856021 3452607463705328330564719)
                      ·
                        rfl

theorem cell23_6723929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_6723929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723929 prefixEnd_6723929 := by exact prefixLift 6723929
  have htrace : WordTrace (prefixWord ++ tailWord_6723929) baseStart_6723929 baseEnd_6723929 := by
    simpa [prefixWord, tailWord_6723929, baseEnd_6723929] using wordTrace_append hprefix tailTrace_6723929
  have hstable : (prefixWord ++ tailWord_6723929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723929).length < 2 ^ (prefixWord ++ tailWord_6723929).sum := by decide
  have hdescent : baseEnd_6723929 < baseStart_6723929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723958 : List Nat := [5, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2]
def baseStart_6723958 : Nat := 118140960795 + 6723958 * 2 ^ 59
def prefixEnd_6723958 : Nat := 4983230072969 + 3 ^ 40 * 6723958 * 2
def baseEnd_6723958 : Nat := 3452622354644308717102087

theorem tailTrace_6723958 : CollatzResearch.WordTrace tailWord_6723958 prefixEnd_6723958 3452622354644308717102087 := by
  unfold tailWord_6723958
  simp only [CollatzResearch.WordTrace]
  refine ⟨15327680985891000090365783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163495263849504000963901685 15327680985891000090365783)
  ·
    refine ⟨22991521478836500135548675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15327680985891000090365783 22991521478836500135548675)
    ·
      refine ⟨34487282218254750203323013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22991521478836500135548675 34487282218254750203323013)
      ·
        refine ⟨6466365415922765663123065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34487282218254750203323013 6466365415922765663123065)
        ·
          refine ⟨4849774061942074247342299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6466365415922765663123065 4849774061942074247342299)
          ·
            refine ⟨7274661092913111371013449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4849774061942074247342299 7274661092913111371013449)
            ·
              refine ⟨5455995819684833528260087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7274661092913111371013449 5455995819684833528260087)
              ·
                refine ⟨8183993729527250292390131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5455995819684833528260087 8183993729527250292390131)
                ·
                  refine ⟨12275990594290875438585197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8183993729527250292390131 12275990594290875438585197)
                  ·
                    refine ⟨4603496472859078289469449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12275990594290875438585197 4603496472859078289469449)
                    ·
                      refine ⟨3452622354644308717102087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4603496472859078289469449 3452622354644308717102087)
                      ·
                        rfl

theorem cell23_6723958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_6723958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723958 prefixEnd_6723958 := by exact prefixLift 6723958
  have htrace : WordTrace (prefixWord ++ tailWord_6723958) baseStart_6723958 baseEnd_6723958 := by
    simpa [prefixWord, tailWord_6723958, baseEnd_6723958] using wordTrace_append hprefix tailTrace_6723958
  have hstable : (prefixWord ++ tailWord_6723958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723958).length < 2 ^ (prefixWord ++ tailWord_6723958).sum := by decide
  have hdescent : baseEnd_6723958 < baseStart_6723958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723993 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 2, 4, 2]
def baseStart_6723993 : Nat := 118140960795 + 6723993 * 2 ^ 59
def prefixEnd_6723993 : Nat := 4983230072969 + 3 ^ 40 * 6723993 * 2
def baseEnd_6723993 : Nat := 3452640326467216080164425

theorem tailTrace_6723993 : CollatzResearch.WordTrace tailWord_6723993 prefixEnd_6723993 3452640326467216080164425 := by
  unfold tailWord_6723993
  simp only [CollatzResearch.WordTrace]
  refine ⟨245244172329129202423376633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163496114886086134948917755 245244172329129202423376633)
  ·
    refine ⟨183933129246846901817532475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245244172329129202423376633 183933129246846901817532475)
    ·
      refine ⟨275899693870270352726298713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183933129246846901817532475 275899693870270352726298713)
      ·
        refine ⟨206924770402702764544724035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275899693870270352726298713 206924770402702764544724035)
        ·
          refine ⟨310387155604054146817086053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206924770402702764544724035 310387155604054146817086053)
          ·
            refine ⟨58197591675760152528203635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 310387155604054146817086053 58197591675760152528203635)
            ·
              refine ⟨87296387513640228792305453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58197591675760152528203635 87296387513640228792305453)
              ·
                refine ⟨32736145317615085797114545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87296387513640228792305453 32736145317615085797114545)
                ·
                  refine ⟨24552108988211314347835909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32736145317615085797114545 24552108988211314347835909)
                  ·
                    refine ⟨4603520435289621440219233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24552108988211314347835909 4603520435289621440219233)
                    ·
                      refine ⟨3452640326467216080164425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4603520435289621440219233 3452640326467216080164425)
                      ·
                        rfl

theorem cell23_6723993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 4, 2].length) (baseStart_6723993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723993 prefixEnd_6723993 := by exact prefixLift 6723993
  have htrace : WordTrace (prefixWord ++ tailWord_6723993) baseStart_6723993 baseEnd_6723993 := by
    simpa [prefixWord, tailWord_6723993, baseEnd_6723993] using wordTrace_append hprefix tailTrace_6723993
  have hstable : (prefixWord ++ tailWord_6723993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723993).length < 2 ^ (prefixWord ++ tailWord_6723993).sum := by decide
  have hdescent : baseEnd_6723993 < baseStart_6723993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724003 : List Nat := [1, 1, 1, 4, 1, 4, 2, 2, 3, 4]
def baseStart_6724003 : Nat := 118140960795 + 6724003 * 2 ^ 59
def prefixEnd_6724003 : Nat := 4983230072969 + 3 ^ 40 * 6724003 * 2
def baseEnd_6724003 : Nat := 1150881820424587013679793

theorem tailTrace_6724003 : CollatzResearch.WordTrace tailWord_6724003 prefixEnd_6724003 1150881820424587013679793 := by
  unfold tailWord_6724003
  simp only [CollatzResearch.WordTrace]
  refine ⟨245244537059092974131240663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163496358039395316087493775 245244537059092974131240663)
  ·
    refine ⟨367866805588639461196860995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245244537059092974131240663 367866805588639461196860995)
    ·
      refine ⟨551800208382959191795291493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367866805588639461196860995 551800208382959191795291493)
      ·
        refine ⟨103462539071804848461617155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 551800208382959191795291493 103462539071804848461617155)
        ·
          refine ⟨155193808607707272692425733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103462539071804848461617155 155193808607707272692425733)
          ·
            refine ⟨29098839113945113629829825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155193808607707272692425733 29098839113945113629829825)
            ·
              refine ⟨21824129335458835222372369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29098839113945113629829825 21824129335458835222372369)
              ·
                refine ⟨16368097001594126416779277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21824129335458835222372369 16368097001594126416779277)
                ·
                  refine ⟨6138036375597797406292229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16368097001594126416779277 6138036375597797406292229)
                  ·
                    refine ⟨1150881820424587013679793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6138036375597797406292229 1150881820424587013679793)
                    ·
                      rfl

theorem cell23_6724003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 4].length) (baseStart_6724003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724003 prefixEnd_6724003 := by exact prefixLift 6724003
  have htrace : WordTrace (prefixWord ++ tailWord_6724003) baseStart_6724003 baseEnd_6724003 := by
    simpa [prefixWord, tailWord_6724003, baseEnd_6724003] using wordTrace_append hprefix tailTrace_6724003
  have hstable : (prefixWord ++ tailWord_6724003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724003).length < 2 ^ (prefixWord ++ tailWord_6724003).sum := by decide
  have hdescent : baseEnd_6724003 < baseStart_6724003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724046 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 2, 9]
def baseStart_6724046 : Nat := 118140960795 + 6724046 * 2 ^ 59
def prefixEnd_6724046 : Nat := 4983230072969 + 3 ^ 40 * 6724046 * 2
def baseEnd_6724046 : Nat := 1150889180313968124267227

theorem tailTrace_6724046 : CollatzResearch.WordTrace tailWord_6724046 prefixEnd_6724046 1150889180313968124267227 := by
  unfold tailWord_6724046
  simp only [CollatzResearch.WordTrace]
  refine ⟨30655763174742149059381999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163497403598624794983370661 30655763174742149059381999)
  ·
    refine ⟨45983644762113223589072999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30655763174742149059381999 45983644762113223589072999)
    ·
      refine ⟨68975467143169835383609499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45983644762113223589072999 68975467143169835383609499)
      ·
        refine ⟨103463200714754753075414249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68975467143169835383609499 103463200714754753075414249)
        ·
          refine ⟨77597400536066064806560687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103463200714754753075414249 77597400536066064806560687)
          ·
            refine ⟨116396100804099097209841031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77597400536066064806560687 116396100804099097209841031)
            ·
              refine ⟨174594151206148645814761547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116396100804099097209841031 174594151206148645814761547)
              ·
                refine ⟨261891226809222968722142321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174594151206148645814761547 261891226809222968722142321)
                ·
                  refine ⟨196418420106917226541606741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261891226809222968722142321 196418420106917226541606741)
                  ·
                    refine ⟨1150889180313968124267227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 196418420106917226541606741 1150889180313968124267227)
                    ·
                      rfl

theorem cell23_6724046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_6724046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724046 prefixEnd_6724046 := by exact prefixLift 6724046
  have htrace : WordTrace (prefixWord ++ tailWord_6724046) baseStart_6724046 baseEnd_6724046 := by
    simpa [prefixWord, tailWord_6724046, baseEnd_6724046] using wordTrace_append hprefix tailTrace_6724046
  have hstable : (prefixWord ++ tailWord_6724046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724046).length < 2 ^ (prefixWord ++ tailWord_6724046).sum := by decide
  have hdescent : baseEnd_6724046 < baseStart_6724046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724063 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 3, 5]
def baseStart_6724063 : Nat := 118140960795 + 6724063 * 2 ^ 59
def prefixEnd_6724063 : Nat := 4983230072969 + 3 ^ 40 * 6724063 * 2
def baseEnd_6724063 : Nat := 1150892090037676935429701

theorem tailTrace_6724063 : CollatzResearch.WordTrace tailWord_6724063 prefixEnd_6724063 1150892090037676935429701 := by
  unfold tailWord_6724063
  simp only [CollatzResearch.WordTrace]
  refine ⟨245246725438875604378424843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163497816959250402918949895 245246725438875604378424843)
  ·
    refine ⟨367870088158313406567637265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245246725438875604378424843 367870088158313406567637265)
    ·
      refine ⟨275902566118735054925727949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367870088158313406567637265 275902566118735054925727949)
      ·
        refine ⟨103463462294525645597147981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275902566118735054925727949 103463462294525645597147981)
        ·
          refine ⟨38798798360447117098930493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103463462294525645597147981 38798798360447117098930493)
          ·
            refine ⟨14549549385167668912098935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38798798360447117098930493 14549549385167668912098935)
            ·
              refine ⟨21824324077751503368148403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14549549385167668912098935 21824324077751503368148403)
              ·
                refine ⟨32736486116627255052222605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21824324077751503368148403 32736486116627255052222605)
                ·
                  refine ⟨12276182293735220644583477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32736486116627255052222605 12276182293735220644583477)
                  ·
                    refine ⟨1150892090037676935429701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12276182293735220644583477 1150892090037676935429701)
                    ·
                      rfl

theorem cell23_6724063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 5].length) (baseStart_6724063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724063 prefixEnd_6724063 := by exact prefixLift 6724063
  have htrace : WordTrace (prefixWord ++ tailWord_6724063) baseStart_6724063 baseEnd_6724063 := by
    simpa [prefixWord, tailWord_6724063, baseEnd_6724063] using wordTrace_append hprefix tailTrace_6724063
  have hstable : (prefixWord ++ tailWord_6724063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724063).length < 2 ^ (prefixWord ++ tailWord_6724063).sum := by decide
  have hdescent : baseEnd_6724063 < baseStart_6724063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724080 : List Nat := [2, 1, 1, 1, 3, 3, 5, 1, 1, 5]
def baseStart_6724080 : Nat := 118140960795 + 6724080 * 2 ^ 59
def prefixEnd_6724080 : Nat := 4983230072969 + 3 ^ 40 * 6724080 * 2
def baseEnd_6724080 : Nat := 1150894999761385746592175

theorem tailTrace_6724080 : CollatzResearch.WordTrace tailWord_6724080 prefixEnd_6724080 1150894999761385746592175 := by
  unfold tailWord_6724080
  simp only [CollatzResearch.WordTrace]
  refine ⟨122623672739907008140896847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163498230319876010854529129 122623672739907008140896847)
  ·
    refine ⟨183935509109860512211345271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122623672739907008140896847 183935509109860512211345271)
    ·
      refine ⟨275903263664790768317017907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183935509109860512211345271 275903263664790768317017907)
      ·
        refine ⟨413854895497186152475526861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275903263664790768317017907 413854895497186152475526861)
        ·
          refine ⟨155195585811444807178322573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 413854895497186152475526861 155195585811444807178322573)
          ·
            refine ⟨58198344679291802691870965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155195585811444807178322573 58198344679291802691870965)
            ·
              refine ⟨5456094813683606502362903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58198344679291802691870965 5456094813683606502362903)
              ·
                refine ⟨8184142220525409753544355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5456094813683606502362903 8184142220525409753544355)
                ·
                  refine ⟨12276213330788114630316533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8184142220525409753544355 12276213330788114630316533)
                  ·
                    refine ⟨1150894999761385746592175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12276213330788114630316533 1150894999761385746592175)
                    ·
                      rfl

theorem cell23_6724080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 1, 5].length) (baseStart_6724080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724080 prefixEnd_6724080 := by exact prefixLift 6724080
  have htrace : WordTrace (prefixWord ++ tailWord_6724080) baseStart_6724080 baseEnd_6724080 := by
    simpa [prefixWord, tailWord_6724080, baseEnd_6724080] using wordTrace_append hprefix tailTrace_6724080
  have hstable : (prefixWord ++ tailWord_6724080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724080).length < 2 ^ (prefixWord ++ tailWord_6724080).sum := by decide
  have hdescent : baseEnd_6724080 < baseStart_6724080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724100 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_6724100 : Nat := 118140960795 + 6724100 * 2 ^ 59
def prefixEnd_6724100 : Nat := 4983230072969 + 3 ^ 40 * 6724100 * 2
def baseEnd_6724100 : Nat := 3452695268897247161526433

theorem tailTrace_6724100 : CollatzResearch.WordTrace tailWord_6724100 prefixEnd_6724100 3452695268897247161526433 := by
  unfold tailWord_6724100
  simp only [CollatzResearch.WordTrace]
  refine ⟨122624037469870779848760877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163498716626494373131681169 122624037469870779848760877)
  ·
    refine ⟨45984014051201542443285329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122624037469870779848760877 45984014051201542443285329)
    ·
      refine ⟨34488010538401156832463997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45984014051201542443285329 34488010538401156832463997)
      ·
        refine ⟨12933003951900433812173999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34488010538401156832463997 12933003951900433812173999)
        ·
          refine ⟨19399505927850650718260999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12933003951900433812173999 19399505927850650718260999)
          ·
            refine ⟨29099258891775976077391499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19399505927850650718260999 29099258891775976077391499)
            ·
              refine ⟨43648888337663964116087249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29099258891775976077391499 43648888337663964116087249)
              ·
                refine ⟨32736666253247973087065437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43648888337663964116087249 32736666253247973087065437)
                ·
                  refine ⟨12276249844967989907649539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32736666253247973087065437 12276249844967989907649539)
                  ·
                    refine ⟨18414374767451984861474309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12276249844967989907649539 18414374767451984861474309)
                    ·
                      refine ⟨3452695268897247161526433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18414374767451984861474309 3452695268897247161526433)
                      ·
                        rfl

theorem cell23_6724100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_6724100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724100 prefixEnd_6724100 := by exact prefixLift 6724100
  have htrace : WordTrace (prefixWord ++ tailWord_6724100) baseStart_6724100 baseEnd_6724100 := by
    simpa [prefixWord, tailWord_6724100, baseEnd_6724100] using wordTrace_append hprefix tailTrace_6724100
  have hstable : (prefixWord ++ tailWord_6724100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724100).length < 2 ^ (prefixWord ++ tailWord_6724100).sum := by decide
  have hdescent : baseEnd_6724100 < baseStart_6724100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724110 : List Nat := [4, 1, 1, 2, 3, 2, 2, 1, 1, 6]
def baseStart_6724110 : Nat := 118140960795 + 6724110 * 2 ^ 59
def prefixEnd_6724110 : Nat := 4983230072969 + 3 ^ 40 * 6724110 * 2
def baseEnd_6724110 : Nat := 1150900134567930707467129

theorem tailTrace_6724110 : CollatzResearch.WordTrace tailWord_6724110 prefixEnd_6724110 1150900134567930707467129 := by
  unfold tailWord_6724110
  simp only [CollatzResearch.WordTrace]
  refine ⟨30656054958713166425673223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163498959779803554270257189 30656054958713166425673223)
  ·
    refine ⟨45984082438069749638509835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30656054958713166425673223 45984082438069749638509835)
    ·
      refine ⟨68976123657104624457764753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45984082438069749638509835 68976123657104624457764753)
      ·
        refine ⟨51732092742828468343323565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68976123657104624457764753 51732092742828468343323565)
        ·
          refine ⟨19399534778560675628746337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51732092742828468343323565 19399534778560675628746337)
          ·
            refine ⟨14549651083920506721559753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19399534778560675628746337 14549651083920506721559753)
            ·
              refine ⟨10912238312940380041169815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14549651083920506721559753 10912238312940380041169815)
              ·
                refine ⟨16368357469410570061754723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10912238312940380041169815 16368357469410570061754723)
                ·
                  refine ⟨24552536204115855092632085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16368357469410570061754723 24552536204115855092632085)
                  ·
                    refine ⟨1150900134567930707467129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24552536204115855092632085 1150900134567930707467129)
                    ·
                      rfl

theorem cell23_6724110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_6724110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724110 prefixEnd_6724110 := by exact prefixLift 6724110
  have htrace : WordTrace (prefixWord ++ tailWord_6724110) baseStart_6724110 baseEnd_6724110 := by
    simpa [prefixWord, tailWord_6724110, baseEnd_6724110] using wordTrace_append hprefix tailTrace_6724110
  have hstable : (prefixWord ++ tailWord_6724110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724110).length < 2 ^ (prefixWord ++ tailWord_6724110).sum := by decide
  have hdescent : baseEnd_6724110 < baseStart_6724110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724117 : List Nat := [1, 3, 2, 1, 3, 1, 3, 2, 3, 2, 2]
def baseStart_6724117 : Nat := 118140960795 + 6724117 * 2 ^ 59
def prefixEnd_6724117 : Nat := 4983230072969 + 3 ^ 40 * 6724117 * 2
def baseEnd_6724117 : Nat := 3452703998068373595013855

theorem tailTrace_6724117 : CollatzResearch.WordTrace tailWord_6724117 prefixEnd_6724117 3452703998068373595013855 := by
  unfold tailWord_6724117
  simp only [CollatzResearch.WordTrace]
  refine ⟨245248694980679971600890605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163499129987119981067260403 245248694980679971600890605)
  ·
    refine ⟨91968260617754989350333977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245248694980679971600890605 91968260617754989350333977)
    ·
      refine ⟨68976195463316242012750483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91968260617754989350333977 68976195463316242012750483)
      ·
        refine ⟨103464293194974363019125725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68976195463316242012750483 103464293194974363019125725)
        ·
          refine ⟨38799109948115386132172147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103464293194974363019125725 38799109948115386132172147)
          ·
            refine ⟨58198664922173079198258221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38799109948115386132172147 58198664922173079198258221)
            ·
              refine ⟨21824499345814904699346833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58198664922173079198258221 21824499345814904699346833)
              ·
                refine ⟨16368374509361178524510125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21824499345814904699346833 16368374509361178524510125)
                ·
                  refine ⟨6138140441010441946691297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16368374509361178524510125 6138140441010441946691297)
                  ·
                    refine ⟨4603605330757831460018473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6138140441010441946691297 4603605330757831460018473)
                    ·
                      refine ⟨3452703998068373595013855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4603605330757831460018473 3452703998068373595013855)
                      ·
                        rfl

theorem cell23_6724117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 2, 2].length) (baseStart_6724117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724117 prefixEnd_6724117 := by exact prefixLift 6724117
  have htrace : WordTrace (prefixWord ++ tailWord_6724117) baseStart_6724117 baseEnd_6724117 := by
    simpa [prefixWord, tailWord_6724117, baseEnd_6724117] using wordTrace_append hprefix tailTrace_6724117
  have hstable : (prefixWord ++ tailWord_6724117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724117).length < 2 ^ (prefixWord ++ tailWord_6724117).sum := by decide
  have hdescent : baseEnd_6724117 < baseStart_6724117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724120 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 3, 2, 3]
def baseStart_6724120 : Nat := 118140960795 + 6724120 * 2 ^ 59
def prefixEnd_6724120 : Nat := 4983230072969 + 3 ^ 40 * 6724120 * 2
def baseEnd_6724120 : Nat := 3452705538510337083276341

theorem tailTrace_6724120 : CollatzResearch.WordTrace tailWord_6724120 prefixEnd_6724120 3452705538510337083276341 := by
  unfold tailWord_6724120
  simp only [CollatzResearch.WordTrace]
  refine ⟨122624402199834551556624907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163499202933112735408833209 122624402199834551556624907)
  ·
    refine ⟨183936603299751827334937361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122624402199834551556624907 183936603299751827334937361)
    ·
      refine ⟨137952452474813870501203021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183936603299751827334937361 137952452474813870501203021)
      ·
        refine ⟨51732169678055201437951133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137952452474813870501203021 51732169678055201437951133)
        ·
          refine ⟨19399563629270700539231675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51732169678055201437951133 19399563629270700539231675)
          ·
            refine ⟨29099345443906050808847513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19399563629270700539231675 29099345443906050808847513)
            ·
              refine ⟨21824509082929538106635635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29099345443906050808847513 21824509082929538106635635)
              ·
                refine ⟨32736763624394307159953453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21824509082929538106635635 32736763624394307159953453)
                ·
                  refine ⟨12276286359147865184982545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32736763624394307159953453 12276286359147865184982545)
                  ·
                    refine ⟨9207214769360898888736909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12276286359147865184982545 9207214769360898888736909)
                    ·
                      refine ⟨3452705538510337083276341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9207214769360898888736909 3452705538510337083276341)
                      ·
                        rfl

theorem cell23_6724120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_6724120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724120 prefixEnd_6724120 := by exact prefixLift 6724120
  have htrace : WordTrace (prefixWord ++ tailWord_6724120) baseStart_6724120 baseEnd_6724120 := by
    simpa [prefixWord, tailWord_6724120, baseEnd_6724120] using wordTrace_append hprefix tailTrace_6724120
  have hstable : (prefixWord ++ tailWord_6724120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724120).length < 2 ^ (prefixWord ++ tailWord_6724120).sum := by decide
  have hdescent : baseEnd_6724120 < baseStart_6724120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724160 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 5, 3, 2]
def baseStart_6724160 : Nat := 118140960795 + 6724160 * 2 ^ 59
def prefixEnd_6724160 : Nat := 4983230072969 + 3 ^ 40 * 6724160 * 2
def baseEnd_6724160 : Nat := 3452726077736516926776157

theorem tailTrace_6724160 : CollatzResearch.WordTrace tailWord_6724160 prefixEnd_6724160 3452726077736516926776157 := by
  unfold tailWord_6724160
  simp only [CollatzResearch.WordTrace]
  refine ⟨122625131659762094972352967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163500175546349459963137289 122625131659762094972352967)
  ·
    refine ⟨183937697489643142458529451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122625131659762094972352967 183937697489643142458529451)
    ·
      refine ⟨275906546234464713687794177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183937697489643142458529451 275906546234464713687794177)
      ·
        refine ⟨206929909675848535265845633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275906546234464713687794177 206929909675848535265845633)
        ·
          refine ⟨155197432256886401449384225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206929909675848535265845633 155197432256886401449384225)
          ·
            refine ⟨116398074192664801087038169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155197432256886401449384225 116398074192664801087038169)
            ·
              refine ⟨87298555644498600815278627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116398074192664801087038169 87298555644498600815278627)
              ·
                refine ⟨130947833466747901222917941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87298555644498600815278627 130947833466747901222917941)
                ·
                  refine ⟨12276359387507615739648557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130947833466747901222917941 12276359387507615739648557)
                  ·
                    refine ⟨4603634770315355902368209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12276359387507615739648557 4603634770315355902368209)
                    ·
                      refine ⟨3452726077736516926776157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4603634770315355902368209 3452726077736516926776157)
                      ·
                        rfl

theorem cell23_6724160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 5, 3, 2].length) (baseStart_6724160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724160 prefixEnd_6724160 := by exact prefixLift 6724160
  have htrace : WordTrace (prefixWord ++ tailWord_6724160) baseStart_6724160 baseEnd_6724160 := by
    simpa [prefixWord, tailWord_6724160, baseEnd_6724160] using wordTrace_append hprefix tailTrace_6724160
  have hstable : (prefixWord ++ tailWord_6724160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724160).length < 2 ^ (prefixWord ++ tailWord_6724160).sum := by decide
  have hdescent : baseEnd_6724160 < baseStart_6724160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724164 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_6724164 : Nat := 118140960795 + 6724164 * 2 ^ 59
def prefixEnd_6724164 : Nat := 4983230072969 + 3 ^ 40 * 6724164 * 2
def baseEnd_6724164 : Nat := 3452728131659134911126139

theorem tailTrace_6724164 : CollatzResearch.WordTrace tailWord_6724164 prefixEnd_6724164 3452728131659134911126139 := by
  unfold tailWord_6724164
  simp only [CollatzResearch.WordTrace]
  refine ⟨122625204605754849313925773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163500272807673132418567697 122625204605754849313925773)
  ·
    refine ⟨45984451727158068492722165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122625204605754849313925773 45984451727158068492722165)
    ·
      refine ⟨4311042349421068921192703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45984451727158068492722165 4311042349421068921192703)
      ·
        refine ⟨6466563524131603381789055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4311042349421068921192703 6466563524131603381789055)
        ·
          refine ⟨9699845286197405072683583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6466563524131603381789055 9699845286197405072683583)
          ·
            refine ⟨14549767929296107609025375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9699845286197405072683583 14549767929296107609025375)
            ·
              refine ⟨21824651893944161413538063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14549767929296107609025375 21824651893944161413538063)
              ·
                refine ⟨32736977840916242120307095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21824651893944161413538063 32736977840916242120307095)
                ·
                  refine ⟨49105466761374363180460643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32736977840916242120307095 49105466761374363180460643)
                  ·
                    refine ⟨73658200142061544770690965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49105466761374363180460643 73658200142061544770690965)
                    ·
                      refine ⟨3452728131659134911126139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73658200142061544770690965 3452728131659134911126139)
                      ·
                        rfl

theorem cell23_6724164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_6724164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724164 prefixEnd_6724164 := by exact prefixLift 6724164
  have htrace : WordTrace (prefixWord ++ tailWord_6724164) baseStart_6724164 baseEnd_6724164 := by
    simpa [prefixWord, tailWord_6724164, baseEnd_6724164] using wordTrace_append hprefix tailTrace_6724164
  have hstable : (prefixWord ++ tailWord_6724164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724164).length < 2 ^ (prefixWord ++ tailWord_6724164).sum := by decide
  have hdescent : baseEnd_6724164 < baseStart_6724164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724167 : List Nat := [1, 1, 4, 1, 4, 3, 1, 1, 1, 3, 3]
def baseStart_6724167 : Nat := 118140960795 + 6724167 * 2 ^ 59
def prefixEnd_6724167 : Nat := 4983230072969 + 3 ^ 40 * 6724167 * 2
def baseEnd_6724167 : Nat := 3452729672101098399388625

theorem tailTrace_6724167 : CollatzResearch.WordTrace tailWord_6724167 prefixEnd_6724167 3452729672101098399388625 := by
  unfold tailWord_6724167
  simp only [CollatzResearch.WordTrace]
  refine ⟨245250518630498830140210755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163500345753665886760140503 245250518630498830140210755)
  ·
    refine ⟨367875777945748245210316133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245250518630498830140210755 367875777945748245210316133)
    ·
      refine ⟨68976708364827795976934275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 367875777945748245210316133 68976708364827795976934275)
      ·
        refine ⟨103465062547241693965401413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68976708364827795976934275 103465062547241693965401413)
        ·
          refine ⟨19399699227607817618512765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103465062547241693965401413 19399699227607817618512765)
          ·
            refine ⟨7274887210352931606942287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19399699227607817618512765 7274887210352931606942287)
            ·
              refine ⟨10912330815529397410413431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7274887210352931606942287 10912330815529397410413431)
              ·
                refine ⟨16368496223294096115620147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10912330815529397410413431 16368496223294096115620147)
                ·
                  refine ⟨24552744334941144173430221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16368496223294096115620147 24552744334941144173430221)
                  ·
                    refine ⟨9207279125602929065036333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24552744334941144173430221 9207279125602929065036333)
                    ·
                      refine ⟨3452729672101098399388625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9207279125602929065036333 3452729672101098399388625)
                      ·
                        rfl

theorem cell23_6724167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_6724167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724167 prefixEnd_6724167 := by exact prefixLift 6724167
  have htrace : WordTrace (prefixWord ++ tailWord_6724167) baseStart_6724167 baseEnd_6724167 := by
    simpa [prefixWord, tailWord_6724167, baseEnd_6724167] using wordTrace_append hprefix tailTrace_6724167
  have hstable : (prefixWord ++ tailWord_6724167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724167).length < 2 ^ (prefixWord ++ tailWord_6724167).sum := by decide
  have hdescent : baseEnd_6724167 < baseStart_6724167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724177 : List Nat := [1, 2, 2, 1, 3, 3, 1, 4, 1, 3, 2]
def baseStart_6724177 : Nat := 118140960795 + 6724177 * 2 ^ 59
def prefixEnd_6724177 : Nat := 4983230072969 + 3 ^ 40 * 6724177 * 2
def baseEnd_6724177 : Nat := 3452734806907643360263579

theorem tailTrace_6724177 : CollatzResearch.WordTrace tailWord_6724177 prefixEnd_6724177 3452734806907643360263579 := by
  unfold tailWord_6724177
  simp only [CollatzResearch.WordTrace]
  refine ⟨245250883360462601848074785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163500588906975067898716523 245250883360462601848074785)
  ·
    refine ⟨183938162520346951386056089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245250883360462601848074785 183938162520346951386056089)
    ·
      refine ⟨137953621890260213539542067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183938162520346951386056089 137953621890260213539542067)
      ·
        refine ⟨206930432835390320309313101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137953621890260213539542067 206930432835390320309313101)
        ·
          refine ⟨77598912313271370115992413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206930432835390320309313101 77598912313271370115992413)
          ·
            refine ⟨29099592117476763793497155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77598912313271370115992413 29099592117476763793497155)
            ·
              refine ⟨43649388176215145690245733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29099592117476763793497155 43649388176215145690245733)
              ·
                refine ⟨8184260283040339816921075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43649388176215145690245733 8184260283040339816921075)
                ·
                  refine ⟨12276390424560509725381613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8184260283040339816921075 12276390424560509725381613)
                  ·
                    refine ⟨4603646409210191147018105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12276390424560509725381613 4603646409210191147018105)
                    ·
                      refine ⟨3452734806907643360263579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4603646409210191147018105 3452734806907643360263579)
                      ·
                        rfl

theorem cell23_6724177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 3, 2].length) (baseStart_6724177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724177 prefixEnd_6724177 := by exact prefixLift 6724177
  have htrace : WordTrace (prefixWord ++ tailWord_6724177) baseStart_6724177 baseEnd_6724177 := by
    simpa [prefixWord, tailWord_6724177, baseEnd_6724177] using wordTrace_append hprefix tailTrace_6724177
  have hstable : (prefixWord ++ tailWord_6724177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724177).length < 2 ^ (prefixWord ++ tailWord_6724177).sum := by decide
  have hdescent : baseEnd_6724177 < baseStart_6724177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724193 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 1, 3, 5]
def baseStart_6724193 : Nat := 118140960795 + 6724193 * 2 ^ 59
def prefixEnd_6724193 : Nat := 4983230072969 + 3 ^ 40 * 6724193 * 2
def baseEnd_6724193 : Nat := 3452743022598115297663505

theorem tailTrace_6724193 : CollatzResearch.WordTrace tailWord_6724193 prefixEnd_6724193 3452743022598115297663505 := by
  unfold tailWord_6724193
  simp only [CollatzResearch.WordTrace]
  refine ⟨245251466928404636580657233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163500977952269757720438155 245251466928404636580657233)
  ·
    refine ⟨183938600196303477435492925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245251466928404636580657233 183938600196303477435492925)
    ·
      refine ⟨68976975073613804038309847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183938600196303477435492925 68976975073613804038309847)
      ·
        refine ⟨103465462610420706057464771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68976975073613804038309847 103465462610420706057464771)
        ·
          refine ⟨155198193915631059086197157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103465462610420706057464771 155198193915631059086197157)
          ·
            refine ⟨29099661359180823578661967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155198193915631059086197157 29099661359180823578661967)
            ·
              refine ⟨43649492038771235367992951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29099661359180823578661967 43649492038771235367992951)
              ·
                refine ⟨65474238058156853051989427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43649492038771235367992951 65474238058156853051989427)
                ·
                  refine ⟨98211357087235279577984141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65474238058156853051989427 98211357087235279577984141)
                  ·
                    refine ⟨36829258907713229841744053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98211357087235279577984141 36829258907713229841744053)
                    ·
                      refine ⟨3452743022598115297663505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36829258907713229841744053 3452743022598115297663505)
                      ·
                        rfl

theorem cell23_6724193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_6724193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724193 prefixEnd_6724193 := by exact prefixLift 6724193
  have htrace : WordTrace (prefixWord ++ tailWord_6724193) baseStart_6724193 baseEnd_6724193 := by
    simpa [prefixWord, tailWord_6724193, baseEnd_6724193] using wordTrace_append hprefix tailTrace_6724193
  have hstable : (prefixWord ++ tailWord_6724193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724193).length < 2 ^ (prefixWord ++ tailWord_6724193).sum := by decide
  have hdescent : baseEnd_6724193 < baseStart_6724193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724203 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 4]
def baseStart_6724203 : Nat := 118140960795 + 6724203 * 2 ^ 59
def prefixEnd_6724203 : Nat := 4983230072969 + 3 ^ 40 * 6724203 * 2
def baseEnd_6724203 : Nat := 3452748157404660258538459

theorem tailTrace_6724203 : CollatzResearch.WordTrace tailWord_6724203 prefixEnd_6724203 3452748157404660258538459 := by
  unfold tailWord_6724203
  simp only [CollatzResearch.WordTrace]
  refine ⟨245251831658368408288521263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163501221105578938859014175 245251831658368408288521263)
  ·
    refine ⟨367877747487552612432781895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245251831658368408288521263 367877747487552612432781895)
    ·
      refine ⟨551816621231328918649172843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367877747487552612432781895 551816621231328918649172843)
      ·
        refine ⟨827724931846993377973759265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551816621231328918649172843 827724931846993377973759265)
        ·
          refine ⟨620793698885245033480319449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 827724931846993377973759265 620793698885245033480319449)
          ·
            refine ⟨465595274163933775110239587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 620793698885245033480319449 465595274163933775110239587)
            ·
              refine ⟨698392911245900662665359381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465595274163933775110239587 698392911245900662665359381)
              ·
                refine ⟨32737167714651593562438721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 698392911245900662665359381 32737167714651593562438721)
                ·
                  refine ⟨24552875785988695171829041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32737167714651593562438721 24552875785988695171829041)
                  ·
                    refine ⟨18414656839491521378871781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24552875785988695171829041 18414656839491521378871781)
                    ·
                      refine ⟨3452748157404660258538459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18414656839491521378871781 3452748157404660258538459)
                      ·
                        rfl

theorem cell23_6724203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 4].length) (baseStart_6724203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724203 prefixEnd_6724203 := by exact prefixLift 6724203
  have htrace : WordTrace (prefixWord ++ tailWord_6724203) baseStart_6724203 baseEnd_6724203 := by
    simpa [prefixWord, tailWord_6724203, baseEnd_6724203] using wordTrace_append hprefix tailTrace_6724203
  have hstable : (prefixWord ++ tailWord_6724203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724203).length < 2 ^ (prefixWord ++ tailWord_6724203).sum := by decide
  have hdescent : baseEnd_6724203 < baseStart_6724203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724207 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 4, 2, 2]
def baseStart_6724207 : Nat := 118140960795 + 6724207 * 2 ^ 59
def prefixEnd_6724207 : Nat := 4983230072969 + 3 ^ 40 * 6724207 * 2
def baseEnd_6724207 : Nat := 3452750211327278242888441

theorem tailTrace_6724207 : CollatzResearch.WordTrace tailWord_6724207 prefixEnd_6724207 3452750211327278242888441 := by
  unfold tailWord_6724207
  simp only [CollatzResearch.WordTrace]
  refine ⟨245251977550353916971666875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163501318366902611314444583 245251977550353916971666875)
  ·
    refine ⟨367877966325530875457500313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245251977550353916971666875 367877966325530875457500313)
    ·
      refine ⟨275908474744148156593125235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367877966325530875457500313 275908474744148156593125235)
      ·
        refine ⟨413862712116222234889687853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275908474744148156593125235 413862712116222234889687853)
        ·
          refine ⟨155198517043583338083632945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 413862712116222234889687853 155198517043583338083632945)
          ·
            refine ⟨116398887782687503562724709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155198517043583338083632945 116398887782687503562724709)
            ·
              refine ⟨21824791459253906918010883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116398887782687503562724709 21824791459253906918010883)
              ·
                refine ⟨32737187188880860377016325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21824791459253906918010883 32737187188880860377016325)
                ·
                  refine ⟨6138222597915161320690561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32737187188880860377016325 6138222597915161320690561)
                  ·
                    refine ⟨4603666948436370990517921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6138222597915161320690561 4603666948436370990517921)
                    ·
                      refine ⟨3452750211327278242888441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4603666948436370990517921 3452750211327278242888441)
                      ·
                        rfl

theorem cell23_6724207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 2, 2].length) (baseStart_6724207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724207 prefixEnd_6724207 := by exact prefixLift 6724207
  have htrace : WordTrace (prefixWord ++ tailWord_6724207) baseStart_6724207 baseEnd_6724207 := by
    simpa [prefixWord, tailWord_6724207, baseEnd_6724207] using wordTrace_append hprefix tailTrace_6724207
  have hstable : (prefixWord ++ tailWord_6724207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724207).length < 2 ^ (prefixWord ++ tailWord_6724207).sum := by decide
  have hdescent : baseEnd_6724207 < baseStart_6724207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724224 : List Nat := [2, 1, 1, 2, 1, 6, 1, 3, 2, 2, 2]
def baseStart_6724224 : Nat := 118140960795 + 6724224 * 2 ^ 59
def prefixEnd_6724224 : Nat := 4983230072969 + 3 ^ 40 * 6724224 * 2
def baseEnd_6724224 : Nat := 3452758940498404676375863

theorem tailTrace_6724224 : CollatzResearch.WordTrace tailWord_6724224 prefixEnd_6724224 3452758940498404676375863 := by
  unfold tailWord_6724224
  simp only [CollatzResearch.WordTrace]
  refine ⟨122626298795646164437517863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163501731727528219250023817 122626298795646164437517863)
  ·
    refine ⟨183939448193469246656276795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122626298795646164437517863 183939448193469246656276795)
    ·
      refine ⟨275909172290203869984415193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183939448193469246656276795 275909172290203869984415193)
      ·
        refine ⟨206931879217652902488311395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275909172290203869984415193 206931879217652902488311395)
        ·
          refine ⟨310397818826479353732467093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206931879217652902488311395 310397818826479353732467093)
          ·
            refine ⟨14549897757491219706209395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 310397818826479353732467093 14549897757491219706209395)
            ·
              refine ⟨21824846636236829559314093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14549897757491219706209395 21824846636236829559314093)
              ·
                refine ⟨8184317488588811084742785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21824846636236829559314093 8184317488588811084742785)
                ·
                  refine ⟨6138238116441608313557089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8184317488588811084742785 6138238116441608313557089)
                  ·
                    refine ⟨4603678587331206235167817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6138238116441608313557089 4603678587331206235167817)
                    ·
                      refine ⟨3452758940498404676375863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4603678587331206235167817 3452758940498404676375863)
                      ·
                        rfl

theorem cell23_6724224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 2, 2, 2].length) (baseStart_6724224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724224 prefixEnd_6724224 := by exact prefixLift 6724224
  have htrace : WordTrace (prefixWord ++ tailWord_6724224) baseStart_6724224 baseEnd_6724224 := by
    simpa [prefixWord, tailWord_6724224, baseEnd_6724224] using wordTrace_append hprefix tailTrace_6724224
  have hstable : (prefixWord ++ tailWord_6724224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724224).length < 2 ^ (prefixWord ++ tailWord_6724224).sum := by decide
  have hdescent : baseEnd_6724224 < baseStart_6724224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724243 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 6, 5]
def baseStart_6724243 : Nat := 118140960795 + 6724243 * 2 ^ 59
def prefixEnd_6724243 : Nat := 4983230072969 + 3 ^ 40 * 6724243 * 2
def baseEnd_6724243 : Nat := 1150922898876946700679425

theorem tailTrace_6724243 : CollatzResearch.WordTrace tailWord_6724243 prefixEnd_6724243 1150922898876946700679425 := by
  unfold tailWord_6724243
  simp only [CollatzResearch.WordTrace]
  refine ⟨245253290578223495119977383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163502193718815663413318255 245253290578223495119977383)
  ·
    refine ⟨367879935867335242679966075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245253290578223495119977383 367879935867335242679966075)
    ·
      refine ⟨551819903801002864019949113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367879935867335242679966075 551819903801002864019949113)
      ·
        refine ⟨413864927850752148014961835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 551819903801002864019949113 413864927850752148014961835)
        ·
          refine ⟨620797391776128222022442753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413864927850752148014961835 620797391776128222022442753)
          ·
            refine ⟨465598043832096166516832065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 620797391776128222022442753 465598043832096166516832065)
            ·
              refine ⟨349198532874072124887624049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465598043832096166516832065 349198532874072124887624049)
              ·
                refine ⟨261898899655554093665718037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349198532874072124887624049 261898899655554093665718037)
                ·
                  refine ⟨12276510921354098140580533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 261898899655554093665718037 12276510921354098140580533)
                  ·
                    refine ⟨1150922898876946700679425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12276510921354098140580533 1150922898876946700679425)
                    ·
                      rfl

theorem cell23_6724243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 5].length) (baseStart_6724243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724243 prefixEnd_6724243 := by exact prefixLift 6724243
  have htrace : WordTrace (prefixWord ++ tailWord_6724243) baseStart_6724243 baseEnd_6724243 := by
    simpa [prefixWord, tailWord_6724243, baseEnd_6724243] using wordTrace_append hprefix tailTrace_6724243
  have hstable : (prefixWord ++ tailWord_6724243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724243).length < 2 ^ (prefixWord ++ tailWord_6724243).sum := by decide
  have hdescent : baseEnd_6724243 < baseStart_6724243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724260 : List Nat := [2, 3, 1, 2, 2, 1, 1, 4, 2, 5]
def baseStart_6724260 : Nat := 118140960795 + 6724260 * 2 ^ 59
def prefixEnd_6724260 : Nat := 4983230072969 + 3 ^ 40 * 6724260 * 2
def baseEnd_6724260 : Nat := 1150925808600655511841899

theorem tailTrace_6724260 : CollatzResearch.WordTrace tailWord_6724260 prefixEnd_6724260 1150925808600655511841899 := by
  unfold tailWord_6724260
  simp only [CollatzResearch.WordTrace]
  refine ⟨122626955309580953511673117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163502607079441271348897489 122626955309580953511673117)
  ·
    refine ⟨45985108241092857566877419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122626955309580953511673117 45985108241092857566877419)
    ·
      refine ⟨68977662361639286350316129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45985108241092857566877419 68977662361639286350316129)
      ·
        refine ⟨51733246771229464762737097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68977662361639286350316129 51733246771229464762737097)
        ·
          refine ⟨38799935078422098572052823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51733246771229464762737097 38799935078422098572052823)
          ·
            refine ⟨58199902617633147858079235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38799935078422098572052823 58199902617633147858079235)
            ·
              refine ⟨87299853926449721787118853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58199902617633147858079235 87299853926449721787118853)
              ·
                refine ⟨16368722611209322835084785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87299853926449721787118853 16368722611209322835084785)
                ·
                  refine ⟨12276541958406992126313589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16368722611209322835084785 12276541958406992126313589)
                  ·
                    refine ⟨1150925808600655511841899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12276541958406992126313589 1150925808600655511841899)
                    ·
                      rfl

theorem cell23_6724260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_6724260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724260 prefixEnd_6724260 := by exact prefixLift 6724260
  have htrace : WordTrace (prefixWord ++ tailWord_6724260) baseStart_6724260 baseEnd_6724260 := by
    simpa [prefixWord, tailWord_6724260, baseEnd_6724260] using wordTrace_append hprefix tailTrace_6724260
  have hstable : (prefixWord ++ tailWord_6724260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724260).length < 2 ^ (prefixWord ++ tailWord_6724260).sum := by decide
  have hdescent : baseEnd_6724260 < baseStart_6724260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724293 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 3, 3, 6]
def baseStart_6724293 : Nat := 118140960795 + 6724293 * 2 ^ 59
def prefixEnd_6724293 : Nat := 4983230072969 + 3 ^ 40 * 6724293 * 2
def baseEnd_6724293 : Nat := 3452794370663564906413045

theorem tailTrace_6724293 : CollatzResearch.WordTrace tailWord_6724293 prefixEnd_6724293 3452794370663564906413045 := by
  unfold tailWord_6724293
  simp only [CollatzResearch.WordTrace]
  refine ⟨245255114228042353659297533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163503409485361569106198355 245255114228042353659297533)
  ·
    refine ⟨91970667835515882622236575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245255114228042353659297533 91970667835515882622236575)
    ·
      refine ⟨137956001753273823933354863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91970667835515882622236575 137956001753273823933354863)
      ·
        refine ⟨206934002629910735900032295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137956001753273823933354863 206934002629910735900032295)
        ·
          refine ⟨310401003944866103850048443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206934002629910735900032295 310401003944866103850048443)
          ·
            refine ⟨465601505917299155775072665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310401003944866103850048443 465601505917299155775072665)
            ·
              refine ⟨349201129437974366831304499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465601505917299155775072665 349201129437974366831304499)
              ·
                refine ⟨523801694156961550246956749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349201129437974366831304499 523801694156961550246956749)
                ·
                  refine ⟨196425635308860581342608781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 523801694156961550246956749 196425635308860581342608781)
                  ·
                    refine ⟨73659613240822718003478293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 196425635308860581342608781 73659613240822718003478293)
                    ·
                      refine ⟨3452794370663564906413045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73659613240822718003478293 3452794370663564906413045)
                      ·
                        rfl

theorem cell23_6724293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_6724293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724293 prefixEnd_6724293 := by exact prefixLift 6724293
  have htrace : WordTrace (prefixWord ++ tailWord_6724293) baseStart_6724293 baseEnd_6724293 := by
    simpa [prefixWord, tailWord_6724293, baseEnd_6724293] using wordTrace_append hprefix tailTrace_6724293
  have hstable : (prefixWord ++ tailWord_6724293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724293).length < 2 ^ (prefixWord ++ tailWord_6724293).sum := by decide
  have hdescent : baseEnd_6724293 < baseStart_6724293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724324 : List Nat := [2, 3, 1, 1, 1, 4, 2, 4, 1, 4]
def baseStart_6724324 : Nat := 118140960795 + 6724324 * 2 ^ 59
def prefixEnd_6724324 : Nat := 4983230072969 + 3 ^ 40 * 6724324 * 2
def baseEnd_6724324 : Nat := 1150936762854618095041801

theorem tailTrace_6724324 : CollatzResearch.WordTrace tailWord_6724324 prefixEnd_6724324 1150936762854618095041801 := by
  unfold tailWord_6724324
  simp only [CollatzResearch.WordTrace]
  refine ⟨122628122445465022976838013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163504163260620030635784017 122628122445465022976838013)
  ·
    refine ⟨45985545917049383616314255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122628122445465022976838013 45985545917049383616314255)
    ·
      refine ⟨68978318875574075424471383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45985545917049383616314255 68978318875574075424471383)
      ·
        refine ⟨103467478313361113136707075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68978318875574075424471383 103467478313361113136707075)
        ·
          refine ⟨155201217470041669705060613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103467478313361113136707075 155201217470041669705060613)
          ·
            refine ⟨29100228275632813069698865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155201217470041669705060613 29100228275632813069698865)
            ·
              refine ⟨21825171206724609802274149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29100228275632813069698865 21825171206724609802274149)
              ·
                refine ⟨4092219601260864337926403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21825171206724609802274149 4092219601260864337926403)
                ·
                  refine ⟨6138329401891296506889605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4092219601260864337926403 6138329401891296506889605)
                  ·
                    refine ⟨1150936762854618095041801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6138329401891296506889605 1150936762854618095041801)
                    ·
                      rfl

theorem cell23_6724324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_6724324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724324 prefixEnd_6724324 := by exact prefixLift 6724324
  have htrace : WordTrace (prefixWord ++ tailWord_6724324) baseStart_6724324 baseEnd_6724324 := by
    simpa [prefixWord, tailWord_6724324, baseEnd_6724324] using wordTrace_append hprefix tailTrace_6724324
  have hstable : (prefixWord ++ tailWord_6724324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724324).length < 2 ^ (prefixWord ++ tailWord_6724324).sum := by decide
  have hdescent : baseEnd_6724324 < baseStart_6724324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724337 : List Nat := [1, 2, 2, 2, 2, 2, 5, 1, 6]
def baseStart_6724337 : Nat := 118140960795 + 6724337 * 2 ^ 59
def prefixEnd_6724337 : Nat := 4983230072969 + 3 ^ 40 * 6724337 * 2
def baseEnd_6724337 : Nat := 383646329312484748251427

theorem tailTrace_6724337 : CollatzResearch.WordTrace tailWord_6724337 prefixEnd_6724337 383646329312484748251427 := by
  unfold tailWord_6724337
  simp only [CollatzResearch.WordTrace]
  refine ⟨245256719039882949173899265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163504479359921966115932843 245256719039882949173899265)
  ·
    refine ⟨183942539279912211880424449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245256719039882949173899265 183942539279912211880424449)
    ·
      refine ⟨137956904459934158910318337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183942539279912211880424449 137956904459934158910318337)
      ·
        refine ⟨103467678344950619182738753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137956904459934158910318337 103467678344950619182738753)
        ·
          refine ⟨77600758758712964387054065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103467678344950619182738753 77600758758712964387054065)
          ·
            refine ⟨58200569069034723290290549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77600758758712964387054065 58200569069034723290290549)
            ·
              refine ⟨5456303350222005308464739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58200569069034723290290549 5456303350222005308464739)
              ·
                refine ⟨8184455025333007962697109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5456303350222005308464739 8184455025333007962697109)
                ·
                  refine ⟨383646329312484748251427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8184455025333007962697109 383646329312484748251427)
                  ·
                    rfl

theorem cell23_6724337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 6].length) (baseStart_6724337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724337 prefixEnd_6724337 := by exact prefixLift 6724337
  have htrace : WordTrace (prefixWord ++ tailWord_6724337) baseStart_6724337 baseEnd_6724337 := by
    simpa [prefixWord, tailWord_6724337, baseEnd_6724337] using wordTrace_append hprefix tailTrace_6724337
  have hstable : (prefixWord ++ tailWord_6724337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724337).length < 2 ^ (prefixWord ++ tailWord_6724337).sum := by decide
  have hdescent : baseEnd_6724337 < baseStart_6724337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724357 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 6, 3, 2]
def baseStart_6724357 : Nat := 118140960795 + 6724357 * 2 ^ 59
def prefixEnd_6724357 : Nat := 4983230072969 + 3 ^ 40 * 6724357 * 2
def baseEnd_6724357 : Nat := 3452827233425452656012751

theorem tailTrace_6724357 : CollatzResearch.WordTrace tailWord_6724357 prefixEnd_6724357 3452827233425452656012751 := by
  unfold tailWord_6724357
  simp only [CollatzResearch.WordTrace]
  refine ⟨245257448499810492589627325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163504965666540328393084883 245257448499810492589627325)
  ·
    refine ⟨91971543187428934721110247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245257448499810492589627325 91971543187428934721110247)
    ·
      refine ⟨137957314781143402081665371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91971543187428934721110247 137957314781143402081665371)
      ·
        refine ⟨206935972171715103122498057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137957314781143402081665371 206935972171715103122498057)
        ·
          refine ⟨155201979128786327341873543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206935972171715103122498057 155201979128786327341873543)
          ·
            refine ⟨232802968693179491012810315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155201979128786327341873543 232802968693179491012810315)
            ·
              refine ⟨349204453039769236519215473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232802968693179491012810315 349204453039769236519215473)
              ·
                refine ⟨261903339779826927389411605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349204453039769236519215473 261903339779826927389411605)
                ·
                  refine ⟨12276719052179387221378669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 261903339779826927389411605 12276719052179387221378669)
                  ·
                    refine ⟨4603769644567270208017001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12276719052179387221378669 4603769644567270208017001)
                    ·
                      refine ⟨3452827233425452656012751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4603769644567270208017001 3452827233425452656012751)
                      ·
                        rfl

theorem cell23_6724357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 3, 2].length) (baseStart_6724357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724357 prefixEnd_6724357 := by exact prefixLift 6724357
  have htrace : WordTrace (prefixWord ++ tailWord_6724357) baseStart_6724357 baseEnd_6724357 := by
    simpa [prefixWord, tailWord_6724357, baseEnd_6724357] using wordTrace_append hprefix tailTrace_6724357
  have hstable : (prefixWord ++ tailWord_6724357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724357).length < 2 ^ (prefixWord ++ tailWord_6724357).sum := by decide
  have hdescent : baseEnd_6724357 < baseStart_6724357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724400 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 4]
def baseStart_6724400 : Nat := 118140960795 + 6724400 * 2 ^ 59
def prefixEnd_6724400 : Nat := 4983230072969 + 3 ^ 40 * 6724400 * 2
def baseEnd_6724400 : Nat := 3452849313093595987775053

theorem tailTrace_6724400 : CollatzResearch.WordTrace tailWord_6724400 prefixEnd_6724400 3452849313093595987775053 := by
  unfold tailWord_6724400
  simp only [CollatzResearch.WordTrace]
  refine ⟨122629508419327355466721327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163506011225769807288961769 122629508419327355466721327)
  ·
    refine ⟨183944262628991033200081991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122629508419327355466721327 183944262628991033200081991)
    ·
      refine ⟨275916393943486549800122987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183944262628991033200081991 275916393943486549800122987)
      ·
        refine ⟨413874590915229824700184481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275916393943486549800122987 413874590915229824700184481)
        ·
          refine ⟨310405943186422368525138361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413874590915229824700184481 310405943186422368525138361)
          ·
            refine ⟨232804457389816776393853771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310405943186422368525138361 232804457389816776393853771)
            ·
              refine ⟨349206686084725164590780657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232804457389816776393853771 349206686084725164590780657)
              ·
                refine ⟨261905014563543873443085493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349206686084725164590780657 261905014563543873443085493)
                ·
                  refine ⟨24553595115332238135289265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 261905014563543873443085493 24553595115332238135289265)
                  ·
                    refine ⟨18415196336499178601466949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24553595115332238135289265 18415196336499178601466949)
                    ·
                      refine ⟨3452849313093595987775053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18415196336499178601466949 3452849313093595987775053)
                      ·
                        rfl

theorem cell23_6724400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 4].length) (baseStart_6724400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724400 prefixEnd_6724400 := by exact prefixLift 6724400
  have htrace : WordTrace (prefixWord ++ tailWord_6724400) baseStart_6724400 baseEnd_6724400 := by
    simpa [prefixWord, tailWord_6724400, baseEnd_6724400] using wordTrace_append hprefix tailTrace_6724400
  have hstable : (prefixWord ++ tailWord_6724400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724400).length < 2 ^ (prefixWord ++ tailWord_6724400).sum := by decide
  have hdescent : baseEnd_6724400 < baseStart_6724400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724407 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 3]
def baseStart_6724407 : Nat := 118140960795 + 6724407 * 2 ^ 59
def prefixEnd_6724407 : Nat := 4983230072969 + 3 ^ 40 * 6724407 * 2
def baseEnd_6724407 : Nat := 3452852907458177460387521

theorem tailTrace_6724407 : CollatzResearch.WordTrace tailWord_6724407 prefixEnd_6724407 3452852907458177460387521 := by
  unfold tailWord_6724407
  simp only [CollatzResearch.WordTrace]
  refine ⟨245259272149629351128947475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163506181433086234085964983 245259272149629351128947475)
  ·
    refine ⟨367888908224444026693421213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245259272149629351128947475 367888908224444026693421213)
    ·
      refine ⟨137958340584166510010032955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 367888908224444026693421213 137958340584166510010032955)
      ·
        refine ⟨206937510876249765015049433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137958340584166510010032955 206937510876249765015049433)
        ·
          refine ⟨155203133157187323761287075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206937510876249765015049433 155203133157187323761287075)
          ·
            refine ⟨232804699735780985641930613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155203133157187323761287075 232804699735780985641930613)
            ·
              refine ⟨21825440600229467403930995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 232804699735780985641930613 21825440600229467403930995)
              ·
                refine ⟨32738160900344201105896493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21825440600229467403930995 32738160900344201105896493)
                ·
                  refine ⟨12276810337629075414711185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32738160900344201105896493 12276810337629075414711185)
                  ·
                    refine ⟨9207607753221806561033389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12276810337629075414711185 9207607753221806561033389)
                    ·
                      refine ⟨3452852907458177460387521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9207607753221806561033389 3452852907458177460387521)
                      ·
                        rfl

theorem cell23_6724407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 3].length) (baseStart_6724407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724407 prefixEnd_6724407 := by exact prefixLift 6724407
  have htrace : WordTrace (prefixWord ++ tailWord_6724407) baseStart_6724407 baseEnd_6724407 := by
    simpa [prefixWord, tailWord_6724407, baseEnd_6724407] using wordTrace_append hprefix tailTrace_6724407
  have hstable : (prefixWord ++ tailWord_6724407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724407).length < 2 ^ (prefixWord ++ tailWord_6724407).sum := by decide
  have hdescent : baseEnd_6724407 < baseStart_6724407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724414 : List Nat := [4, 2, 1, 2, 3, 1, 1, 2, 1, 6]
def baseStart_6724414 : Nat := 118140960795 + 6724414 * 2 ^ 59
def prefixEnd_6724414 : Nat := 4983230072969 + 3 ^ 40 * 6724414 * 2
def baseEnd_6724414 : Nat := 1150952167274252977666663

theorem tailTrace_6724414 : CollatzResearch.WordTrace tailWord_6724414 prefixEnd_6724414 1150952167274252977666663 := by
  unfold tailWord_6724414
  simp only [CollatzResearch.WordTrace]
  refine ⟨30657440932575498915556537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163506351640402660882968197 30657440932575498915556537)
  ·
    refine ⟨22993080699431624186667403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30657440932575498915556537 22993080699431624186667403)
    ·
      refine ⟨34489621049147436280001105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22993080699431624186667403 34489621049147436280001105)
      ·
        refine ⟨25867215786860577210000829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34489621049147436280001105 25867215786860577210000829)
        ·
          refine ⟨9700205920072716453750311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25867215786860577210000829 9700205920072716453750311)
          ·
            refine ⟨14550308880109074680625467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9700205920072716453750311 14550308880109074680625467)
            ·
              refine ⟨21825463320163612020938201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14550308880109074680625467 21825463320163612020938201)
              ·
                refine ⟨16369097490122709015703651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21825463320163612020938201 16369097490122709015703651)
                ·
                  refine ⟨24553646235184063523555477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16369097490122709015703651 24553646235184063523555477)
                  ·
                    refine ⟨1150952167274252977666663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24553646235184063523555477 1150952167274252977666663)
                    ·
                      rfl

theorem cell23_6724414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_6724414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724414 prefixEnd_6724414 := by exact prefixLift 6724414
  have htrace : WordTrace (prefixWord ++ tailWord_6724414) baseStart_6724414 baseEnd_6724414 := by
    simpa [prefixWord, tailWord_6724414, baseEnd_6724414] using wordTrace_append hprefix tailTrace_6724414
  have hstable : (prefixWord ++ tailWord_6724414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724414).length < 2 ^ (prefixWord ++ tailWord_6724414).sum := by decide
  have hdescent : baseEnd_6724414 < baseStart_6724414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724437 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 3, 3, 3]
def baseStart_6724437 : Nat := 118140960795 + 6724437 * 2 ^ 59
def prefixEnd_6724437 : Nat := 4983230072969 + 3 ^ 40 * 6724437 * 2
def baseEnd_6724437 : Nat := 3452868311877812343012383

theorem tailTrace_6724437 : CollatzResearch.WordTrace tailWord_6724437 prefixEnd_6724437 3452868311877812343012383 := by
  unfold tailWord_6724437
  simp only [CollatzResearch.WordTrace]
  refine ⟨245260366339520666252539565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163506910893013777501693043 245260366339520666252539565)
  ·
    refine ⟨91972637377320249844702337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245260366339520666252539565 91972637377320249844702337)
    ·
      refine ⟨68979478032990187383526753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91972637377320249844702337 68979478032990187383526753)
      ·
        refine ⟨51734608524742640537645065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68979478032990187383526753 51734608524742640537645065)
        ·
          refine ⟨38800956393556980403233799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51734608524742640537645065 38800956393556980403233799)
          ·
            refine ⟨58201434590335470604850699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38800956393556980403233799 58201434590335470604850699)
            ·
              refine ⟨87302151885503205907276049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58201434590335470604850699 87302151885503205907276049)
              ·
                refine ⟨65476613914127404430457037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87302151885503205907276049 65476613914127404430457037)
                ·
                  refine ⟨24553730217797776661421389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65476613914127404430457037 24553730217797776661421389)
                  ·
                    refine ⟨9207648831674166248033021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24553730217797776661421389 9207648831674166248033021)
                    ·
                      refine ⟨3452868311877812343012383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9207648831674166248033021 3452868311877812343012383)
                      ·
                        rfl

theorem cell23_6724437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_6724437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724437 prefixEnd_6724437 := by exact prefixLift 6724437
  have htrace : WordTrace (prefixWord ++ tailWord_6724437) baseStart_6724437 baseEnd_6724437 := by
    simpa [prefixWord, tailWord_6724437, baseEnd_6724437] using wordTrace_append hprefix tailTrace_6724437
  have hstable : (prefixWord ++ tailWord_6724437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724437).length < 2 ^ (prefixWord ++ tailWord_6724437).sum := by decide
  have hdescent : baseEnd_6724437 < baseStart_6724437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724444 : List Nat := [2, 2, 4, 2, 1, 3, 1, 8]
def baseStart_6724444 : Nat := 118140960795 + 6724444 * 2 ^ 59
def prefixEnd_6724444 : Nat := 4983230072969 + 3 ^ 40 * 6724444 * 2
def baseEnd_6724444 : Nat := 127884144675644215393513

theorem tailTrace_6724444 : CollatzResearch.WordTrace tailWord_6724444 prefixEnd_6724444 127884144675644215393513 := by
  unfold tailWord_6724444
  simp only [CollatzResearch.WordTrace]
  refine ⟨122630310825247653224022193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163507081100330204298696257 122630310825247653224022193)
  ·
    refine ⟨91972733118935739918016645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122630310825247653224022193 91972733118935739918016645)
    ·
      refine ⟨17244887459800451234628121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91972733118935739918016645 17244887459800451234628121)
      ·
        refine ⟨12933665594850338425971091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17244887459800451234628121 12933665594850338425971091)
        ·
          refine ⟨19400498392275507638956637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12933665594850338425971091 19400498392275507638956637)
          ·
            refine ⟨7275186897103315364608739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19400498392275507638956637 7275186897103315364608739)
            ·
              refine ⟨10912780345654973046913109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7275186897103315364608739 10912780345654973046913109)
              ·
                refine ⟨127884144675644215393513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10912780345654973046913109 127884144675644215393513)
                ·
                  rfl

theorem cell23_6724444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 8].length) (baseStart_6724444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724444 prefixEnd_6724444 := by exact prefixLift 6724444
  have htrace : WordTrace (prefixWord ++ tailWord_6724444) baseStart_6724444 baseEnd_6724444 := by
    simpa [prefixWord, tailWord_6724444, baseEnd_6724444] using wordTrace_append hprefix tailTrace_6724444
  have hstable : (prefixWord ++ tailWord_6724444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724444).length < 2 ^ (prefixWord ++ tailWord_6724444).sum := by decide
  have hdescent : baseEnd_6724444 < baseStart_6724444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724464 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 3, 3, 2]
def baseStart_6724464 : Nat := 118140960795 + 6724464 * 2 ^ 59
def prefixEnd_6724464 : Nat := 4983230072969 + 3 ^ 40 * 6724464 * 2
def baseEnd_6724464 : Nat := 3452882175855483737374759

theorem tailTrace_6724464 : CollatzResearch.WordTrace tailWord_6724464 prefixEnd_6724464 3452882175855483737374759 := by
  unfold tailWord_6724464
  simp only [CollatzResearch.WordTrace]
  refine ⟨122630675555211424931886223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163507567406948566575848297 122630675555211424931886223)
  ·
    refine ⟨183946013332817137397829335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122630675555211424931886223 183946013332817137397829335)
    ·
      refine ⟨275919019999225706096744003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183946013332817137397829335 275919019999225706096744003)
      ·
        refine ⟨413878529998838559145116005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275919019999225706096744003 413878529998838559145116005)
        ·
          refine ⟨77602224374782229839709251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 413878529998838559145116005 77602224374782229839709251)
          ·
            refine ⟨116403336562173344759563877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77602224374782229839709251 116403336562173344759563877)
            ·
              refine ⟨21825625605407502142418227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116403336562173344759563877 21825625605407502142418227)
              ·
                refine ⟨32738438408111253213627341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21825625605407502142418227 32738438408111253213627341)
                ·
                  refine ⟨12276914403041719955110253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32738438408111253213627341 12276914403041719955110253)
                  ·
                    refine ⟨4603842901140644983166345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12276914403041719955110253 4603842901140644983166345)
                    ·
                      refine ⟨3452882175855483737374759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4603842901140644983166345 3452882175855483737374759)
                      ·
                        rfl

theorem cell23_6724464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 3, 3, 2].length) (baseStart_6724464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724464 prefixEnd_6724464 := by exact prefixLift 6724464
  have htrace : WordTrace (prefixWord ++ tailWord_6724464) baseStart_6724464 baseEnd_6724464 := by
    simpa [prefixWord, tailWord_6724464, baseEnd_6724464] using wordTrace_append hprefix tailTrace_6724464
  have hstable : (prefixWord ++ tailWord_6724464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724464).length < 2 ^ (prefixWord ++ tailWord_6724464).sum := by decide
  have hdescent : baseEnd_6724464 < baseStart_6724464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724482 : List Nat := [3, 4, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_6724482 : Nat := 118140960795 + 6724482 * 2 ^ 59
def prefixEnd_6724482 : Nat := 4983230072969 + 3 ^ 40 * 6724482 * 2
def baseEnd_6724482 : Nat := 1150963806169088222316559

theorem tailTrace_6724482 : CollatzResearch.WordTrace tailWord_6724482 prefixEnd_6724482 1150963806169088222316559 := by
  unfold tailWord_6724482
  simp only [CollatzResearch.WordTrace]
  refine ⟨61315501906089409734481925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163508005082905092625285133 61315501906089409734481925)
  ·
    refine ⟨11496656607391764325215361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61315501906089409734481925 11496656607391764325215361)
    ·
      refine ⟨8622492455543823243911521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11496656607391764325215361 8622492455543823243911521)
      ·
        refine ⟨6466869341657867432933641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8622492455543823243911521 6466869341657867432933641)
        ·
          refine ⟨4850152006243400574700231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6466869341657867432933641 4850152006243400574700231)
          ·
            refine ⟨7275228009365100862050347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4850152006243400574700231 7275228009365100862050347)
            ·
              refine ⟨10912842014047651293075521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7275228009365100862050347 10912842014047651293075521)
              ·
                refine ⟨8184631510535738469806641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10912842014047651293075521 8184631510535738469806641)
                ·
                  refine ⟨6138473632901803852354981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8184631510535738469806641 6138473632901803852354981)
                  ·
                    refine ⟨1150963806169088222316559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6138473632901803852354981 1150963806169088222316559)
                    ·
                      rfl

theorem cell23_6724482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_6724482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724482 prefixEnd_6724482 := by exact prefixLift 6724482
  have htrace : WordTrace (prefixWord ++ tailWord_6724482) baseStart_6724482 baseEnd_6724482 := by
    simpa [prefixWord, tailWord_6724482, baseEnd_6724482] using wordTrace_append hprefix tailTrace_6724482
  have hstable : (prefixWord ++ tailWord_6724482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724482).length < 2 ^ (prefixWord ++ tailWord_6724482).sum := by decide
  have hdescent : baseEnd_6724482 < baseStart_6724482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724487 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 2, 6]
def baseStart_6724487 : Nat := 118140960795 + 6724487 * 2 ^ 59
def prefixEnd_6724487 : Nat := 4983230072969 + 3 ^ 40 * 6724487 * 2
def baseEnd_6724487 : Nat := 1150964661970179049129051

theorem tailTrace_6724487 : CollatzResearch.WordTrace tailWord_6724487 prefixEnd_6724487 1150964661970179049129051 := by
  unfold tailWord_6724487
  simp only [CollatzResearch.WordTrace]
  refine ⟨245262189989339524791859715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163508126659559683194573143 245262189989339524791859715)
  ·
    refine ⟨367893284984009287187789573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245262189989339524791859715 367893284984009287187789573)
    ·
      refine ⟨68979990934501741347710545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 367893284984009287187789573 68979990934501741347710545)
      ·
        refine ⟨51734993200876306010782909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68979990934501741347710545 51734993200876306010782909)
        ·
          refine ⟨19400622450328614754043591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51734993200876306010782909 19400622450328614754043591)
          ·
            refine ⟨29100933675492922131065387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19400622450328614754043591 29100933675492922131065387)
            ·
              refine ⟨43651400513239383196598081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29100933675492922131065387 43651400513239383196598081)
              ·
                refine ⟨32738550384929537397448561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43651400513239383196598081 32738550384929537397448561)
                ·
                  refine ⟨24553912788697153048086421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32738550384929537397448561 24553912788697153048086421)
                  ·
                    refine ⟨1150964661970179049129051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24553912788697153048086421 1150964661970179049129051)
                    ·
                      rfl

theorem cell23_6724487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_6724487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724487 prefixEnd_6724487 := by exact prefixLift 6724487
  have htrace : WordTrace (prefixWord ++ tailWord_6724487) baseStart_6724487 baseEnd_6724487 := by
    simpa [prefixWord, tailWord_6724487, baseEnd_6724487] using wordTrace_append hprefix tailTrace_6724487
  have hstable : (prefixWord ++ tailWord_6724487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724487).length < 2 ^ (prefixWord ++ tailWord_6724487).sum := by decide
  have hdescent : baseEnd_6724487 < baseStart_6724487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724488 : List Nat := [2, 1, 3, 3, 2, 3, 1, 2, 2, 1, 3]
def baseStart_6724488 : Nat := 118140960795 + 6724488 * 2 ^ 59
def prefixEnd_6724488 : Nat := 4983230072969 + 3 ^ 40 * 6724488 * 2
def baseEnd_6724488 : Nat := 3452894499391191643474649

theorem tailTrace_6724488 : CollatzResearch.WordTrace tailWord_6724488 prefixEnd_6724488 3452894499391191643474649 := by
  unfold tailWord_6724488
  simp only [CollatzResearch.WordTrace]
  refine ⟨122631113231167950981323059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163508150974890601308430745 122631113231167950981323059)
  ·
    refine ⟨183946669846751926471984589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122631113231167950981323059 183946669846751926471984589)
    ·
      refine ⟨68980001192531972426994221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183946669846751926471984589 68980001192531972426994221)
      ·
        refine ⟨25867500447199489660122833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68980001192531972426994221 25867500447199489660122833)
        ·
          refine ⟨19400625335399617245092125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25867500447199489660122833 19400625335399617245092125)
          ·
            refine ⟨7275234500774856466909547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19400625335399617245092125 7275234500774856466909547)
            ·
              refine ⟨10912851751162284700364321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7275234500774856466909547 10912851751162284700364321)
              ·
                refine ⟨8184638813371713525273241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10912851751162284700364321 8184638813371713525273241)
                ·
                  refine ⟨6138479110028785143954931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8184638813371713525273241 6138479110028785143954931)
                  ·
                    refine ⟨9207718665043177715932397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6138479110028785143954931 9207718665043177715932397)
                    ·
                      refine ⟨3452894499391191643474649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9207718665043177715932397 3452894499391191643474649)
                      ·
                        rfl

theorem cell23_6724488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_6724488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724488 prefixEnd_6724488 := by exact prefixLift 6724488
  have htrace : WordTrace (prefixWord ++ tailWord_6724488) baseStart_6724488 baseEnd_6724488 := by
    simpa [prefixWord, tailWord_6724488, baseEnd_6724488] using wordTrace_append hprefix tailTrace_6724488
  have hstable : (prefixWord ++ tailWord_6724488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724488).length < 2 ^ (prefixWord ++ tailWord_6724488).sum := by decide
  have hdescent : baseEnd_6724488 < baseStart_6724488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724511 : List Nat := [1, 1, 2, 5, 2, 1, 3, 1, 1, 4, 2]
def baseStart_6724511 : Nat := 118140960795 + 6724511 * 2 ^ 59
def prefixEnd_6724511 : Nat := 4983230072969 + 3 ^ 40 * 6724511 * 2
def baseEnd_6724511 : Nat := 3452906309446245053487043

theorem tailTrace_6724511 : CollatzResearch.WordTrace tailWord_6724511 prefixEnd_6724511 3452906309446245053487043 := by
  unfold tailWord_6724511
  simp only [CollatzResearch.WordTrace]
  refine ⟨245263065341252576890733387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163508710227501717927155591 245263065341252576890733387)
  ·
    refine ⟨367894598011878865336100081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245263065341252576890733387 367894598011878865336100081)
    ·
      refine ⟨275920948508909149002075061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367894598011878865336100081 275920948508909149002075061)
      ·
        refine ⟨25867588922710232718944537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 275920948508909149002075061 25867588922710232718944537)
        ·
          refine ⟨19400691692032674539208403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25867588922710232718944537 19400691692032674539208403)
          ·
            refine ⟨29101037538049011808812605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19400691692032674539208403 29101037538049011808812605)
            ·
              refine ⟨10912889076768379428304727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29101037538049011808812605 10912889076768379428304727)
              ·
                refine ⟨16369333615152569142457091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10912889076768379428304727 16369333615152569142457091)
                ·
                  refine ⟨24554000422728853713685637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16369333615152569142457091 24554000422728853713685637)
                  ·
                    refine ⟨4603875079261660071316057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24554000422728853713685637 4603875079261660071316057)
                    ·
                      refine ⟨3452906309446245053487043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4603875079261660071316057 3452906309446245053487043)
                      ·
                        rfl

theorem cell23_6724511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_6724511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724511 prefixEnd_6724511 := by exact prefixLift 6724511
  have htrace : WordTrace (prefixWord ++ tailWord_6724511) baseStart_6724511 baseEnd_6724511 := by
    simpa [prefixWord, tailWord_6724511, baseEnd_6724511] using wordTrace_append hprefix tailTrace_6724511
  have hstable : (prefixWord ++ tailWord_6724511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724511).length < 2 ^ (prefixWord ++ tailWord_6724511).sum := by decide
  have hdescent : baseEnd_6724511 < baseStart_6724511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724527 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 3]
def baseStart_6724527 : Nat := 118140960795 + 6724527 * 2 ^ 59
def prefixEnd_6724527 : Nat := 4983230072969 + 3 ^ 40 * 6724527 * 2
def baseEnd_6724527 : Nat := 3452914525136716990886969

theorem tailTrace_6724527 : CollatzResearch.WordTrace tailWord_6724527 prefixEnd_6724527 3452914525136716990886969 := by
  unfold tailWord_6724527
  simp only [CollatzResearch.WordTrace]
  refine ⟨245263648909194611623315835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163509099272796407748877223 245263648909194611623315835)
  ·
    refine ⟨367895473363791917434973753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245263648909194611623315835 367895473363791917434973753)
    ·
      refine ⟨275921605022843938076230315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367895473363791917434973753 275921605022843938076230315)
      ·
        refine ⟨413882407534265907114345473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275921605022843938076230315 413882407534265907114345473)
        ·
          refine ⟨310411805650699430335759105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413882407534265907114345473 310411805650699430335759105)
          ·
            refine ⟨232808854238024572751819329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310411805650699430335759105 232808854238024572751819329)
            ·
              refine ⟨174606640678518429563864497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232808854238024572751819329 174606640678518429563864497)
              ·
                refine ⟨130954980508888822172898373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174606640678518429563864497 130954980508888822172898373)
                ·
                  refine ⟨24554058845416654157418445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130954980508888822172898373 24554058845416654157418445)
                  ·
                    refine ⟨9207772067031245309031917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24554058845416654157418445 9207772067031245309031917)
                    ·
                      refine ⟨3452914525136716990886969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9207772067031245309031917 3452914525136716990886969)
                      ·
                        rfl

theorem cell23_6724527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 3].length) (baseStart_6724527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724527 prefixEnd_6724527 := by exact prefixLift 6724527
  have htrace : WordTrace (prefixWord ++ tailWord_6724527) baseStart_6724527 baseEnd_6724527 := by
    simpa [prefixWord, tailWord_6724527, baseEnd_6724527] using wordTrace_append hprefix tailTrace_6724527
  have hstable : (prefixWord ++ tailWord_6724527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724527).length < 2 ^ (prefixWord ++ tailWord_6724527).sum := by decide
  have hdescent : baseEnd_6724527 < baseStart_6724527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724547 : List Nat := [1, 1, 1, 3, 1, 1, 2, 6, 2, 5]
def baseStart_6724547 : Nat := 118140960795 + 6724547 * 2 ^ 59
def prefixEnd_6724547 : Nat := 4983230072969 + 3 ^ 40 * 6724547 * 2
def baseEnd_6724547 : Nat := 1150974931583268970878959

theorem tailTrace_6724547 : CollatzResearch.WordTrace tailWord_6724547 prefixEnd_6724547 1150974931583268970878959 := by
  unfold tailWord_6724547
  simp only [CollatzResearch.WordTrace]
  refine ⟨245264378369122155039043895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163509585579414770026029263 245264378369122155039043895)
  ·
    refine ⟨367896567553683232558565843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245264378369122155039043895 367896567553683232558565843)
    ·
      refine ⟨551844851330524848837848765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367896567553683232558565843 551844851330524848837848765)
      ·
        refine ⟨206941819248946818314193287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 551844851330524848837848765 206941819248946818314193287)
        ·
          refine ⟨310412728873420227471289931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206941819248946818314193287 310412728873420227471289931)
          ·
            refine ⟨465619093310130341206934897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310412728873420227471289931 465619093310130341206934897)
            ·
              refine ⟨349214319982597755905201173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465619093310130341206934897 349214319982597755905201173)
              ·
                refine ⟨16369421249184269808056305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 349214319982597755905201173 16369421249184269808056305)
                ·
                  refine ⟨12277065936888202356042229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16369421249184269808056305 12277065936888202356042229)
                  ·
                    refine ⟨1150974931583268970878959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12277065936888202356042229 1150974931583268970878959)
                    ·
                      rfl

theorem cell23_6724547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 5].length) (baseStart_6724547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724547 prefixEnd_6724547 := by exact prefixLift 6724547
  have htrace : WordTrace (prefixWord ++ tailWord_6724547) baseStart_6724547 baseEnd_6724547 := by
    simpa [prefixWord, tailWord_6724547, baseEnd_6724547] using wordTrace_append hprefix tailTrace_6724547
  have hstable : (prefixWord ++ tailWord_6724547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724547).length < 2 ^ (prefixWord ++ tailWord_6724547).sum := by decide
  have hdescent : baseEnd_6724547 < baseStart_6724547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724554 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 2, 5, 2]
def baseStart_6724554 : Nat := 118140960795 + 6724554 * 2 ^ 59
def prefixEnd_6724554 : Nat := 4983230072969 + 3 ^ 40 * 6724554 * 2
def baseEnd_6724554 : Nat := 3452928389114388385249345

theorem tailTrace_6724554 : CollatzResearch.WordTrace tailWord_6724554 prefixEnd_6724554 3452928389114388385249345 := by
  unfold tailWord_6724554
  simp only [CollatzResearch.WordTrace]
  refine ⟨61316158420024198808637179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163509755786731196823032477 61316158420024198808637179)
  ·
    refine ⟨91974237630036298212955769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61316158420024198808637179 91974237630036298212955769)
    ·
      refine ⟨68980678222527223659716827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91974237630036298212955769 68980678222527223659716827)
      ·
        refine ⟨103471017333790835489575241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68980678222527223659716827 103471017333790835489575241)
        ·
          refine ⟨77603263000343126617181431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103471017333790835489575241 77603263000343126617181431)
          ·
            refine ⟨116404894500514689925772147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77603263000343126617181431 116404894500514689925772147)
            ·
              refine ⟨174607341750772034888658221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116404894500514689925772147 174607341750772034888658221)
              ·
                refine ⟨65477753156539513083246833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174607341750772034888658221 65477753156539513083246833)
                ·
                  refine ⟨49108314867404634812435125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65477753156539513083246833 49108314867404634812435125)
                  ·
                    refine ⟨4603904518819184513665793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49108314867404634812435125 4603904518819184513665793)
                    ·
                      refine ⟨3452928389114388385249345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4603904518819184513665793 3452928389114388385249345)
                      ·
                        rfl

theorem cell23_6724554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 2, 5, 2].length) (baseStart_6724554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724554 prefixEnd_6724554 := by exact prefixLift 6724554
  have htrace : WordTrace (prefixWord ++ tailWord_6724554) baseStart_6724554 baseEnd_6724554 := by
    simpa [prefixWord, tailWord_6724554, baseEnd_6724554] using wordTrace_append hprefix tailTrace_6724554
  have hstable : (prefixWord ++ tailWord_6724554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724554).length < 2 ^ (prefixWord ++ tailWord_6724554).sum := by decide
  have hdescent : baseEnd_6724554 < baseStart_6724554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724562 : List Nat := [3, 2, 2, 3, 1, 3, 2, 1, 2, 2, 2]
def baseStart_6724562 : Nat := 118140960795 + 6724562 * 2 ^ 59
def prefixEnd_6724562 : Nat := 4983230072969 + 3 ^ 40 * 6724562 * 2
def baseEnd_6724562 : Nat := 3452932496959624353949309

theorem tailTrace_6724562 : CollatzResearch.WordTrace tailWord_6724562 prefixEnd_6724562 3452932496959624353949309 := by
  unfold tailWord_6724562
  simp only [CollatzResearch.WordTrace]
  refine ⟨61316231366016953150209985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163509950309378541733893293 61316231366016953150209985)
  ·
    refine ⟨45987173524512714862657489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61316231366016953150209985 45987173524512714862657489)
    ·
      refine ⟨34490380143384536146993117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45987173524512714862657489 34490380143384536146993117)
      ·
        refine ⟨12933892553769201055122419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34490380143384536146993117 12933892553769201055122419)
        ·
          refine ⟨19400838830653801582683629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12933892553769201055122419 19400838830653801582683629)
          ·
            refine ⟨7275314561495175593506361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19400838830653801582683629 7275314561495175593506361)
            ·
              refine ⟨5456485921121381695129771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7275314561495175593506361 5456485921121381695129771)
              ·
                refine ⟨8184728881682072542694657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5456485921121381695129771 8184728881682072542694657)
                ·
                  refine ⟨6138546661261554407020993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8184728881682072542694657 6138546661261554407020993)
                  ·
                    refine ⟨4603909995946165805265745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6138546661261554407020993 4603909995946165805265745)
                    ·
                      refine ⟨3452932496959624353949309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4603909995946165805265745 3452932496959624353949309)
                      ·
                        rfl

theorem cell23_6724562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_6724562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724562 prefixEnd_6724562 := by exact prefixLift 6724562
  have htrace : WordTrace (prefixWord ++ tailWord_6724562) baseStart_6724562 baseEnd_6724562 := by
    simpa [prefixWord, tailWord_6724562, baseEnd_6724562] using wordTrace_append hprefix tailTrace_6724562
  have hstable : (prefixWord ++ tailWord_6724562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724562).length < 2 ^ (prefixWord ++ tailWord_6724562).sum := by decide
  have hdescent : baseEnd_6724562 < baseStart_6724562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724567 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 4]
def baseStart_6724567 : Nat := 118140960795 + 6724567 * 2 ^ 59
def prefixEnd_6724567 : Nat := 4983230072969 + 3 ^ 40 * 6724567 * 2
def baseEnd_6724567 : Nat := 3452935064362896834386785

theorem tailTrace_6724567 : CollatzResearch.WordTrace tailWord_6724567 prefixEnd_6724567 3452935064362896834386785 := by
  unfold tailWord_6724567
  simp only [CollatzResearch.WordTrace]
  refine ⟨245265107829049698454771955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163510071886033132303181303 245265107829049698454771955)
  ·
    refine ⟨367897661743574547682157933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245265107829049698454771955 367897661743574547682157933)
    ·
      refine ⟨137961623153840455380809225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 367897661743574547682157933 137961623153840455380809225)
      ·
        refine ⟨103471217365380341535606919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137961623153840455380809225 103471217365380341535606919)
        ·
          refine ⟨155206826048070512303410379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103471217365380341535606919 155206826048070512303410379)
          ·
            refine ⟨232810239072105768455115569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155206826048070512303410379 232810239072105768455115569)
            ·
              refine ⟨174607679304079326341336677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232810239072105768455115569 174607679304079326341336677)
              ·
                refine ⟨32738939869514873689000627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174607679304079326341336677 32738939869514873689000627)
                ·
                  refine ⟨49108409804272310533500941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32738939869514873689000627 49108409804272310533500941)
                  ·
                    refine ⟨18415653676602116450062853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49108409804272310533500941 18415653676602116450062853)
                    ·
                      refine ⟨3452935064362896834386785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18415653676602116450062853 3452935064362896834386785)
                      ·
                        rfl

theorem cell23_6724567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_6724567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724567 prefixEnd_6724567 := by exact prefixLift 6724567
  have htrace : WordTrace (prefixWord ++ tailWord_6724567) baseStart_6724567 baseEnd_6724567 := by
    simpa [prefixWord, tailWord_6724567, baseEnd_6724567] using wordTrace_append hprefix tailTrace_6724567
  have hstable : (prefixWord ++ tailWord_6724567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724567).length < 2 ^ (prefixWord ++ tailWord_6724567).sum := by decide
  have hdescent : baseEnd_6724567 < baseStart_6724567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724584 : List Nat := [2, 1, 4, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_6724584 : Nat := 118140960795 + 6724584 * 2 ^ 59
def prefixEnd_6724584 : Nat := 4983230072969 + 3 ^ 40 * 6724584 * 2
def baseEnd_6724584 : Nat := 3452943793534023267874207

theorem tailTrace_6724584 : CollatzResearch.WordTrace tailWord_6724584 prefixEnd_6724584 3452943793534023267874207 := by
  unfold tailWord_6724584
  simp only [CollatzResearch.WordTrace]
  refine ⟨122632863934994055179070403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163510485246658740238760537 122632863934994055179070403)
  ·
    refine ⟨183949295902491082768605605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122632863934994055179070403 183949295902491082768605605)
    ·
      refine ⟨34490492981717078019113551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183949295902491082768605605 34490492981717078019113551)
      ·
        refine ⟨51735739472575617028670327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34490492981717078019113551 51735739472575617028670327)
        ·
          refine ⟨77603609208863425543005491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51735739472575617028670327 77603609208863425543005491)
          ·
            refine ⟨116405413813295138314508237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77603609208863425543005491 116405413813295138314508237)
            ·
              refine ⟨43652030179985676867940589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116405413813295138314508237 43652030179985676867940589)
              ·
                refine ⟨16369511317494628825477721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43652030179985676867940589 16369511317494628825477721)
                ·
                  refine ⟨12277133488120971619108291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16369511317494628825477721 12277133488120971619108291)
                  ·
                    refine ⟨18415700232181457428662437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12277133488120971619108291 18415700232181457428662437)
                    ·
                      refine ⟨3452943793534023267874207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18415700232181457428662437 3452943793534023267874207)
                      ·
                        rfl

theorem cell23_6724584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_6724584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724584 prefixEnd_6724584 := by exact prefixLift 6724584
  have htrace : WordTrace (prefixWord ++ tailWord_6724584) baseStart_6724584 baseEnd_6724584 := by
    simpa [prefixWord, tailWord_6724584, baseEnd_6724584] using wordTrace_append hprefix tailTrace_6724584
  have hstable : (prefixWord ++ tailWord_6724584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724584).length < 2 ^ (prefixWord ++ tailWord_6724584).sum := by decide
  have hdescent : baseEnd_6724584 < baseStart_6724584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724596 : List Nat := [2, 6, 2, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_6724596 : Nat := 118140960795 + 6724596 * 2 ^ 59
def prefixEnd_6724596 : Nat := 4983230072969 + 3 ^ 40 * 6724596 * 2
def baseEnd_6724596 : Nat := 3452949955301877220924153

theorem tailTrace_6724596 : CollatzResearch.WordTrace tailWord_6724596 prefixEnd_6724596 3452949955301877220924153 := by
  unfold tailWord_6724596
  simp only [CollatzResearch.WordTrace]
  refine ⟨122633082772972318203788821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163510777030629757605051761 122633082772972318203788821)
  ·
    refine ⟨5748425754983077415802601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 122633082772972318203788821 5748425754983077415802601)
    ·
      refine ⟨4311319316237308061851951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5748425754983077415802601 4311319316237308061851951)
      ·
        refine ⟨6466978974355962092777927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4311319316237308061851951 6466978974355962092777927)
        ·
          refine ⟨9700468461533943139166891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6466978974355962092777927 9700468461533943139166891)
          ·
            refine ⟨14550702692300914708750337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9700468461533943139166891 14550702692300914708750337)
            ·
              refine ⟨10913027019225686031562753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14550702692300914708750337 10913027019225686031562753)
              ·
                refine ⟨8184770264419264523672065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10913027019225686031562753 8184770264419264523672065)
                ·
                  refine ⟨6138577698314448392754049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8184770264419264523672065 6138577698314448392754049)
                  ·
                    refine ⟨4603933273735836294565537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6138577698314448392754049 4603933273735836294565537)
                    ·
                      refine ⟨3452949955301877220924153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4603933273735836294565537 3452949955301877220924153)
                      ·
                        rfl

theorem cell23_6724596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_6724596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724596 prefixEnd_6724596 := by exact prefixLift 6724596
  have htrace : WordTrace (prefixWord ++ tailWord_6724596) baseStart_6724596 baseEnd_6724596 := by
    simpa [prefixWord, tailWord_6724596, baseEnd_6724596] using wordTrace_append hprefix tailTrace_6724596
  have hstable : (prefixWord ++ tailWord_6724596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724596).length < 2 ^ (prefixWord ++ tailWord_6724596).sum := by decide
  have hdescent : baseEnd_6724596 < baseStart_6724596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724661 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 4, 3, 2]
def baseStart_6724661 : Nat := 118140960795 + 6724661 * 2 ^ 59
def prefixEnd_6724661 : Nat := 4983230072969 + 3 ^ 40 * 6724661 * 2
def baseEnd_6724661 : Nat := 3452983331544419466611353

theorem tailTrace_6724661 : CollatzResearch.WordTrace tailWord_6724661 prefixEnd_6724661 3452983331544419466611353 := by
  unfold tailWord_6724661
  simp only [CollatzResearch.WordTrace]
  refine ⟨245268536290709152508693837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163512357527139435005795891 245268536290709152508693837)
  ·
    refine ⟨91975701109015932190760189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245268536290709152508693837 91975701109015932190760189)
    ·
      refine ⟨34490887915880974571535071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91975701109015932190760189 34490887915880974571535071)
      ·
        refine ⟨51736331873821461857302607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34490887915880974571535071 51736331873821461857302607)
        ·
          refine ⟨77604497810732192785953911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51736331873821461857302607 77604497810732192785953911)
          ·
            refine ⟨116406746716098289178930867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77604497810732192785953911 116406746716098289178930867)
            ·
              refine ⟨174610120074147433768396301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116406746716098289178930867 174610120074147433768396301)
              ·
                refine ⟨65478795027805287663148613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174610120074147433768396301 65478795027805287663148613)
                ·
                  refine ⟨12277274067713491436840365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65478795027805287663148613 12277274067713491436840365)
                  ·
                    refine ⟨4603977775392559288815137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12277274067713491436840365 4603977775392559288815137)
                    ·
                      refine ⟨3452983331544419466611353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4603977775392559288815137 3452983331544419466611353)
                      ·
                        rfl

theorem cell23_6724661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_6724661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724661 prefixEnd_6724661 := by exact prefixLift 6724661
  have htrace : WordTrace (prefixWord ++ tailWord_6724661) baseStart_6724661 baseEnd_6724661 := by
    simpa [prefixWord, tailWord_6724661, baseEnd_6724661] using wordTrace_append hprefix tailTrace_6724661
  have hstable : (prefixWord ++ tailWord_6724661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724661).length < 2 ^ (prefixWord ++ tailWord_6724661).sum := by decide
  have hdescent : baseEnd_6724661 < baseStart_6724661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724668 : List Nat := [2, 2, 2, 2, 2, 3, 2, 1, 3, 1, 3]
def baseStart_6724668 : Nat := 118140960795 + 6724668 * 2 ^ 59
def prefixEnd_6724668 : Nat := 4983230072969 + 3 ^ 40 * 6724668 * 2
def baseEnd_6724668 : Nat := 3452986925909000939223821

theorem tailTrace_6724668 : CollatzResearch.WordTrace tailWord_6724668 prefixEnd_6724668 3452986925909000939223821 := by
  unfold tailWord_6724668
  simp only [CollatzResearch.WordTrace]
  refine ⟨122634395800841896352099329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163512527734455861802799105 122634395800841896352099329)
  ·
    refine ⟨91975796850631422264074497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122634395800841896352099329 91975796850631422264074497)
    ·
      refine ⟨68981847637973566698055873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91975796850631422264074497 68981847637973566698055873)
      ·
        refine ⟨51736385728480175023541905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68981847637973566698055873 51736385728480175023541905)
        ·
          refine ⟨38802289296360131267656429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51736385728480175023541905 38802289296360131267656429)
          ·
            refine ⟨14550858486135049225371161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38802289296360131267656429 14550858486135049225371161)
            ·
              refine ⟨10913143864601286919028371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14550858486135049225371161 10913143864601286919028371)
              ·
                refine ⟨16369715796901930378542557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10913143864601286919028371 16369715796901930378542557)
                ·
                  refine ⟨6138643423838223891953459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16369715796901930378542557 6138643423838223891953459)
                  ·
                    refine ⟨9207965135757335837930189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6138643423838223891953459 9207965135757335837930189)
                    ·
                      refine ⟨3452986925909000939223821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9207965135757335837930189 3452986925909000939223821)
                      ·
                        rfl

theorem cell23_6724668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_6724668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724668 prefixEnd_6724668 := by exact prefixLift 6724668
  have htrace : WordTrace (prefixWord ++ tailWord_6724668) baseStart_6724668 baseEnd_6724668 := by
    simpa [prefixWord, tailWord_6724668, baseEnd_6724668] using wordTrace_append hprefix tailTrace_6724668
  have hstable : (prefixWord ++ tailWord_6724668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724668).length < 2 ^ (prefixWord ++ tailWord_6724668).sum := by decide
  have hdescent : baseEnd_6724668 < baseStart_6724668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724704 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 4]
def baseStart_6724704 : Nat := 118140960795 + 6724704 * 2 ^ 59
def prefixEnd_6724704 : Nat := 4983230072969 + 3 ^ 40 * 6724704 * 2
def baseEnd_6724704 : Nat := 3453005411212562798373655

theorem tailTrace_6724704 : CollatzResearch.WordTrace tailWord_6724704 prefixEnd_6724704 3453005411212562798373655 := by
  unfold tailWord_6724704
  simp only [CollatzResearch.WordTrace]
  refine ⟨122635052314776685426254583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163513403086368913901672777 122635052314776685426254583)
  ·
    refine ⟨183952578472165028139381875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122635052314776685426254583 183952578472165028139381875)
    ·
      refine ⟨275928867708247542209072813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183952578472165028139381875 275928867708247542209072813)
      ·
        refine ⟨103473325390592828328402305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275928867708247542209072813 103473325390592828328402305)
        ·
          refine ⟨77604994042944621246301729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103473325390592828328402305 77604994042944621246301729)
          ·
            refine ⟨58203745532208465934726297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77604994042944621246301729 58203745532208465934726297)
            ·
              refine ⟨43652809149156349451044723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58203745532208465934726297 43652809149156349451044723)
              ·
                refine ⟨65479213723734524176567085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43652809149156349451044723 65479213723734524176567085)
                ·
                  refine ⟨24554705146400446566212657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65479213723734524176567085 24554705146400446566212657)
                  ·
                    refine ⟨18416028859800334924659493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24554705146400446566212657 18416028859800334924659493)
                    ·
                      refine ⟨3453005411212562798373655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18416028859800334924659493 3453005411212562798373655)
                      ·
                        rfl

theorem cell23_6724704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_6724704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724704 prefixEnd_6724704 := by exact prefixLift 6724704
  have htrace : WordTrace (prefixWord ++ tailWord_6724704) baseStart_6724704 baseEnd_6724704 := by
    simpa [prefixWord, tailWord_6724704, baseEnd_6724704] using wordTrace_append hprefix tailTrace_6724704
  have hstable : (prefixWord ++ tailWord_6724704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724704).length < 2 ^ (prefixWord ++ tailWord_6724704).sum := by decide
  have hdescent : baseEnd_6724704 < baseStart_6724704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724711 : List Nat := [1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 5]
def baseStart_6724711 : Nat := 118140960795 + 6724711 * 2 ^ 59
def prefixEnd_6724711 : Nat := 4983230072969 + 3 ^ 40 * 6724711 * 2
def baseEnd_6724711 : Nat := 3453009005577144270986123

theorem tailTrace_6724711 : CollatzResearch.WordTrace tailWord_6724711 prefixEnd_6724711 3453009005577144270986123 := by
  unfold tailWord_6724711
  simp only [CollatzResearch.WordTrace]
  refine ⟨245270359940528011048013987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163513573293685340698675991 245270359940528011048013987)
  ·
    refine ⟨367905539910792016572020981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245270359940528011048013987 367905539910792016572020981)
    ·
      refine ⟨34491144366636751553626967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 367905539910792016572020981 34491144366636751553626967)
      ·
        refine ⟨51736716549955127330440451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34491144366636751553626967 51736716549955127330440451)
        ·
          refine ⟨77605074824932690995660677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51736716549955127330440451 77605074824932690995660677)
          ·
            refine ⟨14550951529674879561686377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77605074824932690995660677 14550951529674879561686377)
            ·
              refine ⟨10913213647256159671264783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14550951529674879561686377 10913213647256159671264783)
              ·
                refine ⟨16369820470884239506897175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10913213647256159671264783 16369820470884239506897175)
                ·
                  refine ⟨24554730706326359260345763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16369820470884239506897175 24554730706326359260345763)
                  ·
                    refine ⟨36832096059489538890518645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24554730706326359260345763 36832096059489538890518645)
                    ·
                      refine ⟨3453009005577144270986123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36832096059489538890518645 3453009005577144270986123)
                      ·
                        rfl

theorem cell23_6724711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_6724711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724711 prefixEnd_6724711 := by exact prefixLift 6724711
  have htrace : WordTrace (prefixWord ++ tailWord_6724711) baseStart_6724711 baseEnd_6724711 := by
    simpa [prefixWord, tailWord_6724711, baseEnd_6724711] using wordTrace_append hprefix tailTrace_6724711
  have hstable : (prefixWord ++ tailWord_6724711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724711).length < 2 ^ (prefixWord ++ tailWord_6724711).sum := by decide
  have hdescent : baseEnd_6724711 < baseStart_6724711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724714 : List Nat := [3, 1, 3, 2, 2, 1, 11]
def baseStart_6724714 : Nat := 118140960795 + 6724714 * 2 ^ 59
def prefixEnd_6724714 : Nat := 4983230072969 + 3 ^ 40 * 6724714 * 2
def baseEnd_6724714 : Nat := 42629759827396392089489

theorem tailTrace_6724714 : CollatzResearch.WordTrace tailWord_6724714 prefixEnd_6724714 42629759827396392089489 := by
  unfold tailWord_6724714
  simp only [CollatzResearch.WordTrace]
  refine ⟨61317617339879285640093299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163513646239678095040248797 61317617339879285640093299)
  ·
    refine ⟨91976426009818928460139949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61317617339879285640093299 91976426009818928460139949)
    ·
      refine ⟨34491159753682098172552481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91976426009818928460139949 34491159753682098172552481)
      ·
        refine ⟨25868369815261573629414361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34491159753682098172552481 25868369815261573629414361)
        ·
          refine ⟨19401277361446180222060771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25868369815261573629414361 19401277361446180222060771)
          ·
            refine ⟨29101916042169270333091157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19401277361446180222060771 29101916042169270333091157)
            ·
              refine ⟨42629759827396392089489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29101916042169270333091157 42629759827396392089489)
              ·
                rfl

theorem cell23_6724714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 11].length) (baseStart_6724714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724714 prefixEnd_6724714 := by exact prefixLift 6724714
  have htrace : WordTrace (prefixWord ++ tailWord_6724714) baseStart_6724714 baseEnd_6724714 := by
    simpa [prefixWord, tailWord_6724714, baseEnd_6724714] using wordTrace_append hprefix tailTrace_6724714
  have hstable : (prefixWord ++ tailWord_6724714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724714).length < 2 ^ (prefixWord ++ tailWord_6724714).sum := by decide
  have hdescent : baseEnd_6724714 < baseStart_6724714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724775 : List Nat := [1, 1, 6, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_6724775 : Nat := 118140960795 + 6724775 * 2 ^ 59
def prefixEnd_6724775 : Nat := 4983230072969 + 3 ^ 40 * 6724775 * 2
def baseEnd_6724775 : Nat := 3453041868339032020585829

theorem tailTrace_6724775 : CollatzResearch.WordTrace tailWord_6724775 prefixEnd_6724775 3453041868339032020585829 := by
  unfold tailWord_6724775
  simp only [CollatzResearch.WordTrace]
  refine ⟨245272694212296149978343779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163515129474864099985562519 245272694212296149978343779)
  ·
    refine ⟨367909041318444224967515669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245272694212296149978343779 367909041318444224967515669)
    ·
      refine ⟨17245736311802073045352297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 367909041318444224967515669 17245736311802073045352297)
      ·
        refine ⟨12934302233851554784014223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17245736311802073045352297 12934302233851554784014223)
        ·
          refine ⟨19401453350777332176021335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12934302233851554784014223 19401453350777332176021335)
          ·
            refine ⟨29102180026165998264032003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19401453350777332176021335 29102180026165998264032003)
            ·
              refine ⟨43653270039248997396048005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29102180026165998264032003 43653270039248997396048005)
              ·
                refine ⟨8184988132359187011759001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43653270039248997396048005 8184988132359187011759001)
                ·
                  refine ⟨6138741099269390258819251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8184988132359187011759001 6138741099269390258819251)
                  ·
                    refine ⟨9208111648904085388228877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6138741099269390258819251 9208111648904085388228877)
                    ·
                      refine ⟨3453041868339032020585829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9208111648904085388228877 3453041868339032020585829)
                      ·
                        rfl

theorem cell23_6724775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_6724775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724775 prefixEnd_6724775 := by exact prefixLift 6724775
  have htrace : WordTrace (prefixWord ++ tailWord_6724775) baseStart_6724775 baseEnd_6724775 := by
    simpa [prefixWord, tailWord_6724775, baseEnd_6724775] using wordTrace_append hprefix tailTrace_6724775
  have hstable : (prefixWord ++ tailWord_6724775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724775).length < 2 ^ (prefixWord ++ tailWord_6724775).sum := by decide
  have hdescent : baseEnd_6724775 < baseStart_6724775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724831 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 3]
def baseStart_6724831 : Nat := 118140960795 + 6724831 * 2 ^ 59
def prefixEnd_6724831 : Nat := 4983230072969 + 3 ^ 40 * 6724831 * 2
def baseEnd_6724831 : Nat := 3453070623255683801485571

theorem tailTrace_6724831 : CollatzResearch.WordTrace tailWord_6724831 prefixEnd_6724831 3453070623255683801485571 := by
  unfold tailWord_6724831
  simp only [CollatzResearch.WordTrace]
  refine ⟨245274736700093271542382347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163516491133395514361588231 245274736700093271542382347)
  ·
    refine ⟨367912105050139907313573521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245274736700093271542382347 367912105050139907313573521)
    ·
      refine ⟨275934078787604930485180141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367912105050139907313573521 275934078787604930485180141)
      ·
        refine ⟨103475279545351848931942553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275934078787604930485180141 103475279545351848931942553)
        ·
          refine ⟨77606459659013886698956915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103475279545351848931942553 77606459659013886698956915)
          ·
            refine ⟨116409689488520830048435373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77606459659013886698956915 116409689488520830048435373)
            ·
              refine ⟨43653633558195311268163265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116409689488520830048435373 43653633558195311268163265)
              ·
                refine ⟨32740225168646483451122449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43653633558195311268163265 32740225168646483451122449)
                ·
                  refine ⟨24555168876484862588341837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32740225168646483451122449 24555168876484862588341837)
                  ·
                    refine ⟨9208188328681823470628189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24555168876484862588341837 9208188328681823470628189)
                    ·
                      refine ⟨3453070623255683801485571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9208188328681823470628189 3453070623255683801485571)
                      ·
                        rfl

theorem cell23_6724831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_6724831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724831 prefixEnd_6724831 := by exact prefixLift 6724831
  have htrace : WordTrace (prefixWord ++ tailWord_6724831) baseStart_6724831 baseEnd_6724831 := by
    simpa [prefixWord, tailWord_6724831, baseEnd_6724831] using wordTrace_append hprefix tailTrace_6724831
  have hstable : (prefixWord ++ tailWord_6724831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724831).length < 2 ^ (prefixWord ++ tailWord_6724831).sum := by decide
  have hdescent : baseEnd_6724831 < baseStart_6724831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724832 : List Nat := [2, 1, 1, 3, 1, 6, 1, 2, 2, 2, 2]
def baseStart_6724832 : Nat := 118140960795 + 6724832 * 2 ^ 59
def prefixEnd_6724832 : Nat := 4983230072969 + 3 ^ 40 * 6724832 * 2
def baseEnd_6724832 : Nat := 3453071136736338297573067

theorem tailTrace_6724832 : CollatzResearch.WordTrace tailWord_6724832 prefixEnd_6724832 3453071136736338297573067 := by
  unfold tailWord_6724832
  simp only [CollatzResearch.WordTrace]
  refine ⟨122637386586544824356584375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163516515448726432475445833 122637386586544824356584375)
  ·
    refine ⟨183956079879817236534876563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122637386586544824356584375 183956079879817236534876563)
    ·
      refine ⟨275934119819725854802314845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183956079879817236534876563 275934119819725854802314845)
      ·
        refine ⟨103475294932397195550868067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275934119819725854802314845 103475294932397195550868067)
        ·
          refine ⟨155212942398595793326302101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103475294932397195550868067 155212942398595793326302101)
          ·
            refine ⟨7275606674934177812170411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 155212942398595793326302101 7275606674934177812170411)
            ·
              refine ⟨10913410012401266718255617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7275606674934177812170411 10913410012401266718255617)
              ·
                refine ⟨8185057509300950038691713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10913410012401266718255617 8185057509300950038691713)
                ·
                  refine ⟨6138793131975712529018785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8185057509300950038691713 6138793131975712529018785)
                  ·
                    refine ⟨4604094848981784396764089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6138793131975712529018785 4604094848981784396764089)
                    ·
                      refine ⟨3453071136736338297573067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4604094848981784396764089 3453071136736338297573067)
                      ·
                        rfl

theorem cell23_6724832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 2, 2, 2].length) (baseStart_6724832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724832 prefixEnd_6724832 := by exact prefixLift 6724832
  have htrace : WordTrace (prefixWord ++ tailWord_6724832) baseStart_6724832 baseEnd_6724832 := by
    simpa [prefixWord, tailWord_6724832, baseEnd_6724832] using wordTrace_append hprefix tailTrace_6724832
  have hstable : (prefixWord ++ tailWord_6724832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724832).length < 2 ^ (prefixWord ++ tailWord_6724832).sum := by decide
  have hdescent : baseEnd_6724832 < baseStart_6724832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724864 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 1, 10]
def baseStart_6724864 : Nat := 118140960795 + 6724864 * 2 ^ 59
def prefixEnd_6724864 : Nat := 4983230072969 + 3 ^ 40 * 6724864 * 2
def baseEnd_6724864 : Nat := 1151029189372427390790973

theorem tailTrace_6724864 : CollatzResearch.WordTrace tailWord_6724864 prefixEnd_6724864 1151029189372427390790973 := by
  unfold tailWord_6724864
  simp only [CollatzResearch.WordTrace]
  refine ⟨122637970154486859089166823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163517293539315812118889097 122637970154486859089166823)
  ·
    refine ⟨183956955231730288633750235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122637970154486859089166823 183956955231730288633750235)
    ·
      refine ⟨275935432847595432950625353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183956955231730288633750235 275935432847595432950625353)
      ·
        refine ⟨206951574635696574712969015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275935432847595432950625353 206951574635696574712969015)
        ·
          refine ⟨310427361953544862069453523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206951574635696574712969015 310427361953544862069453523)
          ·
            refine ⟨465641042930317293104180285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310427361953544862069453523 465641042930317293104180285)
            ·
              refine ⟨174615391098868984914067607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 465641042930317293104180285 174615391098868984914067607)
              ·
                refine ⟨261923086648303477371101411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174615391098868984914067607 261923086648303477371101411)
                ·
                  refine ⟨392884629972455216056652117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261923086648303477371101411 392884629972455216056652117)
                  ·
                    refine ⟨1151029189372427390790973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 392884629972455216056652117 1151029189372427390790973)
                    ·
                      rfl

theorem cell23_6724864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 10].length) (baseStart_6724864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724864 prefixEnd_6724864 := by exact prefixLift 6724864
  have htrace : WordTrace (prefixWord ++ tailWord_6724864) baseStart_6724864 baseEnd_6724864 := by
    simpa [prefixWord, tailWord_6724864, baseEnd_6724864] using wordTrace_append hprefix tailTrace_6724864
  have hstable : (prefixWord ++ tailWord_6724864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724864).length < 2 ^ (prefixWord ++ tailWord_6724864).sum := by decide
  have hdescent : baseEnd_6724864 < baseStart_6724864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724872 : List Nat := [2, 1, 3, 2, 5, 1, 1, 3, 5]
def baseStart_6724872 : Nat := 118140960795 + 6724872 * 2 ^ 59
def prefixEnd_6724872 : Nat := 4983230072969 + 3 ^ 40 * 6724872 * 2
def baseEnd_6724872 : Nat := 383676852884724237896987

theorem tailTrace_6724872 : CollatzResearch.WordTrace tailWord_6724872 prefixEnd_6724872 383676852884724237896987 := by
  unfold tailWord_6724872
  simp only [CollatzResearch.WordTrace]
  refine ⟨122638116046472367772312435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163517488061963157029749913 122638116046472367772312435)
  ·
    refine ⟨183957174069708551658468653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122638116046472367772312435 183957174069708551658468653)
    ·
      refine ⟨68983940276140706871925745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183957174069708551658468653 68983940276140706871925745)
      ·
        refine ⟨51737955207105530153944309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68983940276140706871925745 51737955207105530153944309)
        ·
          refine ⟨4850433300666143451932279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51737955207105530153944309 4850433300666143451932279)
          ·
            refine ⟨7275649950999215177898419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4850433300666143451932279 7275649950999215177898419)
            ·
              refine ⟨10913474926498822766847629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7275649950999215177898419 10913474926498822766847629)
              ·
                refine ⟨4092553097437058537567861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10913474926498822766847629 4092553097437058537567861)
                ·
                  refine ⟨383676852884724237896987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4092553097437058537567861 383676852884724237896987)
                  ·
                    rfl

theorem cell23_6724872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 5].length) (baseStart_6724872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724872 prefixEnd_6724872 := by exact prefixLift 6724872
  have htrace : WordTrace (prefixWord ++ tailWord_6724872) baseStart_6724872 baseEnd_6724872 := by
    simpa [prefixWord, tailWord_6724872, baseEnd_6724872] using wordTrace_append hprefix tailTrace_6724872
  have hstable : (prefixWord ++ tailWord_6724872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724872).length < 2 ^ (prefixWord ++ tailWord_6724872).sum := by decide
  have hdescent : baseEnd_6724872 < baseStart_6724872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724888 : List Nat := [2, 1, 2, 3, 1, 4, 1, 2, 2, 1, 4]
def baseStart_6724888 : Nat := 118140960795 + 6724888 * 2 ^ 59
def prefixEnd_6724888 : Nat := 4983230072969 + 3 ^ 40 * 6724888 * 2
def baseEnd_6724888 : Nat := 3453099891652990078472809

theorem tailTrace_6724888 : CollatzResearch.WordTrace tailWord_6724888 prefixEnd_6724888 3453099891652990078472809 := by
  unfold tailWord_6724888
  simp only [CollatzResearch.WordTrace]
  refine ⟨122638407830443385138603659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163517877107257846851471545 122638407830443385138603659)
  ·
    refine ⟨183957611745665077707905489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122638407830443385138603659 183957611745665077707905489)
    ·
      refine ⟨137968208809248808280929117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183957611745665077707905489 137968208809248808280929117)
      ·
        refine ⟨51738078303468303105348419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137968208809248808280929117 51738078303468303105348419)
        ·
          refine ⟨77607117455202454658022629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51738078303468303105348419 77607117455202454658022629)
          ·
            refine ⟨14551334522850460248379243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77607117455202454658022629 14551334522850460248379243)
            ·
              refine ⟨21827001784275690372568865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14551334522850460248379243 21827001784275690372568865)
              ·
                refine ⟨16370251338206767779426649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21827001784275690372568865 16370251338206767779426649)
                ·
                  refine ⟨12277688503655075834569987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16370251338206767779426649 12277688503655075834569987)
                  ·
                    refine ⟨18416532755482613751854981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12277688503655075834569987 18416532755482613751854981)
                    ·
                      refine ⟨3453099891652990078472809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18416532755482613751854981 3453099891652990078472809)
                      ·
                        rfl

theorem cell23_6724888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_6724888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724888 prefixEnd_6724888 := by exact prefixLift 6724888
  have htrace : WordTrace (prefixWord ++ tailWord_6724888) baseStart_6724888 baseEnd_6724888 := by
    simpa [prefixWord, tailWord_6724888, baseEnd_6724888] using wordTrace_append hprefix tailTrace_6724888
  have hstable : (prefixWord ++ tailWord_6724888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724888).length < 2 ^ (prefixWord ++ tailWord_6724888).sum := by decide
  have hdescent : baseEnd_6724888 < baseStart_6724888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724949 : List Nat := [1, 3, 2, 2, 3, 3, 2, 2, 1, 4]
def baseStart_6724949 : Nat := 118140960795 + 6724949 * 2 ^ 59
def prefixEnd_6724949 : Nat := 4983230072969 + 3 ^ 40 * 6724949 * 2
def baseEnd_6724949 : Nat := 1151043737990971446603343

theorem tailTrace_6724949 : CollatzResearch.WordTrace tailWord_6724949 prefixEnd_6724949 1151043737990971446603343 := by
  unfold tailWord_6724949
  simp only [CollatzResearch.WordTrace]
  refine ⟨245279040513665777695177901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163519360342443851796785267 245279040513665777695177901)
  ·
    refine ⟨91979640192624666635691713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245279040513665777695177901 91979640192624666635691713)
    ·
      refine ⟨68984730144468499976768785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91979640192624666635691713 68984730144468499976768785)
      ·
        refine ⟨51738547608351374982576589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68984730144468499976768785 51738547608351374982576589)
        ·
          refine ⟨19401955353131765618466221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51738547608351374982576589 19401955353131765618466221)
          ·
            refine ⟨7275733257424412106924833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19401955353131765618466221 7275733257424412106924833)
            ·
              refine ⟨5456799943068309080193625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7275733257424412106924833 5456799943068309080193625)
              ·
                refine ⟨4092599957301231810145219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5456799943068309080193625 4092599957301231810145219)
                ·
                  refine ⟨6138899935951847715217829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4092599957301231810145219 6138899935951847715217829)
                  ·
                    refine ⟨1151043737990971446603343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6138899935951847715217829 1151043737990971446603343)
                    ·
                      rfl

theorem cell23_6724949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_6724949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724949 prefixEnd_6724949 := by exact prefixLift 6724949
  have htrace : WordTrace (prefixWord ++ tailWord_6724949) baseStart_6724949 baseEnd_6724949 := by
    simpa [prefixWord, tailWord_6724949, baseEnd_6724949] using wordTrace_append hprefix tailTrace_6724949
  have hstable : (prefixWord ++ tailWord_6724949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724949).length < 2 ^ (prefixWord ++ tailWord_6724949).sum := by decide
  have hdescent : baseEnd_6724949 < baseStart_6724949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724978 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 3, 1, 4]
def baseStart_6724978 : Nat := 118140960795 + 6724978 * 2 ^ 59
def prefixEnd_6724978 : Nat := 4983230072969 + 3 ^ 40 * 6724978 * 2
def baseEnd_6724978 : Nat := 3453146104911894726347395

theorem tailTrace_6724978 : CollatzResearch.WordTrace tailWord_6724978 prefixEnd_6724978 3453146104911894726347395 := by
  unfold tailWord_6724978
  simp only [CollatzResearch.WordTrace]
  refine ⟨61320024557640178911995897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163520065487040477098655725 61320024557640178911995897)
  ·
    refine ⟨45990018418230134183996923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61320024557640178911995897 45990018418230134183996923)
    ·
      refine ⟨68985027627345201275995385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45990018418230134183996923 68985027627345201275995385)
      ·
        refine ⟨51738770720508900956996539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68985027627345201275995385 51738770720508900956996539)
        ·
          refine ⟨77608156080763351435494809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51738770720508900956996539 77608156080763351435494809)
          ·
            refine ⟨58206117060572513576621107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77608156080763351435494809 58206117060572513576621107)
            ·
              refine ⟨87309175590858770364931661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58206117060572513576621107 87309175590858770364931661)
              ·
                refine ⟨32740940846572038886849373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87309175590858770364931661 32740940846572038886849373)
                ·
                  refine ⟨12277852817464514582568515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32740940846572038886849373 12277852817464514582568515)
                  ·
                    refine ⟨18416779226196771873852773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12277852817464514582568515 18416779226196771873852773)
                    ·
                      refine ⟨3453146104911894726347395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18416779226196771873852773 3453146104911894726347395)
                      ·
                        rfl

theorem cell23_6724978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_6724978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724978 prefixEnd_6724978 := by exact prefixLift 6724978
  have htrace : WordTrace (prefixWord ++ tailWord_6724978) baseStart_6724978 baseEnd_6724978 := by
    simpa [prefixWord, tailWord_6724978, baseEnd_6724978] using wordTrace_append hprefix tailTrace_6724978
  have hstable : (prefixWord ++ tailWord_6724978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724978).length < 2 ^ (prefixWord ++ tailWord_6724978).sum := by decide
  have hdescent : baseEnd_6724978 < baseStart_6724978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724988 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 4, 4]
def baseStart_6724988 : Nat := 118140960795 + 6724988 * 2 ^ 59
def prefixEnd_6724988 : Nat := 4983230072969 + 3 ^ 40 * 6724988 * 2
def baseEnd_6724988 : Nat := 1151050413239479895740783

theorem tailTrace_6724988 : CollatzResearch.WordTrace tailWord_6724988 prefixEnd_6724988 1151050413239479895740783 := by
  unfold tailWord_6724988
  simp only [CollatzResearch.WordTrace]
  refine ⟨122640231480262243677923809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163520308640349658237231745 122640231480262243677923809)
  ·
    refine ⟨91980173610196682758442857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122640231480262243677923809 91980173610196682758442857)
    ·
      refine ⟨68985130207647512068832143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91980173610196682758442857 68985130207647512068832143)
      ·
        refine ⟨103477695311471268103248215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68985130207647512068832143 103477695311471268103248215)
        ·
          refine ⟨155216542967206902154872323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103477695311471268103248215 155216542967206902154872323)
          ·
            refine ⟨232824814450810353232308485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155216542967206902154872323 232824814450810353232308485)
            ·
              refine ⟨43654652709526941231057841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232824814450810353232308485 43654652709526941231057841)
              ·
                refine ⟨32740989532145205923293381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43654652709526941231057841 32740989532145205923293381)
                ·
                  refine ⟨6138935537277226110617509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32740989532145205923293381 6138935537277226110617509)
                  ·
                    refine ⟨1151050413239479895740783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6138935537277226110617509 1151050413239479895740783)
                    ·
                      rfl

theorem cell23_6724988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_6724988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724988 prefixEnd_6724988 := by exact prefixLift 6724988
  have htrace : WordTrace (prefixWord ++ tailWord_6724988) baseStart_6724988 baseEnd_6724988 := by
    simpa [prefixWord, tailWord_6724988, baseEnd_6724988] using wordTrace_append hprefix tailTrace_6724988
  have hstable : (prefixWord ++ tailWord_6724988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724988).length < 2 ^ (prefixWord ++ tailWord_6724988).sum := by decide
  have hdescent : baseEnd_6724988 < baseStart_6724988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6724995 : List Nat := [1, 1, 1, 3, 5, 2, 1, 3, 1, 1, 4]
def baseStart_6724995 : Nat := 118140960795 + 6724995 * 2 ^ 59
def prefixEnd_6724995 : Nat := 4983230072969 + 3 ^ 40 * 6724995 * 2
def baseEnd_6724995 : Nat := 3453154834083021159834817

theorem tailTrace_6724995 : CollatzResearch.WordTrace tailWord_6724995 prefixEnd_6724995 3453154834083021159834817 := by
  unfold tailWord_6724995
  simp only [CollatzResearch.WordTrace]
  refine ⟨245280718271499127551352439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163520478847666085034234959 245280718271499127551352439)
  ·
    refine ⟨367921077407248691327028659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245280718271499127551352439 367921077407248691327028659)
    ·
      refine ⟨551881616110873036990542989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367921077407248691327028659 551881616110873036990542989)
      ·
        refine ⟨206955606041577388871453621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 551881616110873036990542989 206955606041577388871453621)
        ·
          refine ⟨19402088066397880206698777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 206955606041577388871453621 19402088066397880206698777)
          ·
            refine ⟨14551566049798410155024083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19402088066397880206698777 14551566049798410155024083)
            ·
              refine ⟨21827349074697615232536125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14551566049798410155024083 21827349074697615232536125)
              ·
                refine ⟨8185255903011605712201047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21827349074697615232536125 8185255903011605712201047)
                ·
                  refine ⟨12277883854517408568301571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8185255903011605712201047 12277883854517408568301571)
                  ·
                    refine ⟨18416825781776112852452357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12277883854517408568301571 18416825781776112852452357)
                    ·
                      refine ⟨3453154834083021159834817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18416825781776112852452357 3453154834083021159834817)
                      ·
                        rfl

theorem cell23_6724995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 1, 4].length) (baseStart_6724995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6724995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6724995 prefixEnd_6724995 := by exact prefixLift 6724995
  have htrace : WordTrace (prefixWord ++ tailWord_6724995) baseStart_6724995 baseEnd_6724995 := by
    simpa [prefixWord, tailWord_6724995, baseEnd_6724995] using wordTrace_append hprefix tailTrace_6724995
  have hstable : (prefixWord ++ tailWord_6724995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6724995).length < 2 ^ (prefixWord ++ tailWord_6724995).sum := by decide
  have hdescent : baseEnd_6724995 < baseStart_6724995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6724995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725088 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 3]
def baseStart_6725088 : Nat := 118140960795 + 6725088 * 2 ^ 59
def prefixEnd_6725088 : Nat := 4983230072969 + 3 ^ 40 * 6725088 * 2
def baseEnd_6725088 : Nat := 3453202587783889295971889

theorem tailTrace_6725088 : CollatzResearch.WordTrace tailWord_6725088 prefixEnd_6725088 3453202587783889295971889 := by
  unfold tailWord_6725088
  simp only [CollatzResearch.WordTrace]
  refine ⟨122642055130081102217243959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163522740173441469622991945 122642055130081102217243959)
  ·
    refine ⟨183963082695121653325865939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122642055130081102217243959 183963082695121653325865939)
    ·
      refine ⟨275944624042682479988798909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183963082695121653325865939 275944624042682479988798909)
      ·
        refine ⟨103479234016005929995799591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275944624042682479988798909 103479234016005929995799591)
        ·
          refine ⟨155218851024008894993699387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103479234016005929995799591 155218851024008894993699387)
          ·
            refine ⟨232828276536013342490549081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155218851024008894993699387 232828276536013342490549081)
            ·
              refine ⟨174621207402010006867911811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232828276536013342490549081 174621207402010006867911811)
              ·
                refine ⟨261931811103015010301867717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174621207402010006867911811 261931811103015010301867717)
                ·
                  refine ⟨49112214581815314431600197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 261931811103015010301867717 49112214581815314431600197)
                  ·
                    refine ⟨9208540234090371455925037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49112214581815314431600197 9208540234090371455925037)
                    ·
                      refine ⟨3453202587783889295971889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9208540234090371455925037 3453202587783889295971889)
                      ·
                        rfl

theorem cell23_6725088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_6725088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725088 prefixEnd_6725088 := by exact prefixLift 6725088
  have htrace : WordTrace (prefixWord ++ tailWord_6725088) baseStart_6725088 baseEnd_6725088 := by
    simpa [prefixWord, tailWord_6725088, baseEnd_6725088] using wordTrace_append hprefix tailTrace_6725088
  have hstable : (prefixWord ++ tailWord_6725088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725088).length < 2 ^ (prefixWord ++ tailWord_6725088).sum := by decide
  have hdescent : baseEnd_6725088 < baseStart_6725088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725089 : List Nat := [1, 2, 3, 1, 2, 5, 1, 2, 1, 3, 2]
def baseStart_6725089 : Nat := 118140960795 + 6725089 * 2 ^ 59
def prefixEnd_6725089 : Nat := 4983230072969 + 3 ^ 40 * 6725089 * 2
def baseEnd_6725089 : Nat := 3453203101264543792059385

theorem tailTrace_6725089 : CollatzResearch.WordTrace tailWord_6725089 prefixEnd_6725089 3453203101264543792059385 := by
  unfold tailWord_6725089
  simp only [CollatzResearch.WordTrace]
  refine ⟨245284146733158581605274321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163522764488772387736849547 245284146733158581605274321)
  ·
    refine ⟨183963110049868936203955741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245284146733158581605274321 183963110049868936203955741)
    ·
      refine ⟨68986166268700851076483403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183963110049868936203955741 68986166268700851076483403)
      ·
        refine ⟨103479249403051276614725105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68986166268700851076483403 103479249403051276614725105)
        ·
          refine ⟨77609437052288457461043829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103479249403051276614725105 77609437052288457461043829)
          ·
            refine ⟨7275884723652042886972859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77609437052288457461043829 7275884723652042886972859)
            ·
              refine ⟨10913827085478064330459289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7275884723652042886972859 10913827085478064330459289)
              ·
                refine ⟨8185370314108548247844467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10913827085478064330459289 8185370314108548247844467)
                ·
                  refine ⟨12278055471162822371766701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8185370314108548247844467 12278055471162822371766701)
                  ·
                    refine ⟨4604270801686058389412513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12278055471162822371766701 4604270801686058389412513)
                    ·
                      refine ⟨3453203101264543792059385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4604270801686058389412513 3453203101264543792059385)
                      ·
                        rfl

theorem cell23_6725089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 3, 2].length) (baseStart_6725089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725089 prefixEnd_6725089 := by exact prefixLift 6725089
  have htrace : WordTrace (prefixWord ++ tailWord_6725089) baseStart_6725089 baseEnd_6725089 := by
    simpa [prefixWord, tailWord_6725089, baseEnd_6725089] using wordTrace_append hprefix tailTrace_6725089
  have hstable : (prefixWord ++ tailWord_6725089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725089).length < 2 ^ (prefixWord ++ tailWord_6725089).sum := by decide
  have hdescent : baseEnd_6725089 < baseStart_6725089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725102 : List Nat := [4, 1, 2, 1, 2, 1, 3, 2, 1, 4, 2]
def baseStart_6725102 : Nat := 118140960795 + 6725102 * 2 ^ 59
def prefixEnd_6725102 : Nat := 4983230072969 + 3 ^ 40 * 6725102 * 2
def baseEnd_6725102 : Nat := 3453209776513052241196825

theorem tailTrace_6725102 : CollatzResearch.WordTrace tailWord_6725102 prefixEnd_6725102 3453209776513052241196825 := by
  unfold tailWord_6725102
  simp only [CollatzResearch.WordTrace]
  refine ⟨30660577610263935603187195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163523080588074323216998373 30660577610263935603187195)
  ·
    refine ⟨45990866415395903404780793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30660577610263935603187195 45990866415395903404780793)
    ·
      refine ⟨34493149811546927553585595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45990866415395903404780793 34493149811546927553585595)
      ·
        refine ⟨51739724717320391330378393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34493149811546927553585595 51739724717320391330378393)
        ·
          refine ⟨38804793537990293497783795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51739724717320391330378393 38804793537990293497783795)
          ·
            refine ⟨58207190306985440246675693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38804793537990293497783795 58207190306985440246675693)
            ·
              refine ⟨21827696365119540092503385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58207190306985440246675693 21827696365119540092503385)
              ·
                refine ⟨16370772273839655069377539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21827696365119540092503385 16370772273839655069377539)
                ·
                  refine ⟨24556158410759482604066309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16370772273839655069377539 24556158410759482604066309)
                  ·
                    refine ⟨4604279702017402988262433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24556158410759482604066309 4604279702017402988262433)
                    ·
                      refine ⟨3453209776513052241196825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4604279702017402988262433 3453209776513052241196825)
                      ·
                        rfl

theorem cell23_6725102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_6725102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725102 prefixEnd_6725102 := by exact prefixLift 6725102
  have htrace : WordTrace (prefixWord ++ tailWord_6725102) baseStart_6725102 baseEnd_6725102 := by
    simpa [prefixWord, tailWord_6725102, baseEnd_6725102] using wordTrace_append hprefix tailTrace_6725102
  have hstable : (prefixWord ++ tailWord_6725102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725102).length < 2 ^ (prefixWord ++ tailWord_6725102).sum := by decide
  have hdescent : baseEnd_6725102 < baseStart_6725102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725106 : List Nat := [3, 2, 1, 4, 1, 2, 3, 1, 1, 3, 2]
def baseStart_6725106 : Nat := 118140960795 + 6725106 * 2 ^ 59
def prefixEnd_6725106 : Nat := 4983230072969 + 3 ^ 40 * 6725106 * 2
def baseEnd_6725106 : Nat := 3453211830435670225546807

theorem tailTrace_6725106 : CollatzResearch.WordTrace tailWord_6725106 prefixEnd_6725106 3453211830435670225546807 := by
  unfold tailWord_6725106
  simp only [CollatzResearch.WordTrace]
  refine ⟨61321191693524248377160793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163523177849397995672428781 61321191693524248377160793)
  ·
    refine ⟨45990893770143186282870595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61321191693524248377160793 45990893770143186282870595)
    ·
      refine ⟨68986340655214779424305893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45990893770143186282870595 68986340655214779424305893)
      ·
        refine ⟨12934938872852771142057355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68986340655214779424305893 12934938872852771142057355)
        ·
          refine ⟨19402408309279156713086033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12934938872852771142057355 19402408309279156713086033)
          ·
            refine ⟨14551806231959367534814525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19402408309279156713086033 14551806231959367534814525)
            ·
              refine ⟨5456927336984762825555447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14551806231959367534814525 5456927336984762825555447)
              ·
                refine ⟨8185391005477144238333171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5456927336984762825555447 8185391005477144238333171)
                ·
                  refine ⟨12278086508215716357499757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8185391005477144238333171 12278086508215716357499757)
                  ·
                    refine ⟨4604282440580893634062409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12278086508215716357499757 4604282440580893634062409)
                    ·
                      refine ⟨3453211830435670225546807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4604282440580893634062409 3453211830435670225546807)
                      ·
                        rfl

theorem cell23_6725106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_6725106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725106 prefixEnd_6725106 := by exact prefixLift 6725106
  have htrace : WordTrace (prefixWord ++ tailWord_6725106) baseStart_6725106 baseEnd_6725106 := by
    simpa [prefixWord, tailWord_6725106, baseEnd_6725106] using wordTrace_append hprefix tailTrace_6725106
  have hstable : (prefixWord ++ tailWord_6725106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725106).length < 2 ^ (prefixWord ++ tailWord_6725106).sum := by decide
  have hdescent : baseEnd_6725106 < baseStart_6725106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725122 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_6725122 : Nat := 118140960795 + 6725122 * 2 ^ 59
def prefixEnd_6725122 : Nat := 4983230072969 + 3 ^ 40 * 6725122 * 2
def baseEnd_6725122 : Nat := 3453220046126142162946733

theorem tailTrace_6725122 : CollatzResearch.WordTrace tailWord_6725122 prefixEnd_6725122 3453220046126142162946733 := by
  unfold tailWord_6725122
  simp only [CollatzResearch.WordTrace]
  refine ⟨61321337585509757060306405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163523566894692685494150413 61321337585509757060306405)
  ·
    refine ⟨11497750797283079448807451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61321337585509757060306405 11497750797283079448807451)
    ·
      refine ⟨17246626195924619173211177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11497750797283079448807451 17246626195924619173211177)
      ·
        refine ⟨12934969646943464379908383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17246626195924619173211177 12934969646943464379908383)
        ·
          refine ⟨19402454470415196569862575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12934969646943464379908383 19402454470415196569862575)
          ·
            refine ⟨29103681705622794854793863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19402454470415196569862575 29103681705622794854793863)
            ·
              refine ⟨43655522558434192282190795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29103681705622794854793863 43655522558434192282190795)
              ·
                refine ⟨65483283837651288423286193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43655522558434192282190795 65483283837651288423286193)
                ·
                  refine ⟨49112462878238466317464645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65483283837651288423286193 49112462878238466317464645)
                  ·
                    refine ⟨9208586789669712434524621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49112462878238466317464645 9208586789669712434524621)
                    ·
                      refine ⟨3453220046126142162946733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9208586789669712434524621 3453220046126142162946733)
                      ·
                        rfl

theorem cell23_6725122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_6725122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725122 prefixEnd_6725122 := by exact prefixLift 6725122
  have htrace : WordTrace (prefixWord ++ tailWord_6725122) baseStart_6725122 baseEnd_6725122 := by
    simpa [prefixWord, tailWord_6725122, baseEnd_6725122] using wordTrace_append hprefix tailTrace_6725122
  have hstable : (prefixWord ++ tailWord_6725122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725122).length < 2 ^ (prefixWord ++ tailWord_6725122).sum := by decide
  have hdescent : baseEnd_6725122 < baseStart_6725122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725155 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 1, 7]
def baseStart_6725155 : Nat := 118140960795 + 6725155 * 2 ^ 59
def prefixEnd_6725155 : Nat := 4983230072969 + 3 ^ 40 * 6725155 * 2
def baseEnd_6725155 : Nat := 1151078996995913511278027

theorem tailTrace_6725155 : CollatzResearch.WordTrace tailWord_6725155 prefixEnd_6725155 1151078996995913511278027 := by
  unfold tailWord_6725155
  simp only [CollatzResearch.WordTrace]
  refine ⟨245286553950919474877176919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163524369300612983251451279 245286553950919474877176919)
  ·
    refine ⟨367929830926379212315765379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245286553950919474877176919 367929830926379212315765379)
    ·
      refine ⟨551894746389568818473648069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367929830926379212315765379 551894746389568818473648069)
      ·
        refine ⟨103480264948044153463809013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 551894746389568818473648069 103480264948044153463809013)
        ·
          refine ⟨9701274838879139387232095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103480264948044153463809013 9701274838879139387232095)
          ·
            refine ⟨14551912258318709080848143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9701274838879139387232095 14551912258318709080848143)
            ·
              refine ⟨21827868387478063621272215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14551912258318709080848143 21827868387478063621272215)
              ·
                refine ⟨32741802581217095431908323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21827868387478063621272215 32741802581217095431908323)
                ·
                  refine ⟨49112703871825643147862485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32741802581217095431908323 49112703871825643147862485)
                  ·
                    refine ⟨1151078996995913511278027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49112703871825643147862485 1151078996995913511278027)
                    ·
                      rfl

theorem cell23_6725155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 7].length) (baseStart_6725155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725155 prefixEnd_6725155 := by exact prefixLift 6725155
  have htrace : WordTrace (prefixWord ++ tailWord_6725155) baseStart_6725155 baseEnd_6725155 := by
    simpa [prefixWord, tailWord_6725155, baseEnd_6725155] using wordTrace_append hprefix tailTrace_6725155
  have hstable : (prefixWord ++ tailWord_6725155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725155).length < 2 ^ (prefixWord ++ tailWord_6725155).sum := by decide
  have hdescent : baseEnd_6725155 < baseStart_6725155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725202 : List Nat := [3, 2, 2, 1, 2, 2, 2, 2, 3, 4]
def baseStart_6725202 : Nat := 118140960795 + 6725202 * 2 ^ 59
def prefixEnd_6725202 : Nat := 4983230072969 + 3 ^ 40 * 6725202 * 2
def baseEnd_6725202 : Nat := 1151087041526167283315455

theorem tailTrace_6725202 : CollatzResearch.WordTrace tailWord_6725202 prefixEnd_6725202 1151087041526167283315455 := by
  unfold tailWord_6725202
  simp only [CollatzResearch.WordTrace]
  refine ⟨61322067045437300476034465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163525512121166134602758573 61322067045437300476034465)
  ·
    refine ⟨45991550284077975357025849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61322067045437300476034465 45991550284077975357025849)
    ·
      refine ⟨34493662713058481517769387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45991550284077975357025849 34493662713058481517769387)
      ·
        refine ⟨51740494069587722276654081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34493662713058481517769387 51740494069587722276654081)
        ·
          refine ⟨38805370552190791707490561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51740494069587722276654081 38805370552190791707490561)
          ·
            refine ⟨29104027914143093780617921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38805370552190791707490561 29104027914143093780617921)
            ·
              refine ⟨21828020935607320335463441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29104027914143093780617921 21828020935607320335463441)
              ·
                refine ⟨16371015701705490251597581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21828020935607320335463441 16371015701705490251597581)
                ·
                  refine ⟨6139130888139558844349093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16371015701705490251597581 6139130888139558844349093)
                  ·
                    refine ⟨1151087041526167283315455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6139130888139558844349093 1151087041526167283315455)
                    ·
                      rfl

theorem cell23_6725202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_6725202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725202 prefixEnd_6725202 := by exact prefixLift 6725202
  have htrace : WordTrace (prefixWord ++ tailWord_6725202) baseStart_6725202 baseEnd_6725202 := by
    simpa [prefixWord, tailWord_6725202, baseEnd_6725202] using wordTrace_append hprefix tailTrace_6725202
  have hstable : (prefixWord ++ tailWord_6725202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725202).length < 2 ^ (prefixWord ++ tailWord_6725202).sum := by decide
  have hdescent : baseEnd_6725202 < baseStart_6725202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725212 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_6725212 : Nat := 118140960795 + 6725212 * 2 ^ 59
def prefixEnd_6725212 : Nat := 4983230072969 + 3 ^ 40 * 6725212 * 2
def baseEnd_6725212 : Nat := 3453266259385046810821319

theorem tailTrace_6725212 : CollatzResearch.WordTrace tailWord_6725212 prefixEnd_6725212 3453266259385046810821319 := by
  unfold tailWord_6725212
  simp only [CollatzResearch.WordTrace]
  refine ⟨122644316455856486806000945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163525755274475315741334593 122644316455856486806000945)
  ·
    refine ⟨91983237341892365104500709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122644316455856486806000945 91983237341892365104500709)
    ·
      refine ⟨17246857001604818457093883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91983237341892365104500709 17246857001604818457093883)
      ·
        refine ⟨25870285502407227685640825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17246857001604818457093883 25870285502407227685640825)
        ·
          refine ⟨19402714126805420764230619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25870285502407227685640825 19402714126805420764230619)
          ·
            refine ⟨29104071190208131146345929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19402714126805420764230619 29104071190208131146345929)
            ·
              refine ⟨21828053392656098359759447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29104071190208131146345929 21828053392656098359759447)
              ·
                refine ⟨32742080088984147539639171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21828053392656098359759447 32742080088984147539639171)
                ·
                  refine ⟨49113120133476221309458757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32742080088984147539639171 49113120133476221309458757)
                  ·
                    refine ⟨9208710025026791495523517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49113120133476221309458757 9208710025026791495523517)
                    ·
                      refine ⟨3453266259385046810821319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9208710025026791495523517 3453266259385046810821319)
                      ·
                        rfl

theorem cell23_6725212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_6725212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725212 prefixEnd_6725212 := by exact prefixLift 6725212
  have htrace : WordTrace (prefixWord ++ tailWord_6725212) baseStart_6725212 baseEnd_6725212 := by
    simpa [prefixWord, tailWord_6725212, baseEnd_6725212] using wordTrace_append hprefix tailTrace_6725212
  have hstable : (prefixWord ++ tailWord_6725212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725212).length < 2 ^ (prefixWord ++ tailWord_6725212).sum := by decide
  have hdescent : baseEnd_6725212 < baseStart_6725212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725219 : List Nat := [1, 1, 1, 5, 1, 3, 3, 3, 1, 4]
def baseStart_6725219 : Nat := 118140960795 + 6725219 * 2 ^ 59
def prefixEnd_6725219 : Nat := 4983230072969 + 3 ^ 40 * 6725219 * 2
def baseEnd_6725219 : Nat := 1151089951249876094477929

theorem tailTrace_6725219 : CollatzResearch.WordTrace tailWord_6725219 prefixEnd_6725219 1151089951249876094477929 := by
  unfold tailWord_6725219
  simp only [CollatzResearch.WordTrace]
  refine ⟨245288888222687613807506711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163525925481791742538337807 245288888222687613807506711)
  ·
    refine ⟨367933332334031420711260067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245288888222687613807506711 367933332334031420711260067)
    ·
      refine ⟨551899998501047131066890101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367933332334031420711260067 551899998501047131066890101)
      ·
        refine ⟨51740624859473168537520947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 551899998501047131066890101 51740624859473168537520947)
        ·
          refine ⟨77610937289209752806281421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51740624859473168537520947 77610937289209752806281421)
          ·
            refine ⟨29104101483453657302355533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77610937289209752806281421 29104101483453657302355533)
            ·
              refine ⟨10914038056295121488383325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29104101483453657302355533 10914038056295121488383325)
              ·
                refine ⟨4092764271110670558143747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10914038056295121488383325 4092764271110670558143747)
                ·
                  refine ⟨6139146406666005837215621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4092764271110670558143747 6139146406666005837215621)
                  ·
                    refine ⟨1151089951249876094477929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6139146406666005837215621 1151089951249876094477929)
                    ·
                      rfl

theorem cell23_6725219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 1, 4].length) (baseStart_6725219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725219 prefixEnd_6725219 := by exact prefixLift 6725219
  have htrace : WordTrace (prefixWord ++ tailWord_6725219) baseStart_6725219 baseEnd_6725219 := by
    simpa [prefixWord, tailWord_6725219, baseEnd_6725219] using wordTrace_append hprefix tailTrace_6725219
  have hstable : (prefixWord ++ tailWord_6725219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725219).length < 2 ^ (prefixWord ++ tailWord_6725219).sum := by decide
  have hdescent : baseEnd_6725219 < baseStart_6725219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725229 : List Nat := [1, 5, 1, 1, 4, 1, 1, 2, 2, 2, 3]
def baseStart_6725229 : Nat := 118140960795 + 6725229 * 2 ^ 59
def prefixEnd_6725229 : Nat := 4983230072969 + 3 ^ 40 * 6725229 * 2
def baseEnd_6725229 : Nat := 3453274988556173244308741

theorem tailTrace_6725229 : CollatzResearch.WordTrace tailWord_6725229 prefixEnd_6725229 3453274988556173244308741 := by
  unfold tailWord_6725229
  simp only [CollatzResearch.WordTrace]
  refine ⟨245289252952651385515370741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163526168635100923676913827 245289252952651385515370741)
  ·
    refine ⟨22995867464311067392066007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 245289252952651385515370741 22995867464311067392066007)
    ·
      refine ⟨34493801196466601088099011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22995867464311067392066007 34493801196466601088099011)
      ·
        refine ⟨51740701794699901632148517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34493801196466601088099011 51740701794699901632148517)
        ·
          refine ⟨9701381586506231556027847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51740701794699901632148517 9701381586506231556027847)
          ·
            refine ⟨14552072379759347334041771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9701381586506231556027847 14552072379759347334041771)
            ·
              refine ⟨21828108569639021001062657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14552072379759347334041771 21828108569639021001062657)
              ·
                refine ⟨16371081427229265750796993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21828108569639021001062657 16371081427229265750796993)
                ·
                  refine ⟨12278311070421949313097745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16371081427229265750796993 12278311070421949313097745)
                  ·
                    refine ⟨9208733302816461984823309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12278311070421949313097745 9208733302816461984823309)
                    ·
                      refine ⟨3453274988556173244308741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9208733302816461984823309 3453274988556173244308741)
                      ·
                        rfl

theorem cell23_6725229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_6725229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725229 prefixEnd_6725229 := by exact prefixLift 6725229
  have htrace : WordTrace (prefixWord ++ tailWord_6725229) baseStart_6725229 baseEnd_6725229 := by
    simpa [prefixWord, tailWord_6725229, baseEnd_6725229] using wordTrace_append hprefix tailTrace_6725229
  have hstable : (prefixWord ++ tailWord_6725229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725229).length < 2 ^ (prefixWord ++ tailWord_6725229).sum := by decide
  have hdescent : baseEnd_6725229 < baseStart_6725229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725242 : List Nat := [3, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3]
def baseStart_6725242 : Nat := 118140960795 + 6725242 * 2 ^ 59
def prefixEnd_6725242 : Nat := 4983230072969 + 3 ^ 40 * 6725242 * 2
def baseEnd_6725242 : Nat := 3453281663804681693446181

theorem tailTrace_6725242 : CollatzResearch.WordTrace tailWord_6725242 prefixEnd_6725242 3453281663804681693446181 := by
  unfold tailWord_6725242
  simp only [CollatzResearch.WordTrace]
  refine ⟨61322431775401072183898495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163526484734402859157062653 61322431775401072183898495)
  ·
    refine ⟨91983647663101608275847743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61322431775401072183898495 91983647663101608275847743)
    ·
      refine ⟨137975471494652412413771615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91983647663101608275847743 137975471494652412413771615)
      ·
        refine ⟨206963207241978618620657423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137975471494652412413771615 206963207241978618620657423)
        ·
          refine ⟨310444810862967927930986135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206963207241978618620657423 310444810862967927930986135)
          ·
            refine ⟨465667216294451891896479203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310444810862967927930986135 465667216294451891896479203)
            ·
              refine ⟨698500824441677837844718805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465667216294451891896479203 698500824441677837844718805)
              ·
                refine ⟨16371113072851824324485597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 698500824441677837844718805 16371113072851824324485597)
                ·
                  refine ⟨6139167402319434121682099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16371113072851824324485597 6139167402319434121682099)
                  ·
                    refine ⟨9208751103479151182523149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6139167402319434121682099 9208751103479151182523149)
                    ·
                      refine ⟨3453281663804681693446181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9208751103479151182523149 3453281663804681693446181)
                      ·
                        rfl

theorem cell23_6725242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3].length) (baseStart_6725242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725242 prefixEnd_6725242 := by exact prefixLift 6725242
  have htrace : WordTrace (prefixWord ++ tailWord_6725242) baseStart_6725242 baseEnd_6725242 := by
    simpa [prefixWord, tailWord_6725242, baseEnd_6725242] using wordTrace_append hprefix tailTrace_6725242
  have hstable : (prefixWord ++ tailWord_6725242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725242).length < 2 ^ (prefixWord ++ tailWord_6725242).sum := by decide
  have hdescent : baseEnd_6725242 < baseStart_6725242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725249 : List Nat := [1, 2, 4, 2, 1, 4, 2, 1, 6]
def baseStart_6725249 : Nat := 118140960795 + 6725249 * 2 ^ 59
def prefixEnd_6725249 : Nat := 4983230072969 + 3 ^ 40 * 6725249 * 2
def baseEnd_6725249 : Nat := 383698362018807018450961

theorem tailTrace_6725249 : CollatzResearch.WordTrace tailWord_6725249 prefixEnd_6725249 383698362018807018450961 := by
  unfold tailWord_6725249
  simp only [CollatzResearch.WordTrace]
  refine ⟨245289982412578928931098801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163526654941719285954065867 245289982412578928931098801)
  ·
    refine ⟨183967486809434196698324101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245289982412578928931098801 183967486809434196698324101)
    ·
      refine ⟨34493903776768911880935769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183967486809434196698324101 34493903776768911880935769)
      ·
        refine ⟨25870427832576683910701827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34493903776768911880935769 25870427832576683910701827)
        ·
          refine ⟨38805641748865025866052741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25870427832576683910701827 38805641748865025866052741)
          ·
            refine ⟨7276057827912192349884889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38805641748865025866052741 7276057827912192349884889)
            ·
              refine ⟨5457043370934144262413667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7276057827912192349884889 5457043370934144262413667)
              ·
                refine ⟨8185565056401216393620501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5457043370934144262413667 8185565056401216393620501)
                ·
                  refine ⟨383698362018807018450961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8185565056401216393620501 383698362018807018450961)
                  ·
                    rfl

theorem cell23_6725249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 6].length) (baseStart_6725249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725249 prefixEnd_6725249 := by exact prefixLift 6725249
  have htrace : WordTrace (prefixWord ++ tailWord_6725249) baseStart_6725249 baseEnd_6725249 := by
    simpa [prefixWord, tailWord_6725249, baseEnd_6725249] using wordTrace_append hprefix tailTrace_6725249
  have hstable : (prefixWord ++ tailWord_6725249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725249).length < 2 ^ (prefixWord ++ tailWord_6725249).sum := by decide
  have hdescent : baseEnd_6725249 < baseStart_6725249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725262 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 3, 5]
def baseStart_6725262 : Nat := 118140960795 + 6725262 * 2 ^ 59
def prefixEnd_6725262 : Nat := 4983230072969 + 3 ^ 40 * 6725262 * 2
def baseEnd_6725262 : Nat := 1151097311139257205065363

theorem tailTrace_6725262 : CollatzResearch.WordTrace tailWord_6725262 prefixEnd_6725262 1151097311139257205065363 := by
  unfold tailWord_6725262
  simp only [CollatzResearch.WordTrace]
  refine ⟨30661307070191479018915255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163526971041021221434214693 30661307070191479018915255)
  ·
    refine ⟨45991960605287218528372883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30661307070191479018915255 45991960605287218528372883)
    ·
      refine ⟨68987940907930827792559325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45991960605287218528372883 68987940907930827792559325)
      ·
        refine ⟨25870477840474060422209747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68987940907930827792559325 25870477840474060422209747)
        ·
          refine ⟨38805716760711090633314621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25870477840474060422209747 38805716760711090633314621)
          ·
            refine ⟨14552143785266658987492983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38805716760711090633314621 14552143785266658987492983)
            ·
              refine ⟨21828215677899988481239475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14552143785266658987492983 21828215677899988481239475)
              ·
                refine ⟨32742323516849982721859213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21828215677899988481239475 32742323516849982721859213)
                ·
                  refine ⟨12278371318818743520697205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32742323516849982721859213 12278371318818743520697205)
                  ·
                    refine ⟨1151097311139257205065363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12278371318818743520697205 1151097311139257205065363)
                    ·
                      rfl

theorem cell23_6725262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_6725262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725262 prefixEnd_6725262 := by exact prefixLift 6725262
  have htrace : WordTrace (prefixWord ++ tailWord_6725262) baseStart_6725262 baseEnd_6725262 := by
    simpa [prefixWord, tailWord_6725262, baseEnd_6725262] using wordTrace_append hprefix tailTrace_6725262
  have hstable : (prefixWord ++ tailWord_6725262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725262).length < 2 ^ (prefixWord ++ tailWord_6725262).sum := by decide
  have hdescent : baseEnd_6725262 < baseStart_6725262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725295 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 4]
def baseStart_6725295 : Nat := 118140960795 + 6725295 * 2 ^ 59
def prefixEnd_6725295 : Nat := 4983230072969 + 3 ^ 40 * 6725295 * 2
def baseEnd_6725295 : Nat := 3453308878279369986083437

theorem tailTrace_6725295 : CollatzResearch.WordTrace tailWord_6725295 prefixEnd_6725295 3453308878279369986083437 := by
  unfold tailWord_6725295
  simp only [CollatzResearch.WordTrace]
  refine ⟨245291660170412278787273339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163527773446941519191515559 245291660170412278787273339)
  ·
    refine ⟨367937490255618418180910009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245291660170412278787273339 367937490255618418180910009)
    ·
      refine ⟨275953117691713813635682507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367937490255618418180910009 275953117691713813635682507)
      ·
        refine ⟨413929676537570720453523761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275953117691713813635682507 413929676537570720453523761)
        ·
          refine ⟨310447257403178040340142821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413929676537570720453523761 310447257403178040340142821)
          ·
            refine ⟨58208860763095882563776779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 310447257403178040340142821 58208860763095882563776779)
            ·
              refine ⟨87313291144643823845665169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58208860763095882563776779 87313291144643823845665169)
              ·
                refine ⟨65484968358482867884248877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87313291144643823845665169 65484968358482867884248877)
                ·
                  refine ⟨24556863134431075456593329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65484968358482867884248877 24556863134431075456593329)
                  ·
                    refine ⟨18417647350823306592444997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24556863134431075456593329 18417647350823306592444997)
                    ·
                      refine ⟨3453308878279369986083437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18417647350823306592444997 3453308878279369986083437)
                      ·
                        rfl

theorem cell23_6725295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 4].length) (baseStart_6725295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725295 prefixEnd_6725295 := by exact prefixLift 6725295
  have htrace : WordTrace (prefixWord ++ tailWord_6725295) baseStart_6725295 baseEnd_6725295 := by
    simpa [prefixWord, tailWord_6725295, baseEnd_6725295] using wordTrace_append hprefix tailTrace_6725295
  have hstable : (prefixWord ++ tailWord_6725295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725295).length < 2 ^ (prefixWord ++ tailWord_6725295).sum := by decide
  have hdescent : baseEnd_6725295 < baseStart_6725295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725299 : List Nat := [1, 1, 1, 2, 3, 3, 2, 3, 3, 2, 2]
def baseStart_6725299 : Nat := 118140960795 + 6725299 * 2 ^ 59
def prefixEnd_6725299 : Nat := 4983230072969 + 3 ^ 40 * 6725299 * 2
def baseEnd_6725299 : Nat := 3453310932201987970433419

theorem tailTrace_6725299 : CollatzResearch.WordTrace tailWord_6725299 prefixEnd_6725299 3453310932201987970433419 := by
  unfold tailWord_6725299
  simp only [CollatzResearch.WordTrace]
  refine ⟨245291806062397787470418951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163527870708265191646945967 245291806062397787470418951)
  ·
    refine ⟨367937709093596681205628427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245291806062397787470418951 367937709093596681205628427)
    ·
      refine ⟨551906563640395021808442641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367937709093596681205628427 551906563640395021808442641)
      ·
        refine ⟨413929922730296266356331981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 551906563640395021808442641 413929922730296266356331981)
        ·
          refine ⟨155223721023861099883624493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 413929922730296266356331981 155223721023861099883624493)
          ·
            refine ⟨58208895383947912456359185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155223721023861099883624493 58208895383947912456359185)
            ·
              refine ⟨43656671537960934342269389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58208895383947912456359185 43656671537960934342269389)
              ·
                refine ⟨16371251826735350378351021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43656671537960934342269389 16371251826735350378351021)
                ·
                  refine ⟨6139219435025756391881633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16371251826735350378351021 6139219435025756391881633)
                  ·
                    refine ⟨4604414576269317293911225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6139219435025756391881633 4604414576269317293911225)
                    ·
                      refine ⟨3453310932201987970433419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4604414576269317293911225 3453310932201987970433419)
                      ·
                        rfl

theorem cell23_6725299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 2, 2].length) (baseStart_6725299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725299 prefixEnd_6725299 := by exact prefixLift 6725299
  have htrace : WordTrace (prefixWord ++ tailWord_6725299) baseStart_6725299 baseEnd_6725299 := by
    simpa [prefixWord, tailWord_6725299, baseEnd_6725299] using wordTrace_append hprefix tailTrace_6725299
  have hstable : (prefixWord ++ tailWord_6725299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725299).length < 2 ^ (prefixWord ++ tailWord_6725299).sum := by decide
  have hdescent : baseEnd_6725299 < baseStart_6725299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725305 : List Nat := [1, 2, 1, 4, 1, 1, 5, 8]
def baseStart_6725305 : Nat := 118140960795 + 6725305 * 2 ^ 59
def prefixEnd_6725305 : Nat := 4983230072969 + 3 ^ 40 * 6725305 * 2
def baseEnd_6725305 : Nat := 127900519003182035072533

theorem tailTrace_6725305 : CollatzResearch.WordTrace tailWord_6725305 prefixEnd_6725305 127900519003182035072533 := by
  unfold tailWord_6725305
  simp only [CollatzResearch.WordTrace]
  refine ⟨245292024900376050495137369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163528016600250700330091579 245292024900376050495137369)
  ·
    refine ⟨183969018675282037871353027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245292024900376050495137369 183969018675282037871353027)
    ·
      refine ⟨275953528012923056807029541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183969018675282037871353027 275953528012923056807029541)
      ·
        refine ⟨51741286502423073151318039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275953528012923056807029541 51741286502423073151318039)
        ·
          refine ⟨77611929753634609726977059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51741286502423073151318039 77611929753634609726977059)
          ·
            refine ⟨116417894630451914590465589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77611929753634609726977059 116417894630451914590465589)
            ·
              refine ⟨10914177621604866992856149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116417894630451914590465589 10914177621604866992856149)
              ·
                refine ⟨127900519003182035072533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10914177621604866992856149 127900519003182035072533)
                ·
                  rfl

theorem cell23_6725305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 8].length) (baseStart_6725305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725305 prefixEnd_6725305 := by exact prefixLift 6725305
  have htrace : WordTrace (prefixWord ++ tailWord_6725305) baseStart_6725305 baseEnd_6725305 := by
    simpa [prefixWord, tailWord_6725305, baseEnd_6725305] using wordTrace_append hprefix tailTrace_6725305
  have hstable : (prefixWord ++ tailWord_6725305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725305).length < 2 ^ (prefixWord ++ tailWord_6725305).sum := by decide
  have hdescent : baseEnd_6725305 < baseStart_6725305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725312 : List Nat := [2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 4]
def baseStart_6725312 : Nat := 118140960795 + 6725312 * 2 ^ 59
def prefixEnd_6725312 : Nat := 4983230072969 + 3 ^ 40 * 6725312 * 2
def baseEnd_6725312 : Nat := 3453317607450496419570859

theorem tailTrace_6725312 : CollatzResearch.WordTrace tailWord_6725312 prefixEnd_6725312 3453317607450496419570859 := by
  unfold tailWord_6725312
  simp only [CollatzResearch.WordTrace]
  refine ⟨122646140105675345345321095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163528186807567127127094793 122646140105675345345321095)
  ·
    refine ⟨183969210158513018017981643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122646140105675345345321095 183969210158513018017981643)
    ·
      refine ⟨275953815237769527026972465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183969210158513018017981643 275953815237769527026972465)
      ·
        refine ⟨206965361428327145270229349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275953815237769527026972465 206965361428327145270229349)
        ·
          refine ⟨38806005267811339738168003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206965361428327145270229349 38806005267811339738168003)
          ·
            refine ⟨58209007901717009607252005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38806005267811339738168003 58209007901717009607252005)
            ·
              refine ⟨10914188981571939301359751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58209007901717009607252005 10914188981571939301359751)
              ·
                refine ⟨16371283472357908952039627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10914188981571939301359751 16371283472357908952039627)
                ·
                  refine ⟨24556925208536863428059441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16371283472357908952039627 24556925208536863428059441)
                  ·
                    refine ⟨18417693906402647571044581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24556925208536863428059441 18417693906402647571044581)
                    ·
                      refine ⟨3453317607450496419570859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18417693906402647571044581 3453317607450496419570859)
                      ·
                        rfl

theorem cell23_6725312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 4].length) (baseStart_6725312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725312 prefixEnd_6725312 := by exact prefixLift 6725312
  have htrace : WordTrace (prefixWord ++ tailWord_6725312) baseStart_6725312 baseEnd_6725312 := by
    simpa [prefixWord, tailWord_6725312, baseEnd_6725312] using wordTrace_append hprefix tailTrace_6725312
  have hstable : (prefixWord ++ tailWord_6725312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725312).length < 2 ^ (prefixWord ++ tailWord_6725312).sum := by decide
  have hdescent : baseEnd_6725312 < baseStart_6725312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725316 : List Nat := [2, 3, 3, 1, 1, 1, 3, 2, 3, 2, 2]
def baseStart_6725316 : Nat := 118140960795 + 6725316 * 2 ^ 59
def prefixEnd_6725316 : Nat := 4983230072969 + 3 ^ 40 * 6725316 * 2
def baseEnd_6725316 : Nat := 3453319661373114403920841

theorem tailTrace_6725316 : CollatzResearch.WordTrace tailWord_6725316 prefixEnd_6725316 3453319661373114403920841 := by
  unfold tailWord_6725316
  simp only [CollatzResearch.WordTrace]
  refine ⟨122646213051668099686893901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163528284068890799582525201 122646213051668099686893901)
  ·
    refine ⟨45992329894375537382585213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122646213051668099686893901 45992329894375537382585213)
    ·
      refine ⟨17247123710390826518469455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45992329894375537382585213 17247123710390826518469455)
      ·
        refine ⟨25870685565586239777704183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17247123710390826518469455 25870685565586239777704183)
        ·
          refine ⟨38806028348379359666556275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25870685565586239777704183 38806028348379359666556275)
          ·
            refine ⟨58209042522569039499834413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38806028348379359666556275 58209042522569039499834413)
            ·
              refine ⟨21828390945963389812437905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58209042522569039499834413 21828390945963389812437905)
              ·
                refine ⟨16371293209472542359328429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21828390945963389812437905 16371293209472542359328429)
                ·
                  refine ⟨6139234953552203384748161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16371293209472542359328429 6139234953552203384748161)
                  ·
                    refine ⟨4604426215164152538561121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6139234953552203384748161 4604426215164152538561121)
                    ·
                      refine ⟨3453319661373114403920841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4604426215164152538561121 3453319661373114403920841)
                      ·
                        rfl

theorem cell23_6725316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_6725316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725316 prefixEnd_6725316 := by exact prefixLift 6725316
  have htrace : WordTrace (prefixWord ++ tailWord_6725316) baseStart_6725316 baseEnd_6725316 := by
    simpa [prefixWord, tailWord_6725316, baseEnd_6725316] using wordTrace_append hprefix tailTrace_6725316
  have hstable : (prefixWord ++ tailWord_6725316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725316).length < 2 ^ (prefixWord ++ tailWord_6725316).sum := by decide
  have hdescent : baseEnd_6725316 < baseStart_6725316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725349 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 4, 1, 3]
def baseStart_6725349 : Nat := 118140960795 + 6725349 * 2 ^ 59
def prefixEnd_6725349 : Nat := 4983230072969 + 3 ^ 40 * 6725349 * 2
def baseEnd_6725349 : Nat := 3453336606234712774808189

theorem tailTrace_6725349 : CollatzResearch.WordTrace tailWord_6725349 prefixEnd_6725349 3453336606234712774808189 := by
  unfold tailWord_6725349
  simp only [CollatzResearch.WordTrace]
  refine ⟨245293629712216646009739101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163529086474811097339826067 245293629712216646009739101)
  ·
    refine ⟨91985111142081242253652163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245293629712216646009739101 91985111142081242253652163)
    ·
      refine ⟨137977666713121863380478245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91985111142081242253652163 137977666713121863380478245)
      ·
        refine ⟨25870812508710349383839671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137977666713121863380478245 25870812508710349383839671)
        ·
          refine ⟨38806218763065524075759507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25870812508710349383839671 38806218763065524075759507)
          ·
            refine ⟨58209328144598286113639261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38806218763065524075759507 58209328144598286113639261)
            ·
              refine ⟨21828498054224357292614723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58209328144598286113639261 21828498054224357292614723)
              ·
                refine ⟨32742747081336535938922085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21828498054224357292614723 32742747081336535938922085)
                ·
                  refine ⟨6139265077750600488547891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32742747081336535938922085 6139265077750600488547891)
                  ·
                    refine ⟨9208897616625900732821837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6139265077750600488547891 9208897616625900732821837)
                    ·
                      refine ⟨3453336606234712774808189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9208897616625900732821837 3453336606234712774808189)
                      ·
                        rfl

theorem cell23_6725349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_6725349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725349 prefixEnd_6725349 := by exact prefixLift 6725349
  have htrace : WordTrace (prefixWord ++ tailWord_6725349) baseStart_6725349 baseEnd_6725349 := by
    simpa [prefixWord, tailWord_6725349, baseEnd_6725349] using wordTrace_append hprefix tailTrace_6725349
  have hstable : (prefixWord ++ tailWord_6725349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725349).length < 2 ^ (prefixWord ++ tailWord_6725349).sum := by decide
  have hdescent : baseEnd_6725349 < baseStart_6725349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725355 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 4]
def baseStart_6725355 : Nat := 118140960795 + 6725355 * 2 ^ 59
def prefixEnd_6725355 : Nat := 4983230072969 + 3 ^ 40 * 6725355 * 2
def baseEnd_6725355 : Nat := 3453339687118639751333161

theorem tailTrace_6725355 : CollatzResearch.WordTrace tailWord_6725355 prefixEnd_6725355 3453339687118639751333161 := by
  unfold tailWord_6725355
  simp only [CollatzResearch.WordTrace]
  refine ⟨245293848550194909034457519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163529232366796606022971679 245293848550194909034457519)
  ·
    refine ⟨367940772825292363551686279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245293848550194909034457519 367940772825292363551686279)
    ·
      refine ⟨551911159237938545327529419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367940772825292363551686279 551911159237938545327529419)
      ·
        refine ⟨827866738856907817991294129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551911159237938545327529419 827866738856907817991294129)
        ·
          refine ⟨620900054142680863493470597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 827866738856907817991294129 620900054142680863493470597)
          ·
            refine ⟨116418760151752661905025737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 620900054142680863493470597 116418760151752661905025737)
            ·
              refine ⟨87314070113814496428769303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116418760151752661905025737 87314070113814496428769303)
              ·
                refine ⟨130971105170721744643153955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87314070113814496428769303 130971105170721744643153955)
                ·
                  refine ⟨196456657756082616964730933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130971105170721744643153955 196456657756082616964730933)
                  ·
                    refine ⟨18417811664632745340443525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 196456657756082616964730933 18417811664632745340443525)
                    ·
                      refine ⟨3453339687118639751333161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18417811664632745340443525 3453339687118639751333161)
                      ·
                        rfl

theorem cell23_6725355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 4].length) (baseStart_6725355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725355 prefixEnd_6725355 := by exact prefixLift 6725355
  have htrace : WordTrace (prefixWord ++ tailWord_6725355) baseStart_6725355 baseEnd_6725355 := by
    simpa [prefixWord, tailWord_6725355, baseEnd_6725355] using wordTrace_append hprefix tailTrace_6725355
  have hstable : (prefixWord ++ tailWord_6725355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725355).length < 2 ^ (prefixWord ++ tailWord_6725355).sum := by decide
  have hdescent : baseEnd_6725355 < baseStart_6725355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725366 : List Nat := [5, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3]
def baseStart_6725366 : Nat := 118140960795 + 6725366 * 2 ^ 59
def prefixEnd_6725366 : Nat := 4983230072969 + 3 ^ 40 * 6725366 * 2
def baseEnd_6725366 : Nat := 3453345335405839208295611

theorem tailTrace_6725366 : CollatzResearch.WordTrace tailWord_6725366 prefixEnd_6725366 3453345335405839208295611 := by
  unfold tailWord_6725366
  simp only [CollatzResearch.WordTrace]
  refine ⟨15330890609572191119569247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163529499835436705275405301 15330890609572191119569247)
  ·
    refine ⟨22996335914358286679353871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15330890609572191119569247 22996335914358286679353871)
    ·
      refine ⟨34494503871537430019030807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22996335914358286679353871 34494503871537430019030807)
      ·
        refine ⟨51741755807306145028546211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34494503871537430019030807 51741755807306145028546211)
        ·
          refine ⟨77612633710959217542819317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51741755807306145028546211 77612633710959217542819317)
          ·
            refine ⟨7276184410402426644639311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77612633710959217542819317 7276184410402426644639311)
            ·
              refine ⟨10914276615603639966958967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7276184410402426644639311 10914276615603639966958967)
              ·
                refine ⟨16371414923405459950438451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10914276615603639966958967 16371414923405459950438451)
                ·
                  refine ⟨24557122385108189925657677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16371414923405459950438451 24557122385108189925657677)
                  ·
                    refine ⟨9208920894415571222121629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24557122385108189925657677 9208920894415571222121629)
                    ·
                      refine ⟨3453345335405839208295611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9208920894415571222121629 3453345335405839208295611)
                      ·
                        rfl

theorem cell23_6725366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_6725366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725366 prefixEnd_6725366 := by exact prefixLift 6725366
  have htrace : WordTrace (prefixWord ++ tailWord_6725366) baseStart_6725366 baseEnd_6725366 := by
    simpa [prefixWord, tailWord_6725366, baseEnd_6725366] using wordTrace_append hprefix tailTrace_6725366
  have hstable : (prefixWord ++ tailWord_6725366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725366).length < 2 ^ (prefixWord ++ tailWord_6725366).sum := by decide
  have hdescent : baseEnd_6725366 < baseStart_6725366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725463 : List Nat := [1, 1, 3, 2, 5, 2, 2, 2, 5]
def baseStart_6725463 : Nat := 118140960795 + 6725463 * 2 ^ 59
def prefixEnd_6725463 : Nat := 4983230072969 + 3 ^ 40 * 6725463 * 2
def baseEnd_6725463 : Nat := 383710571447702814309185

theorem tailTrace_6725463 : CollatzResearch.WordTrace tailWord_6725463 prefixEnd_6725463 383710571447702814309185 := by
  unfold tailWord_6725463
  simp only [CollatzResearch.WordTrace]
  refine ⟨245297787633803643479389043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163531858422535762319592695 245297787633803643479389043)
  ·
    refine ⟨367946681450705465219083565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245297787633803643479389043 367946681450705465219083565)
    ·
      refine ⟨137980005544014549457156337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 367946681450705465219083565 137980005544014549457156337)
      ·
        refine ⟨103485004158010912092867253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137980005544014549457156337 103485004158010912092867253)
        ·
          refine ⟨9701719139813523008706305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103485004158010912092867253 9701719139813523008706305)
          ·
            refine ⟨7276289354860142256529729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9701719139813523008706305 7276289354860142256529729)
            ·
              refine ⟨5457217016145106692397297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7276289354860142256529729 5457217016145106692397297)
              ·
                refine ⟨4092912762108830019297973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5457217016145106692397297 4092912762108830019297973)
                ·
                  refine ⟨383710571447702814309185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4092912762108830019297973 383710571447702814309185)
                  ·
                    rfl

theorem cell23_6725463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 5].length) (baseStart_6725463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725463 prefixEnd_6725463 := by exact prefixLift 6725463
  have htrace : WordTrace (prefixWord ++ tailWord_6725463) baseStart_6725463 baseEnd_6725463 := by
    simpa [prefixWord, tailWord_6725463, baseEnd_6725463] using wordTrace_append hprefix tailTrace_6725463
  have hstable : (prefixWord ++ tailWord_6725463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725463).length < 2 ^ (prefixWord ++ tailWord_6725463).sum := by decide
  have hdescent : baseEnd_6725463 < baseStart_6725463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725489 : List Nat := [1, 2, 2, 2, 1, 3, 3, 2, 3, 4]
def baseStart_6725489 : Nat := 118140960795 + 6725489 * 2 ^ 59
def prefixEnd_6725489 : Nat := 4983230072969 + 3 ^ 40 * 6725489 * 2
def baseEnd_6725489 : Nat := 1151136164508780742352515

theorem tailTrace_6725489 : CollatzResearch.WordTrace tailWord_6725489 prefixEnd_6725489 1151136164508780742352515 := by
  unfold tailWord_6725489
  simp only [CollatzResearch.WordTrace]
  refine ⟨245298735931709449919835521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163532490621139633279890347 245298735931709449919835521)
  ·
    refine ⟨183974051948782087439876641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245298735931709449919835521 183974051948782087439876641)
    ·
      refine ⟨137980538961586565579907481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183974051948782087439876641 137980538961586565579907481)
      ·
        refine ⟨103485404221189924184930611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137980538961586565579907481 103485404221189924184930611)
        ·
          refine ⟨155228106331784886277395917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103485404221189924184930611 155228106331784886277395917)
          ·
            refine ⟨58210539874419332354023469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155228106331784886277395917 58210539874419332354023469)
            ·
              refine ⟨21828952452907249632758801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58210539874419332354023469 21828952452907249632758801)
              ·
                refine ⟨16371714339680437224569101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21828952452907249632758801 16371714339680437224569101)
                ·
                  refine ⟨6139392877380163959213413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16371714339680437224569101 6139392877380163959213413)
                  ·
                    refine ⟨1151136164508780742352515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6139392877380163959213413 1151136164508780742352515)
                    ·
                      rfl

theorem cell23_6725489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 4].length) (baseStart_6725489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725489 prefixEnd_6725489 := by exact prefixLift 6725489
  have htrace : WordTrace (prefixWord ++ tailWord_6725489) baseStart_6725489 baseEnd_6725489 := by
    simpa [prefixWord, tailWord_6725489, baseEnd_6725489] using wordTrace_append hprefix tailTrace_6725489
  have hstable : (prefixWord ++ tailWord_6725489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725489).length < 2 ^ (prefixWord ++ tailWord_6725489).sum := by decide
  have hdescent : baseEnd_6725489 < baseStart_6725489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725552 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 4]
def baseStart_6725552 : Nat := 118140960795 + 6725552 * 2 ^ 59
def prefixEnd_6725552 : Nat := 4983230072969 + 3 ^ 40 * 6725552 * 2
def baseEnd_6725552 : Nat := 3453440842807575480569755

theorem tailTrace_6725552 : CollatzResearch.WordTrace tailWord_6725552 prefixEnd_6725552 3453440842807575480569755 := by
  unfold tailWord_6725552
  simp only [CollatzResearch.WordTrace]
  refine ⟨122650516865240605839689455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163534022486987474452919273 122650516865240605839689455)
  ·
    refine ⟨183975775297860908759534183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122650516865240605839689455 183975775297860908759534183)
    ·
      refine ⟨275963662946791363139301275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183975775297860908759534183 275963662946791363139301275)
      ·
        refine ⟨413945494420187044708951913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275963662946791363139301275 413945494420187044708951913)
        ·
          refine ⟨310459120815140283531713935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413945494420187044708951913 310459120815140283531713935)
          ·
            refine ⟨465688681222710425297570903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310459120815140283531713935 465688681222710425297570903)
            ·
              refine ⟨698533021834065637946356355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465688681222710425297570903 698533021834065637946356355)
              ·
                refine ⟨1047799532751098456919534533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698533021834065637946356355 1047799532751098456919534533)
                ·
                  refine ⟨196462412390830960672412725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1047799532751098456919534533 196462412390830960672412725)
                  ·
                    refine ⟨18418351161640402563038693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 196462412390830960672412725 18418351161640402563038693)
                    ·
                      refine ⟨3453440842807575480569755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18418351161640402563038693 3453440842807575480569755)
                      ·
                        rfl

theorem cell23_6725552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 4].length) (baseStart_6725552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725552 prefixEnd_6725552 := by exact prefixLift 6725552
  have htrace : WordTrace (prefixWord ++ tailWord_6725552) baseStart_6725552 baseEnd_6725552 := by
    simpa [prefixWord, tailWord_6725552, baseEnd_6725552] using wordTrace_append hprefix tailTrace_6725552
  have hstable : (prefixWord ++ tailWord_6725552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725552).length < 2 ^ (prefixWord ++ tailWord_6725552).sum := by decide
  have hdescent : baseEnd_6725552 < baseStart_6725552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725566 : List Nat := [4, 2, 1, 1, 1, 3, 2, 3, 1, 5]
def baseStart_6725566 : Nat := 118140960795 + 6725566 * 2 ^ 59
def prefixEnd_6725566 : Nat := 4983230072969 + 3 ^ 40 * 6725566 * 2
def baseEnd_6725566 : Nat := 1151149343845579475264897

theorem tailTrace_6725566 : CollatzResearch.WordTrace tailWord_6725566 prefixEnd_6725566 1151149343845579475264897 := by
  unfold tailWord_6725566
  simp only [CollatzResearch.WordTrace]
  refine ⟨30662693044053811508798569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163534362901620328046925701 30662693044053811508798569)
  ·
    refine ⟨22997019783040358631598927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30662693044053811508798569 22997019783040358631598927)
    ·
      refine ⟨34495529674560537947398391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22997019783040358631598927 34495529674560537947398391)
      ·
        refine ⟨51743294511840806921097587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34495529674560537947398391 51743294511840806921097587)
        ·
          refine ⟨77614941767761210381646381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51743294511840806921097587 77614941767761210381646381)
          ·
            refine ⟨29105603162910453893117393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77614941767761210381646381 29105603162910453893117393)
            ·
              refine ⟨21829202372182840419838045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29105603162910453893117393 21829202372182840419838045)
              ·
                refine ⟨8185950889568565157439267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21829202372182840419838045 8185950889568565157439267)
                ·
                  refine ⟨12278926334352847736158901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8185950889568565157439267 12278926334352847736158901)
                  ·
                    refine ⟨1151149343845579475264897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12278926334352847736158901 1151149343845579475264897)
                    ·
                      rfl

theorem cell23_6725566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_6725566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725566 prefixEnd_6725566 := by exact prefixLift 6725566
  have htrace : WordTrace (prefixWord ++ tailWord_6725566) baseStart_6725566 baseEnd_6725566 := by
    simpa [prefixWord, tailWord_6725566, baseEnd_6725566] using wordTrace_append hprefix tailTrace_6725566
  have hstable : (prefixWord ++ tailWord_6725566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725566).length < 2 ^ (prefixWord ++ tailWord_6725566).sum := by decide
  have hdescent : baseEnd_6725566 < baseStart_6725566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725579 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 4, 4]
def baseStart_6725579 : Nat := 118140960795 + 6725579 * 2 ^ 59
def prefixEnd_6725579 : Nat := 4983230072969 + 3 ^ 40 * 6725579 * 2
def baseEnd_6725579 : Nat := 1151151568928415624977377

theorem tailTrace_6725579 : CollatzResearch.WordTrace tailWord_6725579 prefixEnd_6725579 1151151568928415624977377 := by
  unfold tailWord_6725579
  simp only [CollatzResearch.WordTrace]
  refine ⟨245302018501383395290611791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163534679000922263527074527 245302018501383395290611791)
  ·
    refine ⟨367953027752075092935917687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245302018501383395290611791 367953027752075092935917687)
    ·
      refine ⟨551929541628112639403876531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367953027752075092935917687 551929541628112639403876531)
      ·
        refine ⟨827894312442168959105814797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551929541628112639403876531 827894312442168959105814797)
        ·
          refine ⟨310460367165813359664680549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 827894312442168959105814797 310460367165813359664680549)
          ·
            refine ⟨58211318843590004937127603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 310460367165813359664680549 58211318843590004937127603)
            ·
              refine ⟨87316978265385007405691405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58211318843590004937127603 87316978265385007405691405)
              ·
                refine ⟨32743866849519377777134277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87316978265385007405691405 32743866849519377777134277)
                ·
                  refine ⟨6139475034284883333212677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32743866849519377777134277 6139475034284883333212677)
                  ·
                    refine ⟨1151151568928415624977377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6139475034284883333212677 1151151568928415624977377)
                    ·
                      rfl

theorem cell23_6725579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 4].length) (baseStart_6725579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725579 prefixEnd_6725579 := by exact prefixLift 6725579
  have htrace : WordTrace (prefixWord ++ tailWord_6725579) baseStart_6725579 baseEnd_6725579 := by
    simpa [prefixWord, tailWord_6725579, baseEnd_6725579] using wordTrace_append hprefix tailTrace_6725579
  have hstable : (prefixWord ++ tailWord_6725579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725579).length < 2 ^ (prefixWord ++ tailWord_6725579).sum := by decide
  have hdescent : baseEnd_6725579 < baseStart_6725579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725599 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 6]
def baseStart_6725599 : Nat := 118140960795 + 6725599 * 2 ^ 59
def prefixEnd_6725599 : Nat := 4983230072969 + 3 ^ 40 * 6725599 * 2
def baseEnd_6725599 : Nat := 3453464976398336796682039

theorem tailTrace_6725599 : CollatzResearch.WordTrace tailWord_6725599 prefixEnd_6725599 3453464976398336796682039 := by
  unfold tailWord_6725599
  simp only [CollatzResearch.WordTrace]
  refine ⟨245302747961310938706339851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163535165307540625804226567 245302747961310938706339851)
  ·
    refine ⟨367954121941966408059509777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245302747961310938706339851 367954121941966408059509777)
    ·
      refine ⟨275965591456474806044632333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367954121941966408059509777 275965591456474806044632333)
      ·
        refine ⟨103487096796178052266737125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275965591456474806044632333 103487096796178052266737125)
        ·
          refine ⟨19403830649283384800013211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103487096796178052266737125 19403830649283384800013211)
          ·
            refine ⟨29105745973925077200019817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19403830649283384800013211 29105745973925077200019817)
            ·
              refine ⟨21829309480443807900014863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29105745973925077200019817 21829309480443807900014863)
              ·
                refine ⟨32743964220665711850022295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21829309480443807900014863 32743964220665711850022295)
                ·
                  refine ⟨49115946330998567775033443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32743964220665711850022295 49115946330998567775033443)
                  ·
                    refine ⟨73673919496497851662550165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49115946330998567775033443 73673919496497851662550165)
                    ·
                      refine ⟨3453464976398336796682039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73673919496497851662550165 3453464976398336796682039)
                      ·
                        rfl

theorem cell23_6725599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_6725599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725599 prefixEnd_6725599 := by exact prefixLift 6725599
  have htrace : WordTrace (prefixWord ++ tailWord_6725599) baseStart_6725599 baseEnd_6725599 := by
    simpa [prefixWord, tailWord_6725599, baseEnd_6725599] using wordTrace_append hprefix tailTrace_6725599
  have hstable : (prefixWord ++ tailWord_6725599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725599).length < 2 ^ (prefixWord ++ tailWord_6725599).sum := by decide
  have hdescent : baseEnd_6725599 < baseStart_6725599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725603 : List Nat := [1, 1, 1, 6, 1, 4, 1, 2, 1, 1, 4]
def baseStart_6725603 : Nat := 118140960795 + 6725603 * 2 ^ 59
def prefixEnd_6725603 : Nat := 4983230072969 + 3 ^ 40 * 6725603 * 2
def baseEnd_6725603 : Nat := 3453467030320954781032021

theorem tailTrace_6725603 : CollatzResearch.WordTrace tailWord_6725603 prefixEnd_6725603 3453467030320954781032021 := by
  unfold tailWord_6725603
  simp only [CollatzResearch.WordTrace]
  refine ⟨245302893853296447389485463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163535262568864298259656975 245302893853296447389485463)
  ·
    refine ⟨367954340779944671084228195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245302893853296447389485463 367954340779944671084228195)
    ·
      refine ⟨551931511169917006626342293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367954340779944671084228195 551931511169917006626342293)
      ·
        refine ⟨25871789586089859685609795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 551931511169917006626342293 25871789586089859685609795)
        ·
          refine ⟨38807684379134789528414693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25871789586089859685609795 38807684379134789528414693)
          ·
            refine ⟨7276440821087773036577755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38807684379134789528414693 7276440821087773036577755)
            ·
              refine ⟨10914661231631659554866633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7276440821087773036577755 10914661231631659554866633)
              ·
                refine ⟨8185995923723744666149975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10914661231631659554866633 8185995923723744666149975)
                ·
                  refine ⟨12278993885585616999224963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8185995923723744666149975 12278993885585616999224963)
                  ·
                    refine ⟨18418490828378425498837445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12278993885585616999224963 18418490828378425498837445)
                    ·
                      refine ⟨3453467030320954781032021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18418490828378425498837445 3453467030320954781032021)
                      ·
                        rfl

theorem cell23_6725603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_6725603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725603 prefixEnd_6725603 := by exact prefixLift 6725603
  have htrace : WordTrace (prefixWord ++ tailWord_6725603) baseStart_6725603 baseEnd_6725603 := by
    simpa [prefixWord, tailWord_6725603, baseEnd_6725603] using wordTrace_append hprefix tailTrace_6725603
  have hstable : (prefixWord ++ tailWord_6725603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725603).length < 2 ^ (prefixWord ++ tailWord_6725603).sum := by decide
  have hdescent : baseEnd_6725603 < baseStart_6725603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725613 : List Nat := [1, 5, 1, 4, 1, 1, 1, 2, 1, 6]
def baseStart_6725613 : Nat := 118140960795 + 6725613 * 2 ^ 59
def prefixEnd_6725613 : Nat := 4983230072969 + 3 ^ 40 * 6725613 * 2
def baseEnd_6725613 : Nat := 1151157388375833247302325

theorem tailTrace_6725613 : CollatzResearch.WordTrace tailWord_6725613 prefixEnd_6725613 1151157388375833247302325 := by
  unfold tailWord_6725613
  simp only [CollatzResearch.WordTrace]
  refine ⟨245303258583260219097349493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163535505722173479398232995 245303258583260219097349493)
  ·
    refine ⟨22997180492180645540376515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 245303258583260219097349493 22997180492180645540376515)
    ·
      refine ⟨34495770738270968310564773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22997180492180645540376515 34495770738270968310564773)
      ·
        refine ⟨6467957013425806558230895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34495770738270968310564773 6467957013425806558230895)
        ·
          refine ⟨9701935520138709837346343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6467957013425806558230895 9701935520138709837346343)
          ·
            refine ⟨14552903280208064756019515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9701935520138709837346343 14552903280208064756019515)
            ·
              refine ⟨21829354920312097134029273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14552903280208064756019515 21829354920312097134029273)
              ·
                refine ⟨16372016190234072850521955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21829354920312097134029273 16372016190234072850521955)
                ·
                  refine ⟨24558024285351109275782933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16372016190234072850521955 24558024285351109275782933)
                  ·
                    refine ⟨1151157388375833247302325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24558024285351109275782933 1151157388375833247302325)
                    ·
                      rfl

theorem cell23_6725613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_6725613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725613 prefixEnd_6725613 := by exact prefixLift 6725613
  have htrace : WordTrace (prefixWord ++ tailWord_6725613) baseStart_6725613 baseEnd_6725613 := by
    simpa [prefixWord, tailWord_6725613, baseEnd_6725613] using wordTrace_append hprefix tailTrace_6725613
  have hstable : (prefixWord ++ tailWord_6725613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725613).length < 2 ^ (prefixWord ++ tailWord_6725613).sum := by decide
  have hdescent : baseEnd_6725613 < baseStart_6725613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725630 : List Nat := [4, 2, 2, 2, 1, 2, 2, 2, 2, 4]
def baseStart_6725630 : Nat := 118140960795 + 6725630 * 2 ^ 59
def prefixEnd_6725630 : Nat := 4983230072969 + 3 ^ 40 * 6725630 * 2
def baseEnd_6725630 : Nat := 1151160298099542058464799

theorem tailTrace_6725630 : CollatzResearch.WordTrace tailWord_6725630 prefixEnd_6725630 1151160298099542058464799 := by
  unfold tailWord_6725630
  simp only [CollatzResearch.WordTrace]
  refine ⟨30662984828024828875089793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163535919082799087333812229 30662984828024828875089793)
  ·
    refine ⟨22997238621018621656317345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30662984828024828875089793 22997238621018621656317345)
    ·
      refine ⟨17247928965763966242238009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22997238621018621656317345 17247928965763966242238009)
      ·
        refine ⟨12935946724322974681678507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17247928965763966242238009 12935946724322974681678507)
        ·
          refine ⟨19403920086484462022517761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12935946724322974681678507 19403920086484462022517761)
          ·
            refine ⟨14552940064863346516888321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19403920086484462022517761 14552940064863346516888321)
            ·
              refine ⟨10914705048647509887666241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14552940064863346516888321 10914705048647509887666241)
              ·
                refine ⟨8186028786485632415749681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10914705048647509887666241 8186028786485632415749681)
                ·
                  refine ⟨6139521589864224311812261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8186028786485632415749681 6139521589864224311812261)
                  ·
                    refine ⟨1151160298099542058464799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6139521589864224311812261 1151160298099542058464799)
                    ·
                      rfl

theorem cell23_6725630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_6725630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725630 prefixEnd_6725630 := by exact prefixLift 6725630
  have htrace : WordTrace (prefixWord ++ tailWord_6725630) baseStart_6725630 baseEnd_6725630 := by
    simpa [prefixWord, tailWord_6725630, baseEnd_6725630] using wordTrace_append hprefix tailTrace_6725630
  have hstable : (prefixWord ++ tailWord_6725630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725630).length < 2 ^ (prefixWord ++ tailWord_6725630).sum := by decide
  have hdescent : baseEnd_6725630 < baseStart_6725630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725637 : List Nat := [1, 3, 1, 1, 2, 4, 4, 2, 1, 2, 2]
def baseStart_6725637 : Nat := 118140960795 + 6725637 * 2 ^ 59
def prefixEnd_6725637 : Nat := 4983230072969 + 3 ^ 40 * 6725637 * 2
def baseEnd_6725637 : Nat := 3453484488663207648006865

theorem tailTrace_6725637 : CollatzResearch.WordTrace tailWord_6725637 prefixEnd_6725637 3453484488663207648006865 := by
  unfold tailWord_6725637
  simp only [CollatzResearch.WordTrace]
  refine ⟨245304133935173271196223165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163536089290115514130815443 245304133935173271196223165)
  ·
    refine ⟨91989050225689976698583687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245304133935173271196223165 91989050225689976698583687)
    ·
      refine ⟨137983575338534965047875531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91989050225689976698583687 137983575338534965047875531)
      ·
        refine ⟨206975363007802447571813297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137983575338534965047875531 206975363007802447571813297)
        ·
          refine ⟨155231522255851835678859973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206975363007802447571813297 155231522255851835678859973)
          ·
            refine ⟨29105910422972219189786245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155231522255851835678859973 29105910422972219189786245)
            ·
              refine ⟨5457358204307291098084921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29105910422972219189786245 5457358204307291098084921)
              ·
                refine ⟨4093018653230468323563691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5457358204307291098084921 4093018653230468323563691)
                ·
                  refine ⟨6139527979845702485345537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4093018653230468323563691 6139527979845702485345537)
                  ·
                    refine ⟨4604645984884276864009153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6139527979845702485345537 4604645984884276864009153)
                    ·
                      refine ⟨3453484488663207648006865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4604645984884276864009153 3453484488663207648006865)
                      ·
                        rfl

theorem cell23_6725637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 1, 2, 2].length) (baseStart_6725637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725637 prefixEnd_6725637 := by exact prefixLift 6725637
  have htrace : WordTrace (prefixWord ++ tailWord_6725637) baseStart_6725637 baseEnd_6725637 := by
    simpa [prefixWord, tailWord_6725637, baseEnd_6725637] using wordTrace_append hprefix tailTrace_6725637
  have hstable : (prefixWord ++ tailWord_6725637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725637).length < 2 ^ (prefixWord ++ tailWord_6725637).sum := by decide
  have hdescent : baseEnd_6725637 < baseStart_6725637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725639 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 2, 7]
def baseStart_6725639 : Nat := 118140960795 + 6725639 * 2 ^ 59
def prefixEnd_6725639 : Nat := 4983230072969 + 3 ^ 40 * 6725639 * 2
def baseEnd_6725639 : Nat := 1151161838541505546727285

theorem tailTrace_6725639 : CollatzResearch.WordTrace tailWord_6725639 prefixEnd_6725639 1151161838541505546727285 := by
  unfold tailWord_6725639
  simp only [CollatzResearch.WordTrace]
  refine ⟨245304206881166025537795971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163536137920777350358530647 245304206881166025537795971)
  ·
    refine ⟨367956310321749038306693957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245304206881166025537795971 367956310321749038306693957)
    ·
      refine ⟨68991808185327944682505117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 367956310321749038306693957 68991808185327944682505117)
      ·
        refine ⟨25871928069497979255939419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68991808185327944682505117 25871928069497979255939419)
        ·
          refine ⟨38807892104246968883909129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25871928069497979255939419 38807892104246968883909129)
          ·
            refine ⟨29105919078185226662931847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38807892104246968883909129 29105919078185226662931847)
            ·
              refine ⟨43658878617277839994397771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29105919078185226662931847 43658878617277839994397771)
              ·
                refine ⟨65488317925916759991596657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43658878617277839994397771 65488317925916759991596657)
                ·
                  refine ⟨49116238444437569993697493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65488317925916759991596657 49116238444437569993697493)
                  ·
                    refine ⟨1151161838541505546727285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49116238444437569993697493 1151161838541505546727285)
                    ·
                      rfl

theorem cell23_6725639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_6725639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725639 prefixEnd_6725639 := by exact prefixLift 6725639
  have htrace : WordTrace (prefixWord ++ tailWord_6725639) baseStart_6725639 baseEnd_6725639 := by
    simpa [prefixWord, tailWord_6725639, baseEnd_6725639] using wordTrace_append hprefix tailTrace_6725639
  have hstable : (prefixWord ++ tailWord_6725639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725639).length < 2 ^ (prefixWord ++ tailWord_6725639).sum := by decide
  have hdescent : baseEnd_6725639 < baseStart_6725639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725653 : List Nat := [1, 3, 2, 1, 5, 1, 2, 1, 1, 3, 3]
def baseStart_6725653 : Nat := 118140960795 + 6725653 * 2 ^ 59
def prefixEnd_6725653 : Nat := 4983230072969 + 3 ^ 40 * 6725653 * 2
def baseEnd_6725653 : Nat := 3453492704353679585406791

theorem tailTrace_6725653 : CollatzResearch.WordTrace tailWord_6725653 prefixEnd_6725653 3453492704353679585406791 := by
  unfold tailWord_6725653
  simp only [CollatzResearch.WordTrace]
  refine ⟨245304717503115305928805613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163536478335410203952537075 245304717503115305928805613)
  ·
    refine ⟨91989269063668239723302105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245304717503115305928805613 91989269063668239723302105)
    ·
      refine ⟨68991951797751179792476579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91989269063668239723302105 68991951797751179792476579)
      ·
        refine ⟨103487927696626769688714869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68991951797751179792476579 103487927696626769688714869)
        ·
          refine ⟨9701993221558759658317019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103487927696626769688714869 9701993221558759658317019)
          ·
            refine ⟨14552989832338139487475529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9701993221558759658317019 14552989832338139487475529)
            ·
              refine ⟨10914742374253604615606647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14552989832338139487475529 10914742374253604615606647)
              ·
                refine ⟨16372113561380406923409971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10914742374253604615606647 16372113561380406923409971)
                ·
                  refine ⟨24558170342070610385114957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16372113561380406923409971 24558170342070610385114957)
                  ·
                    refine ⟨9209313878276478894418109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24558170342070610385114957 9209313878276478894418109)
                    ·
                      refine ⟨3453492704353679585406791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9209313878276478894418109 3453492704353679585406791)
                      ·
                        rfl

theorem cell23_6725653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_6725653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725653 prefixEnd_6725653 := by exact prefixLift 6725653
  have htrace : WordTrace (prefixWord ++ tailWord_6725653) baseStart_6725653 baseEnd_6725653 := by
    simpa [prefixWord, tailWord_6725653, baseEnd_6725653] using wordTrace_append hprefix tailTrace_6725653
  have hstable : (prefixWord ++ tailWord_6725653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725653).length < 2 ^ (prefixWord ++ tailWord_6725653).sum := by decide
  have hdescent : baseEnd_6725653 < baseStart_6725653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725663 : List Nat := [1, 1, 2, 4, 1, 2, 2, 4, 1, 3, 2]
def baseStart_6725663 : Nat := 118140960795 + 6725663 * 2 ^ 59
def prefixEnd_6725663 : Nat := 4983230072969 + 3 ^ 40 * 6725663 * 2
def baseEnd_6725663 : Nat := 3453497839160224546281745

theorem tailTrace_6725663 : CollatzResearch.WordTrace tailWord_6725663 prefixEnd_6725663 3453497839160224546281745 := by
  unfold tailWord_6725663
  simp only [CollatzResearch.WordTrace]
  refine ⟨245305082233079077636669643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163536721488719385091113095 245305082233079077636669643)
  ·
    refine ⟨367957623349618616455004465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245305082233079077636669643 367957623349618616455004465)
    ·
      refine ⟨275968217512213962341253349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367957623349618616455004465 275968217512213962341253349)
      ·
        refine ⟨51744040783540117938985003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275968217512213962341253349 51744040783540117938985003)
        ·
          refine ⟨77616061175310176908477505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51744040783540117938985003 77616061175310176908477505)
          ·
            refine ⟨58212045881482632681358129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77616061175310176908477505 58212045881482632681358129)
            ·
              refine ⟨43659034411111974511018597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58212045881482632681358129 43659034411111974511018597)
              ·
                refine ⟨8186068952083495220815987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43659034411111974511018597 8186068952083495220815987)
                ·
                  refine ⟨12279103428125242831223981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8186068952083495220815987 12279103428125242831223981)
                  ·
                    refine ⟨4604663785546966061708993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12279103428125242831223981 4604663785546966061708993)
                    ·
                      refine ⟨3453497839160224546281745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4604663785546966061708993 3453497839160224546281745)
                      ·
                        rfl

theorem cell23_6725663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_6725663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725663 prefixEnd_6725663 := by exact prefixLift 6725663
  have htrace : WordTrace (prefixWord ++ tailWord_6725663) baseStart_6725663 baseEnd_6725663 := by
    simpa [prefixWord, tailWord_6725663, baseEnd_6725663] using wordTrace_append hprefix tailTrace_6725663
  have hstable : (prefixWord ++ tailWord_6725663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725663).length < 2 ^ (prefixWord ++ tailWord_6725663).sum := by decide
  have hdescent : baseEnd_6725663 < baseStart_6725663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725676 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 3, 4, 2]
def baseStart_6725676 : Nat := 118140960795 + 6725676 * 2 ^ 59
def prefixEnd_6725676 : Nat := 4983230072969 + 3 ^ 40 * 6725676 * 2
def baseEnd_6725676 : Nat := 3453504514408732995419185

theorem tailTrace_6725676 : CollatzResearch.WordTrace tailWord_6725676 prefixEnd_6725676 3453504514408732995419185 := by
  unfold tailWord_6725676
  simp only [CollatzResearch.WordTrace]
  refine ⟨122652778191015990428446441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163537037588021320571261921 122652778191015990428446441)
  ·
    refine ⟨91989583643261992821334831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122652778191015990428446441 91989583643261992821334831)
    ·
      refine ⟨137984375464892989232002247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91989583643261992821334831 137984375464892989232002247)
      ·
        refine ⟨206976563197339483848003371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137984375464892989232002247 206976563197339483848003371)
        ·
          refine ⟨310464844796009225772005057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206976563197339483848003371 310464844796009225772005057)
          ·
            refine ⟨232848633597006919329003793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310464844796009225772005057 232848633597006919329003793)
            ·
              refine ⟨174636475197755189496752845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232848633597006919329003793 174636475197755189496752845)
              ·
                refine ⟨65488678199158196061282317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174636475197755189496752845 65488678199158196061282317)
                ·
                  refine ⟨24558254324684323522980869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65488678199158196061282317 24558254324684323522980869)
                  ·
                    refine ⟨4604672685878310660558913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24558254324684323522980869 4604672685878310660558913)
                    ·
                      refine ⟨3453504514408732995419185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4604672685878310660558913 3453504514408732995419185)
                      ·
                        rfl

theorem cell23_6725676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 4, 2].length) (baseStart_6725676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725676 prefixEnd_6725676 := by exact prefixLift 6725676
  have htrace : WordTrace (prefixWord ++ tailWord_6725676) baseStart_6725676 baseEnd_6725676 := by
    simpa [prefixWord, tailWord_6725676, baseEnd_6725676] using wordTrace_append hprefix tailTrace_6725676
  have hstable : (prefixWord ++ tailWord_6725676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725676).length < 2 ^ (prefixWord ++ tailWord_6725676).sum := by decide
  have hdescent : baseEnd_6725676 < baseStart_6725676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725679 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 3]
def baseStart_6725679 : Nat := 118140960795 + 6725679 * 2 ^ 59
def prefixEnd_6725679 : Nat := 4983230072969 + 3 ^ 40 * 6725679 * 2
def baseEnd_6725679 : Nat := 3453506054850696483681671

theorem tailTrace_6725679 : CollatzResearch.WordTrace tailWord_6725679 prefixEnd_6725679 3453506054850696483681671 := by
  unfold tailWord_6725679
  simp only [CollatzResearch.WordTrace]
  refine ⟨245305665801021112369252091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163537110534014074912834727 245305665801021112369252091)
  ·
    refine ⟨367958498701531668553878137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245305665801021112369252091 367958498701531668553878137)
    ·
      refine ⟨275968874026148751415408603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367958498701531668553878137 275968874026148751415408603)
      ·
        refine ⟨413953311039223127123112905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275968874026148751415408603 413953311039223127123112905)
        ·
          refine ⟨310464983279417345342334679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413953311039223127123112905 310464983279417345342334679)
          ·
            refine ⟨465697474919126018013502019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310464983279417345342334679 465697474919126018013502019)
            ·
              refine ⟨698546212378689027020253029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465697474919126018013502019 698546212378689027020253029)
              ·
                refine ⟨130977414821004192566297443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 698546212378689027020253029 130977414821004192566297443)
                ·
                  refine ⟨196466122231506288849446165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130977414821004192566297443 196466122231506288849446165)
                  ·
                    refine ⟨9209349479601857289817789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 196466122231506288849446165 9209349479601857289817789)
                    ·
                      refine ⟨3453506054850696483681671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9209349479601857289817789 3453506054850696483681671)
                      ·
                        rfl

theorem cell23_6725679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 3].length) (baseStart_6725679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725679 prefixEnd_6725679 := by exact prefixLift 6725679
  have htrace : WordTrace (prefixWord ++ tailWord_6725679) baseStart_6725679 baseEnd_6725679 := by
    simpa [prefixWord, tailWord_6725679, baseEnd_6725679] using wordTrace_append hprefix tailTrace_6725679
  have hstable : (prefixWord ++ tailWord_6725679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725679).length < 2 ^ (prefixWord ++ tailWord_6725679).sum := by decide
  have hdescent : baseEnd_6725679 < baseStart_6725679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725680 : List Nat := [2, 1, 1, 1, 2, 5, 4, 1, 1, 3, 2]
def baseStart_6725680 : Nat := 118140960795 + 6725680 * 2 ^ 59
def prefixEnd_6725680 : Nat := 4983230072969 + 3 ^ 40 * 6725680 * 2
def baseEnd_6725680 : Nat := 3453506568331350979769167

theorem tailTrace_6725680 : CollatzResearch.WordTrace tailWord_6725680 prefixEnd_6725680 3453506568331350979769167 := by
  unfold tailWord_6725680
  simp only [CollatzResearch.WordTrace]
  refine ⟨122652851137008744770019247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163537134849344993026692329 122652851137008744770019247)
  ·
    refine ⟨183979276705513117155028871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122652851137008744770019247 183979276705513117155028871)
    ·
      refine ⟨275968915058269675732543307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183979276705513117155028871 275968915058269675732543307)
      ·
        refine ⟨413953372587404513598814961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275968915058269675732543307 413953372587404513598814961)
        ·
          refine ⟨310465029440553385199111221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413953372587404513598814961 310465029440553385199111221)
          ·
            refine ⟨29106096510051879862416677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 310465029440553385199111221 29106096510051879862416677)
            ·
              refine ⟨5457393095634727474203127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29106096510051879862416677 5457393095634727474203127)
              ·
                refine ⟨8186089643452091211304691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5457393095634727474203127 8186089643452091211304691)
                ·
                  refine ⟨12279134465178136816957037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8186089643452091211304691 12279134465178136816957037)
                  ·
                    refine ⟨4604675424441801306358889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12279134465178136816957037 4604675424441801306358889)
                    ·
                      refine ⟨3453506568331350979769167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4604675424441801306358889 3453506568331350979769167)
                      ·
                        rfl

theorem cell23_6725680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 1, 3, 2].length) (baseStart_6725680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725680 prefixEnd_6725680 := by exact prefixLift 6725680
  have htrace : WordTrace (prefixWord ++ tailWord_6725680) baseStart_6725680 baseEnd_6725680 := by
    simpa [prefixWord, tailWord_6725680, baseEnd_6725680] using wordTrace_append hprefix tailTrace_6725680
  have hstable : (prefixWord ++ tailWord_6725680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725680).length < 2 ^ (prefixWord ++ tailWord_6725680).sum := by decide
  have hdescent : baseEnd_6725680 < baseStart_6725680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725686 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 4, 6]
def baseStart_6725686 : Nat := 118140960795 + 6725686 * 2 ^ 59
def prefixEnd_6725686 : Nat := 4983230072969 + 3 ^ 40 * 6725686 * 2
def baseEnd_6725686 : Nat := 1151169883071759318764713

theorem tailTrace_6725686 : CollatzResearch.WordTrace tailWord_6725686 prefixEnd_6725686 1151169883071759318764713 := by
  unfold tailWord_6725686
  simp only [CollatzResearch.WordTrace]
  refine ⟨15331620069499734535297307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163537280741330501709837941 15331620069499734535297307)
  ·
    refine ⟨22997430104249601802945961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15331620069499734535297307 22997430104249601802945961)
    ·
      refine ⟨17248072578187201352209471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22997430104249601802945961 17248072578187201352209471)
      ·
        refine ⟨25872108867280802028314207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17248072578187201352209471 25872108867280802028314207)
        ·
          refine ⟨38808163300921203042471311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25872108867280802028314207 38808163300921203042471311)
          ·
            refine ⟨58212244951381804563706967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38808163300921203042471311 58212244951381804563706967)
            ·
              refine ⟨87318367427072706845560451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58212244951381804563706967 87318367427072706845560451)
              ·
                refine ⟨130977551140609060268340677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87318367427072706845560451 130977551140609060268340677)
                ·
                  refine ⟨24558290838864198800313877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130977551140609060268340677 24558290838864198800313877)
                  ·
                    refine ⟨1151169883071759318764713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24558290838864198800313877 1151169883071759318764713)
                    ·
                      rfl

theorem cell23_6725686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_6725686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725686 prefixEnd_6725686 := by exact prefixLift 6725686
  have htrace : WordTrace (prefixWord ++ tailWord_6725686) baseStart_6725686 baseEnd_6725686 := by
    simpa [prefixWord, tailWord_6725686, baseEnd_6725686] using wordTrace_append hprefix tailTrace_6725686
  have hstable : (prefixWord ++ tailWord_6725686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725686).length < 2 ^ (prefixWord ++ tailWord_6725686).sum := by decide
  have hdescent : baseEnd_6725686 < baseStart_6725686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725710 : List Nat := [4, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2]
def baseStart_6725710 : Nat := 118140960795 + 6725710 * 2 ^ 59
def prefixEnd_6725710 : Nat := 4983230072969 + 3 ^ 40 * 6725710 * 2
def baseEnd_6725710 : Nat := 3453521972750985862394029

theorem tailTrace_6725710 : CollatzResearch.WordTrace tailWord_6725710 prefixEnd_6725710 3453521972750985862394029 := by
  unfold tailWord_6725710
  simp only [CollatzResearch.WordTrace]
  refine ⟨30663349557988600582953823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163537864309272536442420389 30663349557988600582953823)
  ·
    refine ⟨45995024336982900874430735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30663349557988600582953823 45995024336982900874430735)
    ·
      refine ⟨68992536505474351311646103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45995024336982900874430735 68992536505474351311646103)
      ·
        refine ⟨103488804758211526967469155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68992536505474351311646103 103488804758211526967469155)
        ·
          refine ⟨155233207137317290451203733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103488804758211526967469155 155233207137317290451203733)
          ·
            refine ⟨7276556584561747989900175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 155233207137317290451203733 7276556584561747989900175)
            ·
              refine ⟨10914834876842621984850263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7276556584561747989900175 10914834876842621984850263)
              ·
                refine ⟨16372252315263932977275395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10914834876842621984850263 16372252315263932977275395)
                ·
                  refine ⟨24558378472895899465913093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16372252315263932977275395 24558378472895899465913093)
                  ·
                    refine ⟨4604695963667981149858705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24558378472895899465913093 4604695963667981149858705)
                    ·
                      refine ⟨3453521972750985862394029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4604695963667981149858705 3453521972750985862394029)
                      ·
                        rfl

theorem cell23_6725710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2].length) (baseStart_6725710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725710 prefixEnd_6725710 := by exact prefixLift 6725710
  have htrace : WordTrace (prefixWord ++ tailWord_6725710) baseStart_6725710 baseEnd_6725710 := by
    simpa [prefixWord, tailWord_6725710, baseEnd_6725710] using wordTrace_append hprefix tailTrace_6725710
  have hstable : (prefixWord ++ tailWord_6725710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725710).length < 2 ^ (prefixWord ++ tailWord_6725710).sum := by decide
  have hdescent : baseEnd_6725710 < baseStart_6725710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725733 : List Nat := [1, 3, 1, 3, 2, 2, 3, 3, 5]
def baseStart_6725733 : Nat := 118140960795 + 6725733 * 2 ^ 59
def prefixEnd_6725733 : Nat := 4983230072969 + 3 ^ 40 * 6725733 * 2
def baseEnd_6725733 : Nat := 383725975867337696934047

theorem tailTrace_6725733 : CollatzResearch.WordTrace tailWord_6725733 prefixEnd_6725733 383725975867337696934047 := by
  unfold tailWord_6725733
  simp only [CollatzResearch.WordTrace]
  refine ⟨245307635342825479591717853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163538423561883653061145235 245307635342825479591717853)
  ·
    refine ⟨91990363253559554846894195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245307635342825479591717853 91990363253559554846894195)
    ·
      refine ⟨137985544880339332270341293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91990363253559554846894195 137985544880339332270341293)
      ·
        refine ⟨51744579330127249601377985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137985544880339332270341293 51744579330127249601377985)
        ·
          refine ⟨38808434497595437201033489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51744579330127249601377985 38808434497595437201033489)
          ·
            refine ⟨29106325873196577900775117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38808434497595437201033489 29106325873196577900775117)
            ·
              refine ⟨10914872202448716712790669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29106325873196577900775117 10914872202448716712790669)
              ·
                refine ⟨4093077075918268767296501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10914872202448716712790669 4093077075918268767296501)
                ·
                  refine ⟨383725975867337696934047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4093077075918268767296501 383725975867337696934047)
                  ·
                    rfl

theorem cell23_6725733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 5].length) (baseStart_6725733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725733 prefixEnd_6725733 := by exact prefixLift 6725733
  have htrace : WordTrace (prefixWord ++ tailWord_6725733) baseStart_6725733 baseEnd_6725733 := by
    simpa [prefixWord, tailWord_6725733, baseEnd_6725733] using wordTrace_append hprefix tailTrace_6725733
  have hstable : (prefixWord ++ tailWord_6725733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725733).length < 2 ^ (prefixWord ++ tailWord_6725733).sum := by decide
  have hdescent : baseEnd_6725733 < baseStart_6725733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725746 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 4, 5]
def baseStart_6725746 : Nat := 118140960795 + 6725746 * 2 ^ 59
def prefixEnd_6725746 : Nat := 4983230072969 + 3 ^ 40 * 6725746 * 2
def baseEnd_6725746 : Nat := 1151180152684849240514621

theorem tailTrace_6725746 : CollatzResearch.WordTrace tailWord_6725746 prefixEnd_6725746 1151180152684849240514621 := by
  unfold tailWord_6725746
  simp only [CollatzResearch.WordTrace]
  refine ⟨61327027372944595702985273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163538739661185588541294061 61327027372944595702985273)
  ·
    refine ⟨45995270529708446777238955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61327027372944595702985273 45995270529708446777238955)
    ·
      refine ⟨68992905794562670165858433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45995270529708446777238955 68992905794562670165858433)
      ·
        refine ⟨51744679345922002624393825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68992905794562670165858433 51744679345922002624393825)
        ·
          refine ⟨38808509509441501968295369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51744679345922002624393825 38808509509441501968295369)
          ·
            refine ⟨29106382132081126476221527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38808509509441501968295369 29106382132081126476221527)
            ·
              refine ⟨43659573198121689714332291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29106382132081126476221527 43659573198121689714332291)
              ·
                refine ⟨65489359797182534571498437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43659573198121689714332291 65489359797182534571498437)
                ·
                  refine ⟨12279254961971725232155957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65489359797182534571498437 12279254961971725232155957)
                  ·
                    refine ⟨1151180152684849240514621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12279254961971725232155957 1151180152684849240514621)
                    ·
                      rfl

theorem cell23_6725746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_6725746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725746 prefixEnd_6725746 := by exact prefixLift 6725746
  have htrace : WordTrace (prefixWord ++ tailWord_6725746) baseStart_6725746 baseEnd_6725746 := by
    simpa [prefixWord, tailWord_6725746, baseEnd_6725746] using wordTrace_append hprefix tailTrace_6725746
  have hstable : (prefixWord ++ tailWord_6725746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725746).length < 2 ^ (prefixWord ++ tailWord_6725746).sum := by decide
  have hdescent : baseEnd_6725746 < baseStart_6725746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725756 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 1, 2, 5]
def baseStart_6725756 : Nat := 118140960795 + 6725756 * 2 ^ 59
def prefixEnd_6725756 : Nat := 4983230072969 + 3 ^ 40 * 6725756 * 2
def baseEnd_6725756 : Nat := 3453545592861092682418817

theorem tailTrace_6725756 : CollatzResearch.WordTrace tailWord_6725756 prefixEnd_6725756 3453545592861092682418817 := by
  unfold tailWord_6725756
  simp only [CollatzResearch.WordTrace]
  refine ⟨122654237110871077259902561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163538982814494769679870081 122654237110871077259902561)
  ·
    refine ⟨91990677833153307944926921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122654237110871077259902561 91990677833153307944926921)
    ·
      refine ⟨68993008374864980958695191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91990677833153307944926921 68993008374864980958695191)
      ·
        refine ⟨103489512562297471438042787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68993008374864980958695191 103489512562297471438042787)
        ·
          refine ⟨155234268843446207157064181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103489512562297471438042787 155234268843446207157064181)
          ·
            refine ⟨14553212704073081920974767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155234268843446207157064181 14553212704073081920974767)
            ·
              refine ⟨21829819056109622881462151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14553212704073081920974767 21829819056109622881462151)
              ·
                refine ⟨32744728584164434322193227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21829819056109622881462151 32744728584164434322193227)
                ·
                  refine ⟨49117092876246651483289841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32744728584164434322193227 49117092876246651483289841)
                  ·
                    refine ⟨36837819657184988612467381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49117092876246651483289841 36837819657184988612467381)
                    ·
                      refine ⟨3453545592861092682418817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36837819657184988612467381 3453545592861092682418817)
                      ·
                        rfl

theorem cell23_6725756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_6725756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725756 prefixEnd_6725756 := by exact prefixLift 6725756
  have htrace : WordTrace (prefixWord ++ tailWord_6725756) baseStart_6725756 baseEnd_6725756 := by
    simpa [prefixWord, tailWord_6725756, baseEnd_6725756] using wordTrace_append hprefix tailTrace_6725756
  have hstable : (prefixWord ++ tailWord_6725756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725756).length < 2 ^ (prefixWord ++ tailWord_6725756).sum := by decide
  have hdescent : baseEnd_6725756 < baseStart_6725756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725761 : List Nat := [1, 2, 4, 2, 4, 1, 2, 1, 2, 2, 2]
def baseStart_6725761 : Nat := 118140960795 + 6725761 * 2 ^ 59
def prefixEnd_6725761 : Nat := 4983230072969 + 3 ^ 40 * 6725761 * 2
def baseEnd_6725761 : Nat := 3453548160264365162856295

theorem tailTrace_6725761 : CollatzResearch.WordTrace tailWord_6725761 prefixEnd_6725761 3453548160264365162856295 := by
  unfold tailWord_6725761
  simp only [CollatzResearch.WordTrace]
  refine ⟨245308656586724040373737137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163539104391149360249158091 245308656586724040373737137)
  ·
    refine ⟨183981492440043030280302853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245308656586724040373737137 183981492440043030280302853)
    ·
      refine ⟨34496529832508068177556785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183981492440043030280302853 34496529832508068177556785)
      ·
        refine ⟨25872397374381051133167589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34496529832508068177556785 25872397374381051133167589)
        ·
          refine ⟨4851074507696447087468923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25872397374381051133167589 4851074507696447087468923)
          ·
            refine ⟨7276611761544670631203385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4851074507696447087468923 7276611761544670631203385)
            ·
              refine ⟨5457458821158502973402539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7276611761544670631203385 5457458821158502973402539)
              ·
                refine ⟨8186188231737754460103809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5457458821158502973402539 8186188231737754460103809)
                ·
                  refine ⟨6139641173803315845077857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8186188231737754460103809 6139641173803315845077857)
                  ·
                    refine ⟨4604730880352486883808393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6139641173803315845077857 4604730880352486883808393)
                    ·
                      refine ⟨3453548160264365162856295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4604730880352486883808393 3453548160264365162856295)
                      ·
                        rfl

theorem cell23_6725761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_6725761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725761 prefixEnd_6725761 := by exact prefixLift 6725761
  have htrace : WordTrace (prefixWord ++ tailWord_6725761) baseStart_6725761 baseEnd_6725761 := by
    simpa [prefixWord, tailWord_6725761, baseEnd_6725761] using wordTrace_append hprefix tailTrace_6725761
  have hstable : (prefixWord ++ tailWord_6725761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725761).length < 2 ^ (prefixWord ++ tailWord_6725761).sum := by decide
  have hdescent : baseEnd_6725761 < baseStart_6725761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725776 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 5, 4]
def baseStart_6725776 : Nat := 118140960795 + 6725776 * 2 ^ 59
def prefixEnd_6725776 : Nat := 4983230072969 + 3 ^ 40 * 6725776 * 2
def baseEnd_6725776 : Nat := 1151185287491394201389575

theorem tailTrace_6725776 : CollatzResearch.WordTrace tailWord_6725776 prefixEnd_6725776 1151185287491394201389575 := by
  unfold tailWord_6725776
  simp only [CollatzResearch.WordTrace]
  refine ⟨122654601840834848967766591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163539469121113131957022121 122654601840834848967766591)
  ·
    refine ⟨183981902761252273451649887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122654601840834848967766591 183981902761252273451649887)
    ·
      refine ⟨275972854141878410177474831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183981902761252273451649887 275972854141878410177474831)
      ·
        refine ⟨413959281212817615266212247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275972854141878410177474831 413959281212817615266212247)
        ·
          refine ⟨620938921819226422899318371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413959281212817615266212247 620938921819226422899318371)
          ·
            refine ⟨931408382728839634348977557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620938921819226422899318371 931408382728839634348977557)
            ·
              refine ⟨43659767940414357860108323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 931408382728839634348977557 43659767940414357860108323)
              ·
                refine ⟨65489651910621536790162485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43659767940414357860108323 65489651910621536790162485)
                ·
                  refine ⟨6139654866620769074077733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65489651910621536790162485 6139654866620769074077733)
                  ·
                    refine ⟨1151185287491394201389575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6139654866620769074077733 1151185287491394201389575)
                    ·
                      rfl

theorem cell23_6725776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 5, 4].length) (baseStart_6725776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725776 prefixEnd_6725776 := by exact prefixLift 6725776
  have htrace : WordTrace (prefixWord ++ tailWord_6725776) baseStart_6725776 baseEnd_6725776 := by
    simpa [prefixWord, tailWord_6725776, baseEnd_6725776] using wordTrace_append hprefix tailTrace_6725776
  have hstable : (prefixWord ++ tailWord_6725776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725776).length < 2 ^ (prefixWord ++ tailWord_6725776).sum := by decide
  have hdescent : baseEnd_6725776 < baseStart_6725776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725779 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 6]
def baseStart_6725779 : Nat := 118140960795 + 6725779 * 2 ^ 59
def prefixEnd_6725779 : Nat := 4983230072969 + 3 ^ 40 * 6725779 * 2
def baseEnd_6725779 : Nat := 3453557402916146092431211

theorem tailTrace_6725779 : CollatzResearch.WordTrace tailWord_6725779 prefixEnd_6725779 3453557402916146092431211 := by
  unfold tailWord_6725779
  simp only [CollatzResearch.WordTrace]
  refine ⟨245309313100658829447892391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163539542067105886298594927 245309313100658829447892391)
  ·
    refine ⟨367963969650988244171838587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245309313100658829447892391 367963969650988244171838587)
    ·
      refine ⟨551945954476482366257757881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367963969650988244171838587 551945954476482366257757881)
      ·
        refine ⟨413959465857361774693318411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 551945954476482366257757881 413959465857361774693318411)
        ·
          refine ⟨620939198786042662039977617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413959465857361774693318411 620939198786042662039977617)
          ·
            refine ⟨465704399089531996529983213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 620939198786042662039977617 465704399089531996529983213)
            ·
              refine ⟨174639149658574498698743705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 465704399089531996529983213 174639149658574498698743705)
              ·
                refine ⟨130979362243930874024057779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174639149658574498698743705 130979362243930874024057779)
                ·
                  refine ⟨196469043365896311036086669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130979362243930874024057779 196469043365896311036086669)
                  ·
                    refine ⟨73675891262211116638532501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 196469043365896311036086669 73675891262211116638532501)
                    ·
                      refine ⟨3453557402916146092431211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73675891262211116638532501 3453557402916146092431211)
                      ·
                        rfl

theorem cell23_6725779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_6725779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725779 prefixEnd_6725779 := by exact prefixLift 6725779
  have htrace : WordTrace (prefixWord ++ tailWord_6725779) baseStart_6725779 baseEnd_6725779 := by
    simpa [prefixWord, tailWord_6725779, baseEnd_6725779] using wordTrace_append hprefix tailTrace_6725779
  have hstable : (prefixWord ++ tailWord_6725779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725779).length < 2 ^ (prefixWord ++ tailWord_6725779).sum := by decide
  have hdescent : baseEnd_6725779 < baseStart_6725779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725810 : List Nat := [3, 2, 1, 1, 1, 3, 3, 4, 1, 4]
def baseStart_6725810 : Nat := 118140960795 + 6725810 * 2 ^ 59
def prefixEnd_6725810 : Nat := 4983230072969 + 3 ^ 40 * 6725810 * 2
def baseEnd_6725810 : Nat := 1151191106938811823714523

theorem tailTrace_6725810 : CollatzResearch.WordTrace tailWord_6725810 prefixEnd_6725810 1151191106938811823714523 := by
  unfold tailWord_6725810
  simp only [CollatzResearch.WordTrace]
  refine ⟨61327610940886630435567721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163540295842364347828180589 61327610940886630435567721)
  ·
    refine ⟨45995708205664972826675791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61327610940886630435567721 45995708205664972826675791)
    ·
      refine ⟨68993562308497459240013687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45995708205664972826675791 68993562308497459240013687)
      ·
        refine ⟨103490343462746188860020531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68993562308497459240013687 103490343462746188860020531)
        ·
          refine ⟨155235515194119283290030797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103490343462746188860020531 155235515194119283290030797)
          ·
            refine ⟨58213318197794731233761549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155235515194119283290030797 58213318197794731233761549)
            ·
              refine ⟨21829994324173024212660581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58213318197794731233761549 21829994324173024212660581)
              ·
                refine ⟨4093123935782442039873859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21829994324173024212660581 4093123935782442039873859)
                ·
                  refine ⟨6139685903673663059810789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4093123935782442039873859 6139685903673663059810789)
                  ·
                    refine ⟨1151191106938811823714523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6139685903673663059810789 1151191106938811823714523)
                    ·
                      rfl

theorem cell23_6725810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_6725810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725810 prefixEnd_6725810 := by exact prefixLift 6725810
  have htrace : WordTrace (prefixWord ++ tailWord_6725810) baseStart_6725810 baseEnd_6725810 := by
    simpa [prefixWord, tailWord_6725810, baseEnd_6725810] using wordTrace_append hprefix tailTrace_6725810
  have hstable : (prefixWord ++ tailWord_6725810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725810).length < 2 ^ (prefixWord ++ tailWord_6725810).sum := by decide
  have hdescent : baseEnd_6725810 < baseStart_6725810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725918 : List Nat := [4, 3, 2, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_6725918 : Nat := 118140960795 + 6725918 * 2 ^ 59
def prefixEnd_6725918 : Nat := 4983230072969 + 3 ^ 40 * 6725918 * 2
def baseEnd_6725918 : Nat := 3453628776727121048593073

theorem tailTrace_6725918 : CollatzResearch.WordTrace tailWord_6725918 prefixEnd_6725918 3453628776727121048593073 := by
  unfold tailWord_6725918
  simp only [CollatzResearch.WordTrace]
  refine ⟨30664297855894407023400301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163542921898103504124801605 30664297855894407023400301)
  ·
    refine ⟨11499111695960402633775113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30664297855894407023400301 11499111695960402633775113)
    ·
      refine ⟨8624333771970301975331335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11499111695960402633775113 8624333771970301975331335)
      ·
        refine ⟨12936500657955452962997003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8624333771970301975331335 12936500657955452962997003)
        ·
          refine ⟨19404750986933179444495505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12936500657955452962997003 19404750986933179444495505)
          ·
            refine ⟨14553563240199884583371629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19404750986933179444495505 14553563240199884583371629)
            ·
              refine ⟨5457586215074956718764361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14553563240199884583371629 5457586215074956718764361)
              ·
                refine ⟨4093189661306217539073271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5457586215074956718764361 4093189661306217539073271)
                ·
                  refine ⟨6139784491959326308609907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4093189661306217539073271 6139784491959326308609907)
                  ·
                    refine ⟨9209676737938989462914861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6139784491959326308609907 9209676737938989462914861)
                    ·
                      refine ⟨3453628776727121048593073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9209676737938989462914861 3453628776727121048593073)
                      ·
                        rfl

theorem cell23_6725918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_6725918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725918 prefixEnd_6725918 := by exact prefixLift 6725918
  have htrace : WordTrace (prefixWord ++ tailWord_6725918) baseStart_6725918 baseEnd_6725918 := by
    simpa [prefixWord, tailWord_6725918, baseEnd_6725918] using wordTrace_append hprefix tailTrace_6725918
  have hstable : (prefixWord ++ tailWord_6725918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725918).length < 2 ^ (prefixWord ++ tailWord_6725918).sum := by decide
  have hdescent : baseEnd_6725918 < baseStart_6725918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725924 : List Nat := [2, 3, 1, 3, 1, 4, 1, 1, 3, 2, 2]
def baseStart_6725924 : Nat := 118140960795 + 6725924 * 2 ^ 59
def prefixEnd_6725924 : Nat := 4983230072969 + 3 ^ 40 * 6725924 * 2
def baseEnd_6725924 : Nat := 3453631857611048025118045

theorem tailTrace_6725924 : CollatzResearch.WordTrace tailWord_6725924 prefixEnd_6725924 3453631857611048025118045 := by
  unfold tailWord_6725924
  simp only [CollatzResearch.WordTrace]
  refine ⟨122657300842566759605960413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163543067790089012807947217 122657300842566759605960413)
  ·
    refine ⟨45996487815962534852235155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122657300842566759605960413 45996487815962534852235155)
    ·
      refine ⟨68994731723943802278352733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45996487815962534852235155 68994731723943802278352733)
      ·
        refine ⟨25873024396478925854382275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68994731723943802278352733 25873024396478925854382275)
        ·
          refine ⟨38809536594718388781573413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25873024396478925854382275 38809536594718388781573413)
          ·
            refine ⟨7276788111509697896545015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38809536594718388781573413 7276788111509697896545015)
            ·
              refine ⟨10915182167264546844817523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7276788111509697896545015 10915182167264546844817523)
              ·
                refine ⟨16372773250896820267226285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10915182167264546844817523 16372773250896820267226285)
                ·
                  refine ⟨6139789969086307600209857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16372773250896820267226285 6139789969086307600209857)
                  ·
                    refine ⟨4604842476814730700157393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6139789969086307600209857 4604842476814730700157393)
                    ·
                      refine ⟨3453631857611048025118045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4604842476814730700157393 3453631857611048025118045)
                      ·
                        rfl

theorem cell23_6725924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_6725924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725924 prefixEnd_6725924 := by exact prefixLift 6725924
  have htrace : WordTrace (prefixWord ++ tailWord_6725924) baseStart_6725924 baseEnd_6725924 := by
    simpa [prefixWord, tailWord_6725924, baseEnd_6725924] using wordTrace_append hprefix tailTrace_6725924
  have hstable : (prefixWord ++ tailWord_6725924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725924).length < 2 ^ (prefixWord ++ tailWord_6725924).sum := by decide
  have hdescent : baseEnd_6725924 < baseStart_6725924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725930 : List Nat := [3, 1, 4, 2, 2, 1, 2, 8]
def baseStart_6725930 : Nat := 118140960795 + 6725930 * 2 ^ 59
def prefixEnd_6725930 : Nat := 4983230072969 + 3 ^ 40 * 6725930 * 2
def baseEnd_6725930 : Nat := 127912405129443518579371

theorem tailTrace_6725930 : CollatzResearch.WordTrace tailWord_6725930 prefixEnd_6725930 127912405129443518579371 := by
  unfold tailWord_6725930
  simp only [CollatzResearch.WordTrace]
  refine ⟨61328705130777945559159811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163543213682074521491092829 61328705130777945559159811)
  ·
    refine ⟨91993057696166918338739717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61328705130777945559159811 91993057696166918338739717)
    ·
      refine ⟨17248698318031297188513697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91993057696166918338739717 17248698318031297188513697)
      ·
        refine ⟨12936523738523472891385273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17248698318031297188513697 12936523738523472891385273)
        ·
          refine ⟨9702392803892604668538955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12936523738523472891385273 9702392803892604668538955)
          ·
            refine ⟨14553589205838907002808433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9702392803892604668538955 14553589205838907002808433)
            ·
              refine ⟨10915191904379180252106325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14553589205838907002808433 10915191904379180252106325)
              ·
                refine ⟨127912405129443518579371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10915191904379180252106325 127912405129443518579371)
                ·
                  rfl

theorem cell23_6725930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 8].length) (baseStart_6725930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725930 prefixEnd_6725930 := by exact prefixLift 6725930
  have htrace : WordTrace (prefixWord ++ tailWord_6725930) baseStart_6725930 baseEnd_6725930 := by
    simpa [prefixWord, tailWord_6725930, baseEnd_6725930] using wordTrace_append hprefix tailTrace_6725930
  have hstable : (prefixWord ++ tailWord_6725930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725930).length < 2 ^ (prefixWord ++ tailWord_6725930).sum := by decide
  have hdescent : baseEnd_6725930 < baseStart_6725930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725934 : List Nat := [4, 1, 3, 3, 1, 1, 1, 3, 2, 4]
def baseStart_6725934 : Nat := 118140960795 + 6725934 * 2 ^ 59
def prefixEnd_6725934 : Nat := 4983230072969 + 3 ^ 40 * 6725934 * 2
def baseEnd_6725934 : Nat := 1151212330805864328664333

theorem tailTrace_6725934 : CollatzResearch.WordTrace tailWord_6725934 prefixEnd_6725934 1151212330805864328664333 := by
  unfold tailWord_6725934
  simp only [CollatzResearch.WordTrace]
  refine ⟨30664370801887161364973107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163543310943398193946523237 30664370801887161364973107)
  ·
    refine ⟨45996556202830742047459661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30664370801887161364973107 45996556202830742047459661)
    ·
      refine ⟨17248708576061528267797373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45996556202830742047459661 17248708576061528267797373)
      ·
        refine ⟨6468265716023073100424015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17248708576061528267797373 6468265716023073100424015)
        ·
          refine ⟨9702398574034609650636023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6468265716023073100424015 9702398574034609650636023)
          ·
            refine ⟨14553597861051914475954035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9702398574034609650636023 14553597861051914475954035)
            ·
              refine ⟨21830396791577871713931053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14553597861051914475954035 21830396791577871713931053)
              ·
                refine ⟨8186398796841701892724145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21830396791577871713931053 8186398796841701892724145)
                ·
                  refine ⟨6139799097631276419543109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8186398796841701892724145 6139799097631276419543109)
                  ·
                    refine ⟨1151212330805864328664333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6139799097631276419543109 1151212330805864328664333)
                    ·
                      rfl

theorem cell23_6725934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_6725934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725934 prefixEnd_6725934 := by exact prefixLift 6725934
  have htrace : WordTrace (prefixWord ++ tailWord_6725934) baseStart_6725934 baseEnd_6725934 := by
    simpa [prefixWord, tailWord_6725934, baseEnd_6725934] using wordTrace_append hprefix tailTrace_6725934
  have hstable : (prefixWord ++ tailWord_6725934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725934).length < 2 ^ (prefixWord ++ tailWord_6725934).sum := by decide
  have hdescent : baseEnd_6725934 < baseStart_6725934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725936 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 5]
def baseStart_6725936 : Nat := 118140960795 + 6725936 * 2 ^ 59
def prefixEnd_6725936 : Nat := 4983230072969 + 3 ^ 40 * 6725936 * 2
def baseEnd_6725936 : Nat := 3453638019378901978167989

theorem tailTrace_6725936 : CollatzResearch.WordTrace tailWord_6725936 prefixEnd_6725936 3453638019378901978167989 := by
  unfold tailWord_6725936
  simp only [CollatzResearch.WordTrace]
  refine ⟨122657519680545022630678831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163543359574060030174238441 122657519680545022630678831)
  ·
    refine ⟨183986279520817533946018247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122657519680545022630678831 183986279520817533946018247)
    ·
      refine ⟨275979419281226300919027371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183986279520817533946018247 275979419281226300919027371)
      ·
        refine ⟨413969128921839451378541057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275979419281226300919027371 413969128921839451378541057)
        ·
          refine ⟨310476846691379588533905793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413969128921839451378541057 310476846691379588533905793)
          ·
            refine ⟨232857635018534691400429345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310476846691379588533905793 232857635018534691400429345)
            ·
              refine ⟨174643226263901018550322009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232857635018534691400429345 174643226263901018550322009)
              ·
                refine ⟨130982419697925763912741507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174643226263901018550322009 130982419697925763912741507)
                ·
                  refine ⟨196473629546888645869112261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130982419697925763912741507 196473629546888645869112261)
                  ·
                    refine ⟨36838805540041621100458549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 196473629546888645869112261 36838805540041621100458549)
                    ·
                      refine ⟨3453638019378901978167989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36838805540041621100458549 3453638019378901978167989)
                      ·
                        rfl

theorem cell23_6725936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_6725936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725936 prefixEnd_6725936 := by exact prefixLift 6725936
  have htrace : WordTrace (prefixWord ++ tailWord_6725936) baseStart_6725936 baseEnd_6725936 := by
    simpa [prefixWord, tailWord_6725936, baseEnd_6725936] using wordTrace_append hprefix tailTrace_6725936
  have hstable : (prefixWord ++ tailWord_6725936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725936).length < 2 ^ (prefixWord ++ tailWord_6725936).sum := by decide
  have hdescent : baseEnd_6725936 < baseStart_6725936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725983 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 3]
def baseStart_6725983 : Nat := 118140960795 + 6725983 * 2 ^ 59
def prefixEnd_6725983 : Nat := 4983230072969 + 3 ^ 40 * 6725983 * 2
def baseEnd_6725983 : Nat := 3453662152969663294280273

theorem tailTrace_6725983 : CollatzResearch.WordTrace tailWord_6725983 prefixEnd_6725983 3453662152969663294280273 := by
  unfold tailWord_6725983
  simp only [CollatzResearch.WordTrace]
  refine ⟨245316753591919772288318603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163544502394613181525545735 245316753591919772288318603)
  ·
    refine ⟨367975130387879658432477905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245316753591919772288318603 367975130387879658432477905)
    ·
      refine ⟨275981347790909743824358429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367975130387879658432477905 275981347790909743824358429)
      ·
        refine ⟨103493005421591153934134411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275981347790909743824358429 103493005421591153934134411)
        ·
          refine ⟨155239508132386730901201617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103493005421591153934134411 155239508132386730901201617)
          ·
            refine ⟨116429631099290048175901213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155239508132386730901201617 116429631099290048175901213)
            ·
              refine ⟨43661111662233768065962955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116429631099290048175901213 43661111662233768065962955)
              ·
                refine ⟨65491667493350652098944433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43661111662233768065962955 65491667493350652098944433)
                ·
                  refine ⟨49118750620012989074208325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65491667493350652098944433 49118750620012989074208325)
                  ·
                    refine ⟨9209765741252435451414061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49118750620012989074208325 9209765741252435451414061)
                    ·
                      refine ⟨3453662152969663294280273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9209765741252435451414061 3453662152969663294280273)
                      ·
                        rfl

theorem cell23_6725983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_6725983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725983 prefixEnd_6725983 := by exact prefixLift 6725983
  have htrace : WordTrace (prefixWord ++ tailWord_6725983) baseStart_6725983 baseEnd_6725983 := by
    simpa [prefixWord, tailWord_6725983, baseEnd_6725983] using wordTrace_append hprefix tailTrace_6725983
  have hstable : (prefixWord ++ tailWord_6725983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725983).length < 2 ^ (prefixWord ++ tailWord_6725983).sum := by decide
  have hdescent : baseEnd_6725983 < baseStart_6725983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725993 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 2, 2, 4]
def baseStart_6725993 : Nat := 118140960795 + 6725993 * 2 ^ 59
def prefixEnd_6725993 : Nat := 4983230072969 + 3 ^ 40 * 6725993 * 2
def baseEnd_6725993 : Nat := 3453667287776208255155227

theorem tailTrace_6725993 : CollatzResearch.WordTrace tailWord_6725993 prefixEnd_6725993 3453667287776208255155227 := by
  unfold tailWord_6725993
  simp only [CollatzResearch.WordTrace]
  refine ⟨245317118321883543996182633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163544745547922362664121755 245317118321883543996182633)
  ·
    refine ⟨183987838741412657997136975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245317118321883543996182633 183987838741412657997136975)
    ·
      refine ⟨275981758112118986995705463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183987838741412657997136975 275981758112118986995705463)
      ·
        refine ⟨413972637168178480493558195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275981758112118986995705463 413972637168178480493558195)
        ·
          refine ⟨620958955752267720740337293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413972637168178480493558195 620958955752267720740337293)
          ·
            refine ⟨232859608407100395277626485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 620958955752267720740337293 232859608407100395277626485)
            ·
              refine ⟨21830588288165662057277483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 232859608407100395277626485 21830588288165662057277483)
              ·
                refine ⟨32745882432248493085916225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21830588288165662057277483 32745882432248493085916225)
                ·
                  refine ⟨24559411824186369814437169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32745882432248493085916225 24559411824186369814437169)
                  ·
                    refine ⟨18419558868139777360827877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24559411824186369814437169 18419558868139777360827877)
                    ·
                      refine ⟨3453667287776208255155227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18419558868139777360827877 3453667287776208255155227)
                      ·
                        rfl

theorem cell23_6725993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 2, 4].length) (baseStart_6725993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725993 prefixEnd_6725993 := by exact prefixLift 6725993
  have htrace : WordTrace (prefixWord ++ tailWord_6725993) baseStart_6725993 baseEnd_6725993 := by
    simpa [prefixWord, tailWord_6725993, baseEnd_6725993] using wordTrace_append hprefix tailTrace_6725993
  have hstable : (prefixWord ++ tailWord_6725993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725993).length < 2 ^ (prefixWord ++ tailWord_6725993).sum := by decide
  have hdescent : baseEnd_6725993 < baseStart_6725993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6725997 : List Nat := [1, 5, 1, 1, 1, 2, 4, 1, 1, 4, 2]
def baseStart_6725997 : Nat := 118140960795 + 6725997 * 2 ^ 59
def prefixEnd_6725997 : Nat := 4983230072969 + 3 ^ 40 * 6725997 * 2
def baseEnd_6725997 : Nat := 3453669341698826239505209

theorem tailTrace_6725997 : CollatzResearch.WordTrace tailWord_6725997 prefixEnd_6725997 3453669341698826239505209 := by
  unfold tailWord_6725997
  simp only [CollatzResearch.WordTrace]
  refine ⟨245317264213869052679328245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163544842809246035119552163 245317264213869052679328245)
  ·
    refine ⟨22998493520050223688687023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 245317264213869052679328245 22998493520050223688687023)
    ·
      refine ⟨34497740280075335533030535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22998493520050223688687023 34497740280075335533030535)
      ·
        refine ⟨51746610420113003299545803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34497740280075335533030535 51746610420113003299545803)
        ·
          refine ⟨77619915630169504949318705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51746610420113003299545803 77619915630169504949318705)
          ·
            refine ⟨58214936722627128711989029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77619915630169504949318705 58214936722627128711989029)
            ·
              refine ⟨10915300635492586633497943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58214936722627128711989029 10915300635492586633497943)
              ·
                refine ⟨16372950953238879950246915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10915300635492586633497943 16372950953238879950246915)
                ·
                  refine ⟨24559426429858319925370373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16372950953238879950246915 24559426429858319925370373)
                  ·
                    refine ⟨4604892455598434986006945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24559426429858319925370373 4604892455598434986006945)
                    ·
                      refine ⟨3453669341698826239505209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4604892455598434986006945 3453669341698826239505209)
                      ·
                        rfl

theorem cell23_6725997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_6725997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6725997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6725997 prefixEnd_6725997 := by exact prefixLift 6725997
  have htrace : WordTrace (prefixWord ++ tailWord_6725997) baseStart_6725997 baseEnd_6725997 := by
    simpa [prefixWord, tailWord_6725997, baseEnd_6725997] using wordTrace_append hprefix tailTrace_6725997
  have hstable : (prefixWord ++ tailWord_6725997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6725997).length < 2 ^ (prefixWord ++ tailWord_6725997).sum := by decide
  have hdescent : baseEnd_6725997 < baseStart_6725997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6725997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726053 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 3, 3, 4]
def baseStart_6726053 : Nat := 118140960795 + 6726053 * 2 ^ 59
def prefixEnd_6726053 : Nat := 4983230072969 + 3 ^ 40 * 6726053 * 2
def baseEnd_6726053 : Nat := 3453698096615478020404951

theorem tailTrace_6726053 : CollatzResearch.WordTrace tailWord_6726053 prefixEnd_6726053 3453698096615478020404951 := by
  unfold tailWord_6726053
  simp only [CollatzResearch.WordTrace]
  refine ⟨245319306701666174243366813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163546204467777449495577875 245319306701666174243366813)
  ·
    refine ⟨91994740013124815341262555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245319306701666174243366813 91994740013124815341262555)
    ·
      refine ⟨137992110019687223011893833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91994740013124815341262555 137992110019687223011893833)
      ·
        refine ⟨103494082514765417258920375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137992110019687223011893833 103494082514765417258920375)
        ·
          refine ⟨155241123772148125888380563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103494082514765417258920375 155241123772148125888380563)
          ·
            refine ⟨232861685658222188832570845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155241123772148125888380563 232861685658222188832570845)
            ·
              refine ⟨87323132121833320812214067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232861685658222188832570845 87323132121833320812214067)
              ·
                refine ⟨130984698182749981218321101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87323132121833320812214067 130984698182749981218321101)
                ·
                  refine ⟨49119261818531242956870413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130984698182749981218321101 49119261818531242956870413)
                  ·
                    refine ⟨18419723181949216108826405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49119261818531242956870413 18419723181949216108826405)
                    ·
                      refine ⟨3453698096615478020404951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18419723181949216108826405 3453698096615478020404951)
                      ·
                        rfl

theorem cell23_6726053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_6726053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726053 prefixEnd_6726053 := by exact prefixLift 6726053
  have htrace : WordTrace (prefixWord ++ tailWord_6726053) baseStart_6726053 baseEnd_6726053 := by
    simpa [prefixWord, tailWord_6726053, baseEnd_6726053] using wordTrace_append hprefix tailTrace_6726053
  have hstable : (prefixWord ++ tailWord_6726053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726053).length < 2 ^ (prefixWord ++ tailWord_6726053).sum := by decide
  have hdescent : baseEnd_6726053 < baseStart_6726053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726097 : List Nat := [1, 2, 2, 1, 2, 1, 1, 8, 1, 4]
def baseStart_6726097 : Nat := 118140960795 + 6726097 * 2 ^ 59
def prefixEnd_6726097 : Nat := 4983230072969 + 3 ^ 40 * 6726097 * 2
def baseEnd_6726097 : Nat := 1151240229921425282751583

theorem tailTrace_6726097 : CollatzResearch.WordTrace tailWord_6726097 prefixEnd_6726097 1151240229921425282751583 := by
  unfold tailWord_6726097
  simp only [CollatzResearch.WordTrace]
  refine ⟨245320911513506769757968545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163547274342337846505312363 245320911513506769757968545)
  ·
    refine ⟨183990683635130077318476409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245320911513506769757968545 183990683635130077318476409)
    ·
      refine ⟨137993012726347557988857307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183990683635130077318476409 137993012726347557988857307)
      ·
        refine ⟨206989519089521336983285961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137993012726347557988857307 206989519089521336983285961)
        ·
          refine ⟨155242139317141002737464471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206989519089521336983285961 155242139317141002737464471)
          ·
            refine ⟨232863208975711504106196707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155242139317141002737464471 232863208975711504106196707)
            ·
              refine ⟨349294813463567256159295061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232863208975711504106196707 349294813463567256159295061)
              ·
                refine ⟨4093298595276178783116739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 349294813463567256159295061 4093298595276178783116739)
                ·
                  refine ⟨6139947892914268174675109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4093298595276178783116739 6139947892914268174675109)
                  ·
                    refine ⟨1151240229921425282751583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6139947892914268174675109 1151240229921425282751583)
                    ·
                      rfl

theorem cell23_6726097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 1, 4].length) (baseStart_6726097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726097 prefixEnd_6726097 := by exact prefixLift 6726097
  have htrace : WordTrace (prefixWord ++ tailWord_6726097) baseStart_6726097 baseEnd_6726097 := by
    simpa [prefixWord, tailWord_6726097, baseEnd_6726097] using wordTrace_append hprefix tailTrace_6726097
  have hstable : (prefixWord ++ tailWord_6726097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726097).length < 2 ^ (prefixWord ++ tailWord_6726097).sum := by decide
  have hdescent : baseEnd_6726097 < baseStart_6726097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726147 : List Nat := [1, 1, 1, 3, 2, 1, 3, 4, 2, 3, 2]
def baseStart_6726147 : Nat := 118140960795 + 6726147 * 2 ^ 59
def prefixEnd_6726147 : Nat := 4983230072969 + 3 ^ 40 * 6726147 * 2
def baseEnd_6726147 : Nat := 3453746363797000652629519

theorem tailTrace_6726147 : CollatzResearch.WordTrace tailWord_6726147 prefixEnd_6726147 3453746363797000652629519 := by
  unfold tailWord_6726147
  simp only [CollatzResearch.WordTrace]
  refine ⟨245322735163325628297288695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163548490108883752198192463 245322735163325628297288695)
  ·
    refine ⟨367984102744988442445933043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245322735163325628297288695 367984102744988442445933043)
    ·
      refine ⟨551976154117482663668899565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367984102744988442445933043 551976154117482663668899565)
      ·
        refine ⟨206991057794055998875837337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 551976154117482663668899565 206991057794055998875837337)
        ·
          refine ⟨155243293345541999156878003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206991057794055998875837337 155243293345541999156878003)
          ·
            refine ⟨232864940018312998735317005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155243293345541999156878003 232864940018312998735317005)
            ·
              refine ⟨87324352506867374525743877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232864940018312998735317005 87324352506867374525743877)
              ·
                refine ⟨16373316095037632723576977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87324352506867374525743877 16373316095037632723576977)
                ·
                  refine ⟨12279987071278224542682733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16373316095037632723576977 12279987071278224542682733)
                  ·
                    refine ⟨4604995151729334203506025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12279987071278224542682733 4604995151729334203506025)
                    ·
                      refine ⟨3453746363797000652629519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4604995151729334203506025 3453746363797000652629519)
                      ·
                        rfl

theorem cell23_6726147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 3, 2].length) (baseStart_6726147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726147 prefixEnd_6726147 := by exact prefixLift 6726147
  have htrace : WordTrace (prefixWord ++ tailWord_6726147) baseStart_6726147 baseEnd_6726147 := by
    simpa [prefixWord, tailWord_6726147, baseEnd_6726147] using wordTrace_append hprefix tailTrace_6726147
  have hstable : (prefixWord ++ tailWord_6726147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726147).length < 2 ^ (prefixWord ++ tailWord_6726147).sum := by decide
  have hdescent : baseEnd_6726147 < baseStart_6726147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726148 : List Nat := [2, 3, 2, 3, 1, 3, 2, 2, 1, 4]
def baseStart_6726148 : Nat := 118140960795 + 6726148 * 2 ^ 59
def prefixEnd_6726148 : Nat := 4983230072969 + 3 ^ 40 * 6726148 * 2
def baseEnd_6726148 : Nat := 1151248959092551716239005

theorem tailTrace_6726148 : CollatzResearch.WordTrace tailWord_6726148 prefixEnd_6726148 1151248959092551716239005 := by
  unfold tailWord_6726148
  simp only [CollatzResearch.WordTrace]
  refine ⟨122661385818161002734037549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163548514424214670312050065 122661385818161002734037549)
  ·
    refine ⟨45998019681810376025264081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122661385818161002734037549 45998019681810376025264081)
    ·
      refine ⟨34498514761357782018948061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45998019681810376025264081 34498514761357782018948061)
      ·
        refine ⟨12936943035509168257105523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34498514761357782018948061 12936943035509168257105523)
        ·
          refine ⟨19405414553263752385658285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12936943035509168257105523 19405414553263752385658285)
          ·
            refine ⟨7277030457473907144621857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19405414553263752385658285 7277030457473907144621857)
            ·
              refine ⟨5457772843105430358466393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7277030457473907144621857 5457772843105430358466393)
              ·
                refine ⟨4093329632329072768849795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5457772843105430358466393 4093329632329072768849795)
                ·
                  refine ⟨6139994448493609153274693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4093329632329072768849795 6139994448493609153274693)
                  ·
                    refine ⟨1151248959092551716239005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6139994448493609153274693 1151248959092551716239005)
                    ·
                      rfl

theorem cell23_6726148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_6726148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726148 prefixEnd_6726148 := by exact prefixLift 6726148
  have htrace : WordTrace (prefixWord ++ tailWord_6726148) baseStart_6726148 baseEnd_6726148 := by
    simpa [prefixWord, tailWord_6726148, baseEnd_6726148] using wordTrace_append hprefix tailTrace_6726148
  have hstable : (prefixWord ++ tailWord_6726148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726148).length < 2 ^ (prefixWord ++ tailWord_6726148).sum := by decide
  have hdescent : baseEnd_6726148 < baseStart_6726148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726170 : List Nat := [3, 1, 1, 3, 1, 1, 3, 3, 1, 6]
def baseStart_6726170 : Nat := 118140960795 + 6726170 * 2 ^ 59
def prefixEnd_6726170 : Nat := 4983230072969 + 3 ^ 40 * 6726170 * 2
def baseEnd_6726170 : Nat := 1151252724617351354213971

theorem tailTrace_6726170 : CollatzResearch.WordTrace tailWord_6726170 prefixEnd_6726170 1151252724617351354213971 := by
  unfold tailWord_6726170
  simp only [CollatzResearch.WordTrace]
  refine ⟨61330893510560575806343991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163549049361494868816917309 61330893510560575806343991)
  ·
    refine ⟨91996340265840863709515987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61330893510560575806343991 91996340265840863709515987)
    ·
      refine ⟨137994510398761295564273981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91996340265840863709515987 137994510398761295564273981)
      ·
        refine ⟨51747941399535485836602743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137994510398761295564273981 51747941399535485836602743)
        ·
          refine ⟨77621912099303228754904115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51747941399535485836602743 77621912099303228754904115)
          ·
            refine ⟨116432868148954843132356173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77621912099303228754904115 116432868148954843132356173)
            ·
              refine ⟨43662325555858066174633565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116432868148954843132356173 43662325555858066174633565)
              ·
                refine ⟨16373372083446774815487587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43662325555858066174633565 16373372083446774815487587)
                ·
                  refine ⟨24560058125170162223231381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16373372083446774815487587 24560058125170162223231381)
                  ·
                    refine ⟨1151252724617351354213971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24560058125170162223231381 1151252724617351354213971)
                    ·
                      rfl

theorem cell23_6726170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_6726170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726170 prefixEnd_6726170 := by exact prefixLift 6726170
  have htrace : WordTrace (prefixWord ++ tailWord_6726170) baseStart_6726170 baseEnd_6726170 := by
    simpa [prefixWord, tailWord_6726170, baseEnd_6726170] using wordTrace_append hprefix tailTrace_6726170
  have hstable : (prefixWord ++ tailWord_6726170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726170).length < 2 ^ (prefixWord ++ tailWord_6726170).sum := by decide
  have hdescent : baseEnd_6726170 < baseStart_6726170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726177 : List Nat := [1, 2, 3, 2, 2, 1, 2, 4, 1, 1, 4]
def baseStart_6726177 : Nat := 118140960795 + 6726177 * 2 ^ 59
def prefixEnd_6726177 : Nat := 4983230072969 + 3 ^ 40 * 6726177 * 2
def baseEnd_6726177 : Nat := 3453761768216635535254381

theorem tailTrace_6726177 : CollatzResearch.WordTrace tailWord_6726177 prefixEnd_6726177 3453761768216635535254381 := by
  unfold tailWord_6726177
  simp only [CollatzResearch.WordTrace]
  refine ⟨245323829353216943420880785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163549219568811295613920523 245323829353216943420880785)
  ·
    refine ⟨183992872014912707565660589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245323829353216943420880785 183992872014912707565660589)
    ·
      refine ⟨68997327005592265337122721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183992872014912707565660589 68997327005592265337122721)
      ·
        refine ⟨51747995254194199002842041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68997327005592265337122721 51747995254194199002842041)
        ·
          refine ⟨38810996440645649252131531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51747995254194199002842041 38810996440645649252131531)
          ·
            refine ⟨58216494660968473878197297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38810996440645649252131531 58216494660968473878197297)
            ·
              refine ⟨43662370995726355408647973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58216494660968473878197297 43662370995726355408647973)
              ·
                refine ⟨8186694561698691639121495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43662370995726355408647973 8186694561698691639121495)
                ·
                  refine ⟨12280041842548037458682243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8186694561698691639121495 12280041842548037458682243)
                  ·
                    refine ⟨18420062763822056188023365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12280041842548037458682243 18420062763822056188023365)
                    ·
                      refine ⟨3453761768216635535254381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18420062763822056188023365 3453761768216635535254381)
                      ·
                        rfl

theorem cell23_6726177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_6726177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726177 prefixEnd_6726177 := by exact prefixLift 6726177
  have htrace : WordTrace (prefixWord ++ tailWord_6726177) baseStart_6726177 baseEnd_6726177 := by
    simpa [prefixWord, tailWord_6726177, baseEnd_6726177] using wordTrace_append hprefix tailTrace_6726177
  have hstable : (prefixWord ++ tailWord_6726177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726177).length < 2 ^ (prefixWord ++ tailWord_6726177).sum := by decide
  have hdescent : baseEnd_6726177 < baseStart_6726177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726194 : List Nat := [3, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4]
def baseStart_6726194 : Nat := 118140960795 + 6726194 * 2 ^ 59
def prefixEnd_6726194 : Nat := 4983230072969 + 3 ^ 40 * 6726194 * 2
def baseEnd_6726194 : Nat := 3453770497387761968741803

theorem tailTrace_6726194 : CollatzResearch.WordTrace tailWord_6726194 prefixEnd_6726194 3453770497387761968741803 := by
  unfold tailWord_6726194
  simp only [CollatzResearch.WordTrace]
  refine ⟨61331112348538838831062409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163549632929436903549499757 61331112348538838831062409)
  ·
    refine ⟨45998334261404129123296807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61331112348538838831062409 45998334261404129123296807)
    ·
      refine ⟨68997501392106193684945211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45998334261404129123296807 68997501392106193684945211)
      ·
        refine ⟨103496252088159290527417817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68997501392106193684945211 103496252088159290527417817)
        ·
          refine ⟨77622189066119467895563363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103496252088159290527417817 77622189066119467895563363)
          ·
            refine ⟨116433283599179201843345045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77622189066119467895563363 116433283599179201843345045)
            ·
              refine ⟨5457810168711525086406799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 116433283599179201843345045 5457810168711525086406799)
              ·
                refine ⟨8186715253067287629610199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5457810168711525086406799 8186715253067287629610199)
                ·
                  refine ⟨12280072879600931444415299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8186715253067287629610199 12280072879600931444415299)
                  ·
                    refine ⟨18420109319401397166622949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12280072879600931444415299 18420109319401397166622949)
                    ·
                      refine ⟨3453770497387761968741803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18420109319401397166622949 3453770497387761968741803)
                      ·
                        rfl

theorem cell23_6726194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4].length) (baseStart_6726194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726194 prefixEnd_6726194 := by exact prefixLift 6726194
  have htrace : WordTrace (prefixWord ++ tailWord_6726194) baseStart_6726194 baseEnd_6726194 := by
    simpa [prefixWord, tailWord_6726194, baseEnd_6726194] using wordTrace_append hprefix tailTrace_6726194
  have hstable : (prefixWord ++ tailWord_6726194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726194).length < 2 ^ (prefixWord ++ tailWord_6726194).sum := by decide
  have hdescent : baseEnd_6726194 < baseStart_6726194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726204 : List Nat := [2, 2, 2, 2, 3, 1, 3, 2, 2, 4]
def baseStart_6726204 : Nat := 118140960795 + 6726204 * 2 ^ 59
def prefixEnd_6726204 : Nat := 4983230072969 + 3 ^ 40 * 6726204 * 2
def baseEnd_6726204 : Nat := 1151258544064768976538919

theorem tailTrace_6726204 : CollatzResearch.WordTrace tailWord_6726204 prefixEnd_6726204 1151258544064768976538919 := by
  unfold tailWord_6726204
  simp only [CollatzResearch.WordTrace]
  refine ⟨122662407062059563516056833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163549876082746084688075777 122662407062059563516056833)
  ·
    refine ⟨91996805296544672637042625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122662407062059563516056833 91996805296544672637042625)
    ·
      refine ⟨68997603972408504477781969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91996805296544672637042625 68997603972408504477781969)
      ·
        refine ⟨51748202979306378358336477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68997603972408504477781969 51748202979306378358336477)
        ·
          refine ⟨19405576117239891884376179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51748202979306378358336477 19405576117239891884376179)
          ·
            refine ⟨29108364175859837826564269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19405576117239891884376179 29108364175859837826564269)
            ·
              refine ⟨10915636565947439184961601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29108364175859837826564269 10915636565947439184961601)
              ·
                refine ⟨8186727424460579388721201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10915636565947439184961601 8186727424460579388721201)
                ·
                  refine ⟨6140045568345434541540901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8186727424460579388721201 6140045568345434541540901)
                  ·
                    refine ⟨1151258544064768976538919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6140045568345434541540901 1151258544064768976538919)
                    ·
                      rfl

theorem cell23_6726204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_6726204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726204 prefixEnd_6726204 := by exact prefixLift 6726204
  have htrace : WordTrace (prefixWord ++ tailWord_6726204) baseStart_6726204 baseEnd_6726204 := by
    simpa [prefixWord, tailWord_6726204, baseEnd_6726204] using wordTrace_append hprefix tailTrace_6726204
  have hstable : (prefixWord ++ tailWord_6726204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726204).length < 2 ^ (prefixWord ++ tailWord_6726204).sum := by decide
  have hdescent : baseEnd_6726204 < baseStart_6726204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726214 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_6726214 : Nat := 118140960795 + 6726214 * 2 ^ 59
def prefixEnd_6726214 : Nat := 4983230072969 + 3 ^ 40 * 6726214 * 2
def baseEnd_6726214 : Nat := 3453780767000851890491711

theorem tailTrace_6726214 : CollatzResearch.WordTrace tailWord_6726214 prefixEnd_6726214 3453780767000851890491711 := by
  unfold tailWord_6726214
  simp only [CollatzResearch.WordTrace]
  refine ⟨7666411839190090585624303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 163550119236055265826651797 7666411839190090585624303)
  ·
    refine ⟨11499617758785135878436455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7666411839190090585624303 11499617758785135878436455)
    ·
      refine ⟨17249426638177703817654683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11499617758785135878436455 17249426638177703817654683)
      ·
        refine ⟨25874139957266555726482025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17249426638177703817654683 25874139957266555726482025)
        ·
          refine ⟨19405604967949916794861519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25874139957266555726482025 19405604967949916794861519)
          ·
            refine ⟨29108407451924875192292279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19405604967949916794861519 29108407451924875192292279)
            ·
              refine ⟨43662611177887312788438419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29108407451924875192292279 43662611177887312788438419)
              ·
                refine ⟨65493916766830969182657629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43662611177887312788438419 65493916766830969182657629)
                ·
                  refine ⟨24560218787561613443496611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65493916766830969182657629 24560218787561613443496611)
                  ·
                    refine ⟨36840328181342420165244917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24560218787561613443496611 36840328181342420165244917)
                    ·
                      refine ⟨3453780767000851890491711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36840328181342420165244917 3453780767000851890491711)
                      ·
                        rfl

theorem cell23_6726214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_6726214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726214 prefixEnd_6726214 := by exact prefixLift 6726214
  have htrace : WordTrace (prefixWord ++ tailWord_6726214) baseStart_6726214 baseEnd_6726214 := by
    simpa [prefixWord, tailWord_6726214, baseEnd_6726214] using wordTrace_append hprefix tailTrace_6726214
  have hstable : (prefixWord ++ tailWord_6726214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726214).length < 2 ^ (prefixWord ++ tailWord_6726214).sum := by decide
  have hdescent : baseEnd_6726214 < baseStart_6726214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726240 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 5]
def baseStart_6726240 : Nat := 118140960795 + 6726240 * 2 ^ 59
def prefixEnd_6726240 : Nat := 4983230072969 + 3 ^ 40 * 6726240 * 2
def baseEnd_6726240 : Nat := 3453794117497868788766591

theorem tailTrace_6726240 : CollatzResearch.WordTrace tailWord_6726240 prefixEnd_6726240 3453794117497868788766591 := by
  unfold tailWord_6726240
  simp only [CollatzResearch.WordTrace]
  refine ⟨122663063575994352590212087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163550751434659136786949449 122663063575994352590212087)
  ·
    refine ⟨183994595363991528885318131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122663063575994352590212087 183994595363991528885318131)
    ·
      refine ⟨275991893045987293327977197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183994595363991528885318131 275991893045987293327977197)
      ·
        refine ⟨103496959892245234997991449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275991893045987293327977197 103496959892245234997991449)
        ·
          refine ⟨77622719919183926248493587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103496959892245234997991449 77622719919183926248493587)
          ·
            refine ⟨116434079878775889372740381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77622719919183926248493587 116434079878775889372740381)
            ·
              refine ⟨43662779954540958514777643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116434079878775889372740381 43662779954540958514777643)
              ·
                refine ⟨65494169931811437772166465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43662779954540958514777643 65494169931811437772166465)
                ·
                  refine ⟨49120627448858578329124849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65494169931811437772166465 49120627448858578329124849)
                  ·
                    refine ⟨36840470586643933746843637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49120627448858578329124849 36840470586643933746843637)
                    ·
                      refine ⟨3453794117497868788766591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36840470586643933746843637 3453794117497868788766591)
                      ·
                        rfl

theorem cell23_6726240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_6726240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726240 prefixEnd_6726240 := by exact prefixLift 6726240
  have htrace : WordTrace (prefixWord ++ tailWord_6726240) baseStart_6726240 baseEnd_6726240 := by
    simpa [prefixWord, tailWord_6726240, baseEnd_6726240] using wordTrace_append hprefix tailTrace_6726240
  have hstable : (prefixWord ++ tailWord_6726240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726240).length < 2 ^ (prefixWord ++ tailWord_6726240).sum := by decide
  have hdescent : baseEnd_6726240 < baseStart_6726240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726245 : List Nat := [1, 3, 1, 3, 4, 2, 1, 3, 1, 2, 2]
def baseStart_6726245 : Nat := 118140960795 + 6726245 * 2 ^ 59
def prefixEnd_6726245 : Nat := 4983230072969 + 3 ^ 40 * 6726245 * 2
def baseEnd_6726245 : Nat := 3453796684901141269204069

theorem tailTrace_6726245 : CollatzResearch.WordTrace tailWord_6726245 prefixEnd_6726245 3453796684901141269204069 := by
  unfold tailWord_6726245
  simp only [CollatzResearch.WordTrace]
  refine ⟨245326309516970591034356189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163550873011313727356237459 245326309516970591034356189)
  ·
    refine ⟨91997366068863971637883571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245326309516970591034356189 91997366068863971637883571)
    ·
      refine ⟨137996049103295957456825357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91997366068863971637883571 137996049103295957456825357)
      ·
        refine ⟨51748518413735984046309509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137996049103295957456825357 51748518413735984046309509)
        ·
          refine ⟨9702847202575497008683033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51748518413735984046309509 9702847202575497008683033)
          ·
            refine ⟨7277135401931622756512275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9702847202575497008683033 7277135401931622756512275)
            ·
              refine ⟨10915703102897434134768413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7277135401931622756512275 10915703102897434134768413)
              ·
                refine ⟨4093388663586537800538155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10915703102897434134768413 4093388663586537800538155)
                ·
                  refine ⟨6140082995379806700807233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4093388663586537800538155 6140082995379806700807233)
                  ·
                    refine ⟨4605062246534855025605425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6140082995379806700807233 4605062246534855025605425)
                    ·
                      refine ⟨3453796684901141269204069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4605062246534855025605425 3453796684901141269204069)
                      ·
                        rfl

theorem cell23_6726245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_6726245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726245 prefixEnd_6726245 := by exact prefixLift 6726245
  have htrace : WordTrace (prefixWord ++ tailWord_6726245) baseStart_6726245 baseEnd_6726245 := by
    simpa [prefixWord, tailWord_6726245, baseEnd_6726245] using wordTrace_append hprefix tailTrace_6726245
  have hstable : (prefixWord ++ tailWord_6726245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726245).length < 2 ^ (prefixWord ++ tailWord_6726245).sum := by decide
  have hdescent : baseEnd_6726245 < baseStart_6726245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726262 : List Nat := [5, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2]
def baseStart_6726262 : Nat := 118140960795 + 6726262 * 2 ^ 59
def prefixEnd_6726262 : Nat := 4983230072969 + 3 ^ 40 * 6726262 * 2
def baseEnd_6726262 : Nat := 3453805414072267702691491

theorem tailTrace_6726262 : CollatzResearch.WordTrace tailWord_6726262 prefixEnd_6726262 3453805414072267702691491 := by
  unfold tailWord_6726262
  simp only [CollatzResearch.WordTrace]
  refine ⟨15332933097369312683607815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163551286371939335291816693 15332933097369312683607815)
  ·
    refine ⟨22999399646053969025411723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15332933097369312683607815 22999399646053969025411723)
    ·
      refine ⟨34499099469080953538117585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22999399646053969025411723 34499099469080953538117585)
      ·
        refine ⟨25874324601810715153588189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34499099469080953538117585 25874324601810715153588189)
        ·
          refine ⟨9702871725679018182595571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25874324601810715153588189 9702871725679018182595571)
          ·
            refine ⟨14554307588518527273893357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9702871725679018182595571 14554307588518527273893357)
            ·
              refine ⟨5457865345694447727710009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14554307588518527273893357 5457865345694447727710009)
              ·
                refine ⟨4093399009270835795782507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5457865345694447727710009 4093399009270835795782507)
                ·
                  refine ⟨6140098513906253693673761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4093399009270835795782507 6140098513906253693673761)
                  ·
                    refine ⟨4605073885429690270255321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6140098513906253693673761 4605073885429690270255321)
                    ·
                      refine ⟨3453805414072267702691491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4605073885429690270255321 3453805414072267702691491)
                      ·
                        rfl

theorem cell23_6726262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_6726262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726262 prefixEnd_6726262 := by exact prefixLift 6726262
  have htrace : WordTrace (prefixWord ++ tailWord_6726262) baseStart_6726262 baseEnd_6726262 := by
    simpa [prefixWord, tailWord_6726262, baseEnd_6726262] using wordTrace_append hprefix tailTrace_6726262
  have hstable : (prefixWord ++ tailWord_6726262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726262).length < 2 ^ (prefixWord ++ tailWord_6726262).sum := by decide
  have hdescent : baseEnd_6726262 < baseStart_6726262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726267 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 5, 4, 2]
def baseStart_6726267 : Nat := 118140960795 + 6726267 * 2 ^ 59
def prefixEnd_6726267 : Nat := 4983230072969 + 3 ^ 40 * 6726267 * 2
def baseEnd_6726267 : Nat := 3453807981475540183128967

theorem tailTrace_6726267 : CollatzResearch.WordTrace tailWord_6726267 prefixEnd_6726267 3453807981475540183128967 := by
  unfold tailWord_6726267
  simp only [CollatzResearch.WordTrace]
  refine ⟨245327111922890888791657055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163551407948593925861104703 245327111922890888791657055)
  ·
    refine ⟨367990667884336333187485583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245327111922890888791657055 367990667884336333187485583)
    ·
      refine ⟨551986001826504499781228375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367990667884336333187485583 551986001826504499781228375)
      ·
        refine ⟨827979002739756749671842563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551986001826504499781228375 827979002739756749671842563)
        ·
          refine ⟨1241968504109635124507763845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 827979002739756749671842563 1241968504109635124507763845)
          ·
            refine ⟨232869094520556585845205721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1241968504109635124507763845 232869094520556585845205721)
            ·
              refine ⟨174651820890417439383904291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232869094520556585845205721 174651820890417439383904291)
              ·
                refine ⟨261977731335626159075856437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174651820890417439383904291 261977731335626159075856437)
                ·
                  refine ⟨24560412312714952413361541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 261977731335626159075856437 24560412312714952413361541)
                  ·
                    refine ⟨4605077308634053577505289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24560412312714952413361541 4605077308634053577505289)
                    ·
                      refine ⟨3453807981475540183128967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4605077308634053577505289 3453807981475540183128967)
                      ·
                        rfl

theorem cell23_6726267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 4, 2].length) (baseStart_6726267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726267 prefixEnd_6726267 := by exact prefixLift 6726267
  have htrace : WordTrace (prefixWord ++ tailWord_6726267) baseStart_6726267 baseEnd_6726267 := by
    simpa [prefixWord, tailWord_6726267, baseEnd_6726267] using wordTrace_append hprefix tailTrace_6726267
  have hstable : (prefixWord ++ tailWord_6726267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726267).length < 2 ^ (prefixWord ++ tailWord_6726267).sum := by decide
  have hdescent : baseEnd_6726267 < baseStart_6726267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726284 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 6, 2, 2]
def baseStart_6726284 : Nat := 118140960795 + 6726284 * 2 ^ 59
def prefixEnd_6726284 : Nat := 4983230072969 + 3 ^ 40 * 6726284 * 2
def baseEnd_6726284 : Nat := 3453816710646666616616389

theorem tailTrace_6726284 : CollatzResearch.WordTrace tailWord_6726284 prefixEnd_6726284 3453816710646666616616389 := by
  unfold tailWord_6726284
  simp only [CollatzResearch.WordTrace]
  refine ⟨122663865981914650347512953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163551821309219533796683937 122663865981914650347512953)
  ·
    refine ⟨91997899486435987760634715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122663865981914650347512953 91997899486435987760634715)
    ·
      refine ⟨137996849229653981640952073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91997899486435987760634715 137996849229653981640952073)
      ·
        refine ⟨103497636922240486230714055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137996849229653981640952073 103497636922240486230714055)
        ·
          refine ⟨155246455383360729346071083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103497636922240486230714055 155246455383360729346071083)
          ·
            refine ⟨232869683075041094019106625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155246455383360729346071083 232869683075041094019106625)
            ·
              refine ⟨174652262306280820514329969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232869683075041094019106625 174652262306280820514329969)
              ·
                refine ⟨130989196729710615385747477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174652262306280820514329969 130989196729710615385747477)
                ·
                  refine ⟨6140118596705185096206913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130989196729710615385747477 6140118596705185096206913)
                  ·
                    refine ⟨4605088947528888822155185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6140118596705185096206913 4605088947528888822155185)
                    ·
                      refine ⟨3453816710646666616616389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4605088947528888822155185 3453816710646666616616389)
                      ·
                        rfl

theorem cell23_6726284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 6, 2, 2].length) (baseStart_6726284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726284 prefixEnd_6726284 := by exact prefixLift 6726284
  have htrace : WordTrace (prefixWord ++ tailWord_6726284) baseStart_6726284 baseEnd_6726284 := by
    simpa [prefixWord, tailWord_6726284, baseEnd_6726284] using wordTrace_append hprefix tailTrace_6726284
  have hstable : (prefixWord ++ tailWord_6726284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726284).length < 2 ^ (prefixWord ++ tailWord_6726284).sum := by decide
  have hdescent : baseEnd_6726284 < baseStart_6726284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726320 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 3, 7]
def baseStart_6726320 : Nat := 118140960795 + 6726320 * 2 ^ 59
def prefixEnd_6726320 : Nat := 4983230072969 + 3 ^ 40 * 6726320 * 2
def baseEnd_6726320 : Nat := 1151278398650076158588741

theorem tailTrace_6726320 : CollatzResearch.WordTrace tailWord_6726320 prefixEnd_6726320 1151278398650076158588741 := by
  unfold tailWord_6726320
  simp only [CollatzResearch.WordTrace]
  refine ⟨122664522495849439421668207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163552696661132585895557609 122664522495849439421668207)
  ·
    refine ⟨183996783743774159132502311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122664522495849439421668207 183996783743774159132502311)
    ·
      refine ⟨275995175615661238698753467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183996783743774159132502311 275995175615661238698753467)
      ·
        refine ⟨413992763423491858048130201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275995175615661238698753467 413992763423491858048130201)
        ·
          refine ⟨310494572567618893536097651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413992763423491858048130201 310494572567618893536097651)
          ·
            refine ⟨465741858851428340304146477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310494572567618893536097651 465741858851428340304146477)
            ·
              refine ⟨174653197069285627614054929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 465741858851428340304146477 174653197069285627614054929)
              ·
                refine ⟨130989897801964220710541197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174653197069285627614054929 130989897801964220710541197)
                ·
                  refine ⟨49121211675736582766452949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130989897801964220710541197 49121211675736582766452949)
                  ·
                    refine ⟨1151278398650076158588741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49121211675736582766452949 1151278398650076158588741)
                    ·
                      rfl

theorem cell23_6726320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 3, 7].length) (baseStart_6726320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726320 prefixEnd_6726320 := by exact prefixLift 6726320
  have htrace : WordTrace (prefixWord ++ tailWord_6726320) baseStart_6726320 baseEnd_6726320 := by
    simpa [prefixWord, tailWord_6726320, baseEnd_6726320] using wordTrace_append hprefix tailTrace_6726320
  have hstable : (prefixWord ++ tailWord_6726320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726320).length < 2 ^ (prefixWord ++ tailWord_6726320).sum := by decide
  have hdescent : baseEnd_6726320 < baseStart_6726320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726334 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3]
def baseStart_6726334 : Nat := 118140960795 + 6726334 * 2 ^ 59
def prefixEnd_6726334 : Nat := 4983230072969 + 3 ^ 40 * 6726334 * 2
def baseEnd_6726334 : Nat := 3453842384679391420991159

theorem tailTrace_6726334 : CollatzResearch.WordTrace tailWord_6726334 prefixEnd_6726334 3453842384679391420991159 := by
  unfold tailWord_6726334
  simp only [CollatzResearch.WordTrace]
  refine ⟨30666194451706019904293257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163553037075765439489564037 30666194451706019904293257)
  ·
    refine ⟨22999645838779514928219943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30666194451706019904293257 22999645838779514928219943)
    ·
      refine ⟨34499468758169272392329915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22999645838779514928219943 34499468758169272392329915)
      ·
        refine ⟨51749203137253908588494873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34499468758169272392329915 51749203137253908588494873)
        ·
          refine ⟨38811902352940431441371155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51749203137253908588494873 38811902352940431441371155)
          ·
            refine ⟨58217853529410647162056733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38811902352940431441371155 58217853529410647162056733)
            ·
              refine ⟨21831695073528992685771275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58217853529410647162056733 21831695073528992685771275)
              ·
                refine ⟨32747542610293489028656913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21831695073528992685771275 32747542610293489028656913)
                ·
                  refine ⟨24560656957720116771492685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32747542610293489028656913 24560656957720116771492685)
                  ·
                    refine ⟨9210246359145043789309757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24560656957720116771492685 9210246359145043789309757)
                    ·
                      refine ⟨3453842384679391420991159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9210246359145043789309757 3453842384679391420991159)
                      ·
                        rfl

theorem cell23_6726334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_6726334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726334 prefixEnd_6726334 := by exact prefixLift 6726334
  have htrace : WordTrace (prefixWord ++ tailWord_6726334) baseStart_6726334 baseEnd_6726334 := by
    simpa [prefixWord, tailWord_6726334, baseEnd_6726334] using wordTrace_append hprefix tailTrace_6726334
  have hstable : (prefixWord ++ tailWord_6726334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726334).length < 2 ^ (prefixWord ++ tailWord_6726334).sum := by decide
  have hdescent : baseEnd_6726334 < baseStart_6726334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726354 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 1, 7]
def baseStart_6726354 : Nat := 118140960795 + 6726354 * 2 ^ 59
def prefixEnd_6726354 : Nat := 4983230072969 + 3 ^ 40 * 6726354 * 2
def baseEnd_6726354 : Nat := 1151284218097493780913689

theorem tailTrace_6726354 : CollatzResearch.WordTrace tailWord_6726354 prefixEnd_6726354 1151284218097493780913689 := by
  unfold tailWord_6726354
  simp only [CollatzResearch.WordTrace]
  refine ⟨61332571268393925662518529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163553523382383801766716077 61332571268393925662518529)
  ·
    refine ⟨45999428451295444246888897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61332571268393925662518529 45999428451295444246888897)
    ·
      refine ⟨34499571338471583185166673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45999428451295444246888897 34499571338471583185166673)
      ·
        refine ⟨25874678503853687388875005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34499571338471583185166673 25874678503853687388875005)
        ·
          refine ⟨9703004438945132770828127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25874678503853687388875005 9703004438945132770828127)
          ·
            refine ⟨14554506658417699156242191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9703004438945132770828127 14554506658417699156242191)
            ·
              refine ⟨21831759987626548734363287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14554506658417699156242191 21831759987626548734363287)
              ·
                refine ⟨32747639981439823101544931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21831759987626548734363287 32747639981439823101544931)
                ·
                  refine ⟨49121459972159734652317397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32747639981439823101544931 49121459972159734652317397)
                  ·
                    refine ⟨1151284218097493780913689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49121459972159734652317397 1151284218097493780913689)
                    ·
                      rfl

theorem cell23_6726354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_6726354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726354 prefixEnd_6726354 := by exact prefixLift 6726354
  have htrace : WordTrace (prefixWord ++ tailWord_6726354) baseStart_6726354 baseEnd_6726354 := by
    simpa [prefixWord, tailWord_6726354, baseEnd_6726354] using wordTrace_append hprefix tailTrace_6726354
  have hstable : (prefixWord ++ tailWord_6726354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726354).length < 2 ^ (prefixWord ++ tailWord_6726354).sum := by decide
  have hdescent : baseEnd_6726354 < baseStart_6726354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726384 : List Nat := [2, 1, 1, 1, 3, 1, 6, 1, 3, 4]
def baseStart_6726384 : Nat := 118140960795 + 6726384 * 2 ^ 59
def prefixEnd_6726384 : Nat := 4983230072969 + 3 ^ 40 * 6726384 * 2
def baseEnd_6726384 : Nat := 1151289352904038741788643

theorem tailTrace_6726384 : CollatzResearch.WordTrace tailWord_6726384 prefixEnd_6726384 1151289352904038741788643 := by
  unfold tailWord_6726384
  simp only [CollatzResearch.WordTrace]
  refine ⟨122665689631733508886833103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163554252842311345182444137 122665689631733508886833103)
  ·
    refine ⟨183998534447600263330249655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122665689631733508886833103 183998534447600263330249655)
    ·
      refine ⟨275997801671400394995374483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183998534447600263330249655 275997801671400394995374483)
      ·
        refine ⟨413996702507100592493061725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275997801671400394995374483 413996702507100592493061725)
        ·
          refine ⟨155248763440162722184898147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 413996702507100592493061725 155248763440162722184898147)
          ·
            refine ⟨232873145160244083277347221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155248763440162722184898147 232873145160244083277347221)
            ·
              refine ⟨10915928679386441403625651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 232873145160244083277347221 10915928679386441403625651)
              ·
                refine ⟨16373893019079662105438477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10915928679386441403625651 16373893019079662105438477)
                ·
                  refine ⟨6140209882154873289539429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16373893019079662105438477 6140209882154873289539429)
                  ·
                    refine ⟨1151289352904038741788643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6140209882154873289539429 1151289352904038741788643)
                    ·
                      rfl

theorem cell23_6726384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 3, 4].length) (baseStart_6726384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726384 prefixEnd_6726384 := by exact prefixLift 6726384
  have htrace : WordTrace (prefixWord ++ tailWord_6726384) baseStart_6726384 baseEnd_6726384 := by
    simpa [prefixWord, tailWord_6726384, baseEnd_6726384] using wordTrace_append hprefix tailTrace_6726384
  have hstable : (prefixWord ++ tailWord_6726384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726384).length < 2 ^ (prefixWord ++ tailWord_6726384).sum := by decide
  have hdescent : baseEnd_6726384 < baseStart_6726384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726461 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 3, 5]
def baseStart_6726461 : Nat := 118140960795 + 6726461 * 2 ^ 59
def prefixEnd_6726461 : Nat := 4983230072969 + 3 ^ 40 * 6726461 * 2
def baseEnd_6726461 : Nat := 1151302532240837474701025

theorem tailTrace_6726461 : CollatzResearch.WordTrace tailWord_6726461 prefixEnd_6726461 1151302532240837474701025 := by
  unfold tailWord_6726461
  simp only [CollatzResearch.WordTrace]
  refine ⟨245334187684188059924219237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163556125122792039949479491 245334187684188059924219237)
  ·
    refine ⟨46000160190785261235791107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245334187684188059924219237 46000160190785261235791107)
    ·
      refine ⟨69000240286177891853686661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46000160190785261235791107 69000240286177891853686661)
      ·
        refine ⟨12937545053658354722566249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69000240286177891853686661 12937545053658354722566249)
        ·
          refine ⟨9703158790243766041924687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12937545053658354722566249 9703158790243766041924687)
          ·
            refine ⟨14554738185365649062887031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9703158790243766041924687 14554738185365649062887031)
            ·
              refine ⟨21832107278048473594330547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14554738185365649062887031 21832107278048473594330547)
              ·
                refine ⟨32748160917072710391495821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21832107278048473594330547 32748160917072710391495821)
                ·
                  refine ⟨12280560343902266396810933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32748160917072710391495821 12280560343902266396810933)
                  ·
                    refine ⟨1151302532240837474701025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12280560343902266396810933 1151302532240837474701025)
                    ·
                      rfl

theorem cell23_6726461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_6726461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726461 prefixEnd_6726461 := by exact prefixLift 6726461
  have htrace : WordTrace (prefixWord ++ tailWord_6726461) baseStart_6726461 baseEnd_6726461 := by
    simpa [prefixWord, tailWord_6726461, baseEnd_6726461] using wordTrace_append hprefix tailTrace_6726461
  have hstable : (prefixWord ++ tailWord_6726461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726461).length < 2 ^ (prefixWord ++ tailWord_6726461).sum := by decide
  have hdescent : baseEnd_6726461 < baseStart_6726461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726464 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 2, 6, 2]
def baseStart_6726464 : Nat := 118140960795 + 6726464 * 2 ^ 59
def prefixEnd_6726464 : Nat := 4983230072969 + 3 ^ 40 * 6726464 * 2
def baseEnd_6726464 : Nat := 3453909137164475912365561

theorem tailTrace_6726464 : CollatzResearch.WordTrace tailWord_6726464 prefixEnd_6726464 3453909137164475912365561 := by
  unfold tailWord_6726464
  simp only [CollatzResearch.WordTrace]
  refine ⟨122667148551588595718289223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163556198068784794291052297 122667148551588595718289223)
  ·
    refine ⟨184000722827382893577433835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122667148551588595718289223 184000722827382893577433835)
    ·
      refine ⟨276001084241074340366150753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184000722827382893577433835 276001084241074340366150753)
      ·
        refine ⟨207000813180805755274613065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276001084241074340366150753 207000813180805755274613065)
        ·
          refine ⟨155250609885604316455959799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207000813180805755274613065 155250609885604316455959799)
          ·
            refine ⟨232875914828406474683939699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155250609885604316455959799 232875914828406474683939699)
            ·
              refine ⟨349313872242609712025909549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232875914828406474683939699 349313872242609712025909549)
              ·
                refine ⟨130992702090978642009716081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 349313872242609712025909549 130992702090978642009716081)
                ·
                  refine ⟨98244526568233981507287061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130992702090978642009716081 98244526568233981507287061)
                  ·
                    refine ⟨4605212182885967883154081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98244526568233981507287061 4605212182885967883154081)
                    ·
                      refine ⟨3453909137164475912365561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4605212182885967883154081 3453909137164475912365561)
                      ·
                        rfl

theorem cell23_6726464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 6, 2].length) (baseStart_6726464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726464 prefixEnd_6726464 := by exact prefixLift 6726464
  have htrace : WordTrace (prefixWord ++ tailWord_6726464) baseStart_6726464 baseEnd_6726464 := by
    simpa [prefixWord, tailWord_6726464, baseEnd_6726464] using wordTrace_append hprefix tailTrace_6726464
  have hstable : (prefixWord ++ tailWord_6726464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726464).length < 2 ^ (prefixWord ++ tailWord_6726464).sum := by decide
  have hdescent : baseEnd_6726464 < baseStart_6726464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726474 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 4, 4]
def baseStart_6726474 : Nat := 118140960795 + 6726474 * 2 ^ 59
def prefixEnd_6726474 : Nat := 4983230072969 + 3 ^ 40 * 6726474 * 2
def baseEnd_6726474 : Nat := 1151304757323673624413505

theorem tailTrace_6726474 : CollatzResearch.WordTrace tailWord_6726474 prefixEnd_6726474 1151304757323673624413505 := by
  unfold tailWord_6726474
  simp only [CollatzResearch.WordTrace]
  refine ⟨61333665458285240786110619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163556441222093975429628317 61333665458285240786110619)
  ·
    refine ⟨92000498187427861179165929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61333665458285240786110619 92000498187427861179165929)
    ·
      refine ⟨69000373640570895884374447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92000498187427861179165929 69000373640570895884374447)
      ·
        refine ⟨103500560460856343826561671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69000373640570895884374447 103500560460856343826561671)
        ·
          refine ⟨155250840691284515739842507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103500560460856343826561671 155250840691284515739842507)
          ·
            refine ⟨232876261036926773609763761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155250840691284515739842507 232876261036926773609763761)
            ·
              refine ⟨174657195777695080207322821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232876261036926773609763761 174657195777695080207322821)
              ·
                refine ⟨32748224208317827538873029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174657195777695080207322821 32748224208317827538873029)
                ·
                  refine ⟨6140292039059592663538693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32748224208317827538873029 6140292039059592663538693)
                  ·
                    refine ⟨1151304757323673624413505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6140292039059592663538693 1151304757323673624413505)
                    ·
                      rfl

theorem cell23_6726474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_6726474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726474 prefixEnd_6726474 := by exact prefixLift 6726474
  have htrace : WordTrace (prefixWord ++ tailWord_6726474) baseStart_6726474 baseEnd_6726474 := by
    simpa [prefixWord, tailWord_6726474, baseEnd_6726474] using wordTrace_append hprefix tailTrace_6726474
  have hstable : (prefixWord ++ tailWord_6726474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726474).length < 2 ^ (prefixWord ++ tailWord_6726474).sum := by decide
  have hdescent : baseEnd_6726474 < baseStart_6726474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726487 : List Nat := [1, 1, 3, 2, 4, 12]
def baseStart_6726487 : Nat := 118140960795 + 6726487 * 2 ^ 59
def prefixEnd_6726487 : Nat := 4983230072969 + 3 ^ 40 * 6726487 * 2
def baseEnd_6726487 : Nat := 14213666449463083631185

theorem tailTrace_6726487 : CollatzResearch.WordTrace tailWord_6726487 prefixEnd_6726487 14213666449463083631185 := by
  unfold tailWord_6726487
  simp only [CollatzResearch.WordTrace]
  refine ⟨245335135982093866364665715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163556757321395910909777143 245335135982093866364665715)
  ·
    refine ⟨368002703973140799546998573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245335135982093866364665715 368002703973140799546998573)
    ·
      refine ⟨138001013989927799830124465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368002703973140799546998573 138001013989927799830124465)
      ·
        refine ⟨103500760492445849872593349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138001013989927799830124465 103500760492445849872593349)
        ·
          refine ⟨19406392592333596851111253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103500760492445849872593349 19406392592333596851111253)
          ·
            refine ⟨14213666449463083631185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 19406392592333596851111253 14213666449463083631185)
            ·
              rfl

theorem cell23_6726487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 12].length) (baseStart_6726487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726487 prefixEnd_6726487 := by exact prefixLift 6726487
  have htrace : WordTrace (prefixWord ++ tailWord_6726487) baseStart_6726487 baseEnd_6726487 := by
    simpa [prefixWord, tailWord_6726487, baseEnd_6726487] using wordTrace_append hprefix tailTrace_6726487
  have hstable : (prefixWord ++ tailWord_6726487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726487).length < 2 ^ (prefixWord ++ tailWord_6726487).sum := by decide
  have hdescent : baseEnd_6726487 < baseStart_6726487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726492 : List Nat := [2, 2, 4, 2, 1, 1, 4, 2, 1, 1, 3]
def baseStart_6726492 : Nat := 118140960795 + 6726492 * 2 ^ 59
def prefixEnd_6726492 : Nat := 4983230072969 + 3 ^ 40 * 6726492 * 2
def baseEnd_6726492 : Nat := 3453923514622801802815433

theorem tailTrace_6726492 : CollatzResearch.WordTrace tailWord_6726492 prefixEnd_6726492 3453923514622801802815433 := by
  unfold tailWord_6726492
  simp only [CollatzResearch.WordTrace]
  refine ⟨122667659173537876109298865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163556878898050501479065153 122667659173537876109298865)
  ·
    refine ⟨92000744380153407081974149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122667659173537876109298865 92000744380153407081974149)
    ·
      refine ⟨17250139571278763827870153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92000744380153407081974149 17250139571278763827870153)
      ·
        refine ⟨12937604678459072870902615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17250139571278763827870153 12937604678459072870902615)
        ·
          refine ⟨19406407017688609306353923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12937604678459072870902615 19406407017688609306353923)
          ·
            refine ⟨29109610526532913959530885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19406407017688609306353923 29109610526532913959530885)
            ·
              refine ⟨5458051973724921367412041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29109610526532913959530885 5458051973724921367412041)
              ·
                refine ⟨4093538980293691025559031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5458051973724921367412041 4093538980293691025559031)
                ·
                  refine ⟨6140308470440536538338547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4093538980293691025559031 6140308470440536538338547)
                  ·
                    refine ⟨9210462705660804807507821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6140308470440536538338547 9210462705660804807507821)
                    ·
                      refine ⟨3453923514622801802815433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9210462705660804807507821 3453923514622801802815433)
                      ·
                        rfl

theorem cell23_6726492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_6726492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726492 prefixEnd_6726492 := by exact prefixLift 6726492
  have htrace : WordTrace (prefixWord ++ tailWord_6726492) baseStart_6726492 baseEnd_6726492 := by
    simpa [prefixWord, tailWord_6726492, baseEnd_6726492] using wordTrace_append hprefix tailTrace_6726492
  have hstable : (prefixWord ++ tailWord_6726492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726492).length < 2 ^ (prefixWord ++ tailWord_6726492).sum := by decide
  have hdescent : baseEnd_6726492 < baseStart_6726492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726497 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 2, 2, 7]
def baseStart_6726497 : Nat := 118140960795 + 6726497 * 2 ^ 59
def prefixEnd_6726497 : Nat := 4983230072969 + 3 ^ 40 * 6726497 * 2
def baseEnd_6726497 : Nat := 3453926082026074283252909

theorem tailTrace_6726497 : CollatzResearch.WordTrace tailWord_6726497 prefixEnd_6726497 3453926082026074283252909 := by
  unfold tailWord_6726497
  simp only [CollatzResearch.WordTrace]
  refine ⟨245335500712057638072529745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163557000474705092048353163 245335500712057638072529745)
  ·
    refine ⟨184001625534043228554397309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245335500712057638072529745 184001625534043228554397309)
    ·
      refine ⟨69000609575266210707898991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184001625534043228554397309 69000609575266210707898991)
      ·
        refine ⟨103500914362899316061848487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69000609575266210707898991 103500914362899316061848487)
        ·
          refine ⟨155251371544348974092772731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103500914362899316061848487 155251371544348974092772731)
          ·
            refine ⟨232877057316523461139159097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155251371544348974092772731 232877057316523461139159097)
            ·
              refine ⟨174657792987392595854369323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232877057316523461139159097 174657792987392595854369323)
              ·
                refine ⟨261986689481088893781553985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174657792987392595854369323 261986689481088893781553985)
                ·
                  refine ⟨196490017110816670336165489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261986689481088893781553985 196490017110816670336165489)
                  ·
                    refine ⟨147367512833112502752124117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 196490017110816670336165489 147367512833112502752124117)
                    ·
                      refine ⟨3453926082026074283252909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 147367512833112502752124117 3453926082026074283252909)
                      ·
                        rfl

theorem cell23_6726497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_6726497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726497 prefixEnd_6726497 := by exact prefixLift 6726497
  have htrace : WordTrace (prefixWord ++ tailWord_6726497) baseStart_6726497 baseEnd_6726497 := by
    simpa [prefixWord, tailWord_6726497, baseEnd_6726497] using wordTrace_append hprefix tailTrace_6726497
  have hstable : (prefixWord ++ tailWord_6726497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726497).length < 2 ^ (prefixWord ++ tailWord_6726497).sum := by decide
  have hdescent : baseEnd_6726497 < baseStart_6726497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726504 : List Nat := [2, 1, 4, 2, 1, 2, 3, 8]
def baseStart_6726504 : Nat := 118140960795 + 6726504 * 2 ^ 59
def prefixEnd_6726504 : Nat := 4983230072969 + 3 ^ 40 * 6726504 * 2
def baseEnd_6726504 : Nat := 127923321347802065032051

theorem tailTrace_6726504 : CollatzResearch.WordTrace tailWord_6726504 prefixEnd_6726504 127923321347802065032051 := by
  unfold tailWord_6726504
  simp only [CollatzResearch.WordTrace]
  refine ⟨122667878011516139134017283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163557170682021518845356377 122667878011516139134017283)
  ·
    refine ⟨184001817017274208701025925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122667878011516139134017283 184001817017274208701025925)
    ·
      refine ⟨34500340690738914131442361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184001817017274208701025925 34500340690738914131442361)
      ·
        refine ⟨25875255518054185598581771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34500340690738914131442361 25875255518054185598581771)
        ·
          refine ⟨38812883277081278397872657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25875255518054185598581771 38812883277081278397872657)
          ·
            refine ⟨29109662457810958798404493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38812883277081278397872657 29109662457810958798404493)
            ·
              refine ⟨10916123421679109549401685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29109662457810958798404493 10916123421679109549401685)
              ·
                refine ⟨127923321347802065032051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10916123421679109549401685 127923321347802065032051)
                ·
                  rfl

theorem cell23_6726504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 8].length) (baseStart_6726504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726504 prefixEnd_6726504 := by exact prefixLift 6726504
  have htrace : WordTrace (prefixWord ++ tailWord_6726504) baseStart_6726504 baseEnd_6726504 := by
    simpa [prefixWord, tailWord_6726504, baseEnd_6726504] using wordTrace_append hprefix tailTrace_6726504
  have hstable : (prefixWord ++ tailWord_6726504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726504).length < 2 ^ (prefixWord ++ tailWord_6726504).sum := by decide
  have hdescent : baseEnd_6726504 < baseStart_6726504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726507 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 6]
def baseStart_6726507 : Nat := 118140960795 + 6726507 * 2 ^ 59
def prefixEnd_6726507 : Nat := 4983230072969 + 3 ^ 40 * 6726507 * 2
def baseEnd_6726507 : Nat := 3453931216832619244127863

theorem tailTrace_6726507 : CollatzResearch.WordTrace tailWord_6726507 prefixEnd_6726507 3453931216832619244127863 := by
  unfold tailWord_6726507
  simp only [CollatzResearch.WordTrace]
  refine ⟨245335865442021409780393775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163557243628014273186929183 245335865442021409780393775)
  ·
    refine ⟨368003798163032114670590663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245335865442021409780393775 368003798163032114670590663)
    ·
      refine ⟨552005697244548172005885995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368003798163032114670590663 552005697244548172005885995)
      ·
        refine ⟨828008545866822258008828993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552005697244548172005885995 828008545866822258008828993)
        ·
          refine ⟨621006409400116693506621745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 828008545866822258008828993 621006409400116693506621745)
          ·
            refine ⟨465754807050087520129966309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 621006409400116693506621745 465754807050087520129966309)
            ·
              refine ⟨87329026321891410024368683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 465754807050087520129966309 87329026321891410024368683)
              ·
                refine ⟨130993539482837115036553025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87329026321891410024368683 130993539482837115036553025)
                ·
                  refine ⟨98245154612127836277414769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130993539482837115036553025 98245154612127836277414769)
                  ·
                    refine ⟨73683865959095877208061077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98245154612127836277414769 73683865959095877208061077)
                    ·
                      refine ⟨3453931216832619244127863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73683865959095877208061077 3453931216832619244127863)
                      ·
                        rfl

theorem cell23_6726507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 6].length) (baseStart_6726507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726507 prefixEnd_6726507 := by exact prefixLift 6726507
  have htrace : WordTrace (prefixWord ++ tailWord_6726507) baseStart_6726507 baseEnd_6726507 := by
    simpa [prefixWord, tailWord_6726507, baseEnd_6726507] using wordTrace_append hprefix tailTrace_6726507
  have hstable : (prefixWord ++ tailWord_6726507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726507).length < 2 ^ (prefixWord ++ tailWord_6726507).sum := by decide
  have hdescent : baseEnd_6726507 < baseStart_6726507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726518 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3]
def baseStart_6726518 : Nat := 118140960795 + 6726518 * 2 ^ 59
def prefixEnd_6726518 : Nat := 4983230072969 + 3 ^ 40 * 6726518 * 2
def baseEnd_6726518 : Nat := 3453936865119818701090313

theorem tailTrace_6726518 : CollatzResearch.WordTrace tailWord_6726518 prefixEnd_6726518 3453936865119818701090313 := by
  unfold tailWord_6726518
  simp only [CollatzResearch.WordTrace]
  refine ⟨15333516665311347416190263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163557511096654372439362805 15333516665311347416190263)
  ·
    refine ⟨23000274997967021124285395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15333516665311347416190263 23000274997967021124285395)
    ·
      refine ⟨34500412496950531686428093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23000274997967021124285395 34500412496950531686428093)
      ·
        refine ⟨12937654686356449382410535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34500412496950531686428093 12937654686356449382410535)
        ·
          refine ⟨19406482029534674073615803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12937654686356449382410535 19406482029534674073615803)
          ·
            refine ⟨29109723044302011110423705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19406482029534674073615803 29109723044302011110423705)
            ·
              refine ⟨21832292283226508332817779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29109723044302011110423705 21832292283226508332817779)
              ·
                refine ⟨32748438424839762499226669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21832292283226508332817779 32748438424839762499226669)
                ·
                  refine ⟨12280664409314910937210001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32748438424839762499226669 12280664409314910937210001)
                  ·
                    refine ⟨9210498306986183202907501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12280664409314910937210001 9210498306986183202907501)
                    ·
                      refine ⟨3453936865119818701090313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9210498306986183202907501 3453936865119818701090313)
                      ·
                        rfl

theorem cell23_6726518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_6726518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726518 prefixEnd_6726518 := by exact prefixLift 6726518
  have htrace : WordTrace (prefixWord ++ tailWord_6726518) baseStart_6726518 baseEnd_6726518 := by
    simpa [prefixWord, tailWord_6726518, baseEnd_6726518] using wordTrace_append hprefix tailTrace_6726518
  have hstable : (prefixWord ++ tailWord_6726518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726518).length < 2 ^ (prefixWord ++ tailWord_6726518).sum := by decide
  have hdescent : baseEnd_6726518 < baseStart_6726518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726531 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 4, 1, 3]
def baseStart_6726531 : Nat := 118140960795 + 6726531 * 2 ^ 59
def prefixEnd_6726531 : Nat := 4983230072969 + 3 ^ 40 * 6726531 * 2
def baseEnd_6726531 : Nat := 3453943540368327150227753

theorem tailTrace_6726531 : CollatzResearch.WordTrace tailWord_6726531 prefixEnd_6726531 3453943540368327150227753 := by
  unfold tailWord_6726531
  simp only [CollatzResearch.WordTrace]
  refine ⟨245336740793934461879267447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163557827195956307919511631 245336740793934461879267447)
  ·
    refine ⟨368005111190901692818901171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245336740793934461879267447 368005111190901692818901171)
    ·
      refine ⟨552007666786352539228351757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368005111190901692818901171 552007666786352539228351757)
      ·
        refine ⟨207002875044882202210631909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 552007666786352539228351757 207002875044882202210631909)
        ·
          refine ⟨38813039070915412914493483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207002875044882202210631909 38813039070915412914493483)
          ·
            refine ⟨58219558606373119371740225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38813039070915412914493483 58219558606373119371740225)
            ·
              refine ⟨43664668954779839528805169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58219558606373119371740225 43664668954779839528805169)
              ·
                refine ⟨32748501716084879646603877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43664668954779839528805169 32748501716084879646603877)
                ·
                  refine ⟨6140344071765914933738227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32748501716084879646603877 6140344071765914933738227)
                  ·
                    refine ⟨9210516107648872400607341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6140344071765914933738227 9210516107648872400607341)
                    ·
                      refine ⟨3453943540368327150227753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9210516107648872400607341 3453943540368327150227753)
                      ·
                        rfl

theorem cell23_6726531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 1, 3].length) (baseStart_6726531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726531 prefixEnd_6726531 := by exact prefixLift 6726531
  have htrace : WordTrace (prefixWord ++ tailWord_6726531) baseStart_6726531 baseEnd_6726531 := by
    simpa [prefixWord, tailWord_6726531, baseEnd_6726531] using wordTrace_append hprefix tailTrace_6726531
  have hstable : (prefixWord ++ tailWord_6726531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726531).length < 2 ^ (prefixWord ++ tailWord_6726531).sum := by decide
  have hdescent : baseEnd_6726531 < baseStart_6726531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726535 : List Nat := [1, 1, 4, 2, 3, 3, 2, 1, 1, 2, 3]
def baseStart_6726535 : Nat := 118140960795 + 6726535 * 2 ^ 59
def prefixEnd_6726535 : Nat := 4983230072969 + 3 ^ 40 * 6726535 * 2
def baseEnd_6726535 : Nat := 3453945594290945134577735

theorem tailTrace_6726535 : CollatzResearch.WordTrace tailWord_6726535 prefixEnd_6726535 3453945594290945134577735 := by
  unfold tailWord_6726535
  simp only [CollatzResearch.WordTrace]
  refine ⟨245336886685919970562413059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163557924457279980374942039 245336886685919970562413059)
  ·
    refine ⟨368005330028879955843619589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245336886685919970562413059 368005330028879955843619589)
    ·
      refine ⟨69000999380414991720678673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 368005330028879955843619589 69000999380414991720678673)
      ·
        refine ⟨51750749535311243790509005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69000999380414991720678673 51750749535311243790509005)
        ·
          refine ⟨19406531075741716421440877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51750749535311243790509005 19406531075741716421440877)
          ·
            refine ⟨7277449153403143658040329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19406531075741716421440877 7277449153403143658040329)
            ·
              refine ⟨5458086865052357743530247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7277449153403143658040329 5458086865052357743530247)
              ·
                refine ⟨8187130297578536615295371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5458086865052357743530247 8187130297578536615295371)
                ·
                  refine ⟨12280695446367804922943057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8187130297578536615295371 12280695446367804922943057)
                  ·
                    refine ⟨9210521584775853692207293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12280695446367804922943057 9210521584775853692207293)
                    ·
                      refine ⟨3453945594290945134577735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9210521584775853692207293 3453945594290945134577735)
                      ·
                        rfl

theorem cell23_6726535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_6726535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726535 prefixEnd_6726535 := by exact prefixLift 6726535
  have htrace : WordTrace (prefixWord ++ tailWord_6726535) baseStart_6726535 baseEnd_6726535 := by
    simpa [prefixWord, tailWord_6726535, baseEnd_6726535] using wordTrace_append hprefix tailTrace_6726535
  have hstable : (prefixWord ++ tailWord_6726535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726535).length < 2 ^ (prefixWord ++ tailWord_6726535).sum := by decide
  have hdescent : baseEnd_6726535 < baseStart_6726535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726548 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_6726548 : Nat := 118140960795 + 6726548 * 2 ^ 59
def prefixEnd_6726548 : Nat := 4983230072969 + 3 ^ 40 * 6726548 * 2
def baseEnd_6726548 : Nat := 3453952269539453583715175

theorem tailTrace_6726548 : CollatzResearch.WordTrace tailWord_6726548 prefixEnd_6726548 3453952269539453583715175 := by
  unfold tailWord_6726548
  simp only [CollatzResearch.WordTrace]
  refine ⟨122668680417436436891318149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163558240556581915855090865 122668680417436436891318149)
  ·
    refine ⟨23000377578269331917122153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122668680417436436891318149 23000377578269331917122153)
    ·
      refine ⟨17250283183701998937841615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23000377578269331917122153 17250283183701998937841615)
      ·
        refine ⟨25875424775552998406762423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17250283183701998937841615 25875424775552998406762423)
        ·
          refine ⟨38813137163329497610143635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25875424775552998406762423 38813137163329497610143635)
          ·
            refine ⟨58219705744994246415215453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38813137163329497610143635 58219705744994246415215453)
            ·
              refine ⟨21832389654372842405705795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58219705744994246415215453 21832389654372842405705795)
              ·
                refine ⟨32748584481559263608558693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21832389654372842405705795 32748584481559263608558693)
                ·
                  refine ⟨6140359590292361926604755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32748584481559263608558693 6140359590292361926604755)
                  ·
                    refine ⟨9210539385438542889907133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6140359590292361926604755 9210539385438542889907133)
                    ·
                      refine ⟨3453952269539453583715175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9210539385438542889907133 3453952269539453583715175)
                      ·
                        rfl

theorem cell23_6726548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_6726548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726548 prefixEnd_6726548 := by exact prefixLift 6726548
  have htrace : WordTrace (prefixWord ++ tailWord_6726548) baseStart_6726548 baseEnd_6726548 := by
    simpa [prefixWord, tailWord_6726548, baseEnd_6726548] using wordTrace_append hprefix tailTrace_6726548
  have hstable : (prefixWord ++ tailWord_6726548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726548).length < 2 ^ (prefixWord ++ tailWord_6726548).sum := by decide
  have hdescent : baseEnd_6726548 < baseStart_6726548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726564 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 2, 6]
def baseStart_6726564 : Nat := 118140960795 + 6726564 * 2 ^ 59
def prefixEnd_6726564 : Nat := 4983230072969 + 3 ^ 40 * 6726564 * 2
def baseEnd_6726564 : Nat := 1151320161743308507038367

theorem tailTrace_6726564 : CollatzResearch.WordTrace tailWord_6726564 prefixEnd_6726564 1151320161743308507038367 := by
  unfold tailWord_6726564
  simp only [CollatzResearch.WordTrace]
  refine ⟨122668972201407454257609373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163558629601876605676812497 122668972201407454257609373)
  ·
    refine ⟨46000864575527795346603515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122668972201407454257609373 46000864575527795346603515)
    ·
      refine ⟨69001296863291693019905273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46000864575527795346603515 69001296863291693019905273)
      ·
        refine ⟨51750972647468769764928955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69001296863291693019905273 51750972647468769764928955)
        ·
          refine ⟨77626458971203154647393433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51750972647468769764928955 77626458971203154647393433)
          ·
            refine ⟨58219844228402365985545075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77626458971203154647393433 58219844228402365985545075)
            ·
              refine ⟨87329766342603548978317613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58219844228402365985545075 87329766342603548978317613)
              ·
                refine ⟨32748662378476330866869105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87329766342603548978317613 32748662378476330866869105)
                ·
                  refine ⟨24561496783857248150151829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32748662378476330866869105 24561496783857248150151829)
                  ·
                    refine ⟨1151320161743308507038367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24561496783857248150151829 1151320161743308507038367)
                    ·
                      rfl

theorem cell23_6726564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_6726564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726564 prefixEnd_6726564 := by exact prefixLift 6726564
  have htrace : WordTrace (prefixWord ++ tailWord_6726564) baseStart_6726564 baseEnd_6726564 := by
    simpa [prefixWord, tailWord_6726564, baseEnd_6726564] using wordTrace_append hprefix tailTrace_6726564
  have hstable : (prefixWord ++ tailWord_6726564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726564).length < 2 ^ (prefixWord ++ tailWord_6726564).sum := by decide
  have hdescent : baseEnd_6726564 < baseStart_6726564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726604 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 1, 2, 7]
def baseStart_6726604 : Nat := 118140960795 + 6726604 * 2 ^ 59
def prefixEnd_6726604 : Nat := 4983230072969 + 3 ^ 40 * 6726604 * 2
def baseEnd_6726604 : Nat := 3453981024456105364614917

theorem tailTrace_6726604 : CollatzResearch.WordTrace tailWord_6726604 prefixEnd_6726604 3453981024456105364614917 := by
  unfold tailWord_6726604
  simp only [CollatzResearch.WordTrace]
  refine ⟨122669701661334997673337433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163559602215113330231116577 122669701661334997673337433)
  ·
    refine ⟨92002276246001248255003075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122669701661334997673337433 92002276246001248255003075)
    ·
      refine ⟨138003414369001872382504613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92002276246001248255003075 138003414369001872382504613)
      ·
        refine ⟨25875640194187851071719615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138003414369001872382504613 25875640194187851071719615)
        ·
          refine ⟨38813460291281776607579423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25875640194187851071719615 38813460291281776607579423)
          ·
            refine ⟨58220190436922664911369135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38813460291281776607579423 58220190436922664911369135)
            ·
              refine ⟨87330285655383997367053703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58220190436922664911369135 87330285655383997367053703)
              ·
                refine ⟨130995428483075996050580555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87330285655383997367053703 130995428483075996050580555)
                ·
                  refine ⟨196493142724613994075870833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130995428483075996050580555 196493142724613994075870833)
                  ·
                    refine ⟨147369857043460495556903125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 196493142724613994075870833 147369857043460495556903125)
                    ·
                      refine ⟨3453981024456105364614917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 147369857043460495556903125 3453981024456105364614917)
                      ·
                        rfl

theorem cell23_6726604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_6726604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726604 prefixEnd_6726604 := by exact prefixLift 6726604
  have htrace : WordTrace (prefixWord ++ tailWord_6726604) baseStart_6726604 baseEnd_6726604 := by
    simpa [prefixWord, tailWord_6726604, baseEnd_6726604] using wordTrace_append hprefix tailTrace_6726604
  have hstable : (prefixWord ++ tailWord_6726604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726604).length < 2 ^ (prefixWord ++ tailWord_6726604).sum := by decide
  have hdescent : baseEnd_6726604 < baseStart_6726604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726641 : List Nat := [1, 2, 2, 2, 4, 1, 1, 3, 2, 5]
def baseStart_6726641 : Nat := 118140960795 + 6726641 * 2 ^ 59
def prefixEnd_6726641 : Nat := 4983230072969 + 3 ^ 40 * 6726641 * 2
def baseEnd_6726641 : Nat := 1151333341080107239950749

theorem tailTrace_6726641 : CollatzResearch.WordTrace tailWord_6726641 prefixEnd_6726641 1151333341080107239950749 := by
  unfold tailWord_6726641
  simp only [CollatzResearch.WordTrace]
  refine ⟨245340752823535950665771777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163560501882357300443847851 245340752823535950665771777)
  ·
    refine ⟨184005564617651962999328833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245340752823535950665771777 184005564617651962999328833)
    ·
      refine ⟨138004173463238972249496625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184005564617651962999328833 138004173463238972249496625)
      ·
        refine ⟨103503130097429229187122469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138004173463238972249496625 103503130097429229187122469)
        ·
          refine ⟨19406836893267980472585463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103503130097429229187122469 19406836893267980472585463)
          ·
            refine ⟨29110255339901970708878195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19406836893267980472585463 29110255339901970708878195)
            ·
              refine ⟨43665383009852956063317293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29110255339901970708878195 43665383009852956063317293)
              ·
                refine ⟨16374518628694858523743985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43665383009852956063317293 16374518628694858523743985)
                ·
                  refine ⟨12280888971521143892807989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16374518628694858523743985 12280888971521143892807989)
                  ·
                    refine ⟨1151333341080107239950749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12280888971521143892807989 1151333341080107239950749)
                    ·
                      rfl

theorem cell23_6726641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_6726641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726641 prefixEnd_6726641 := by exact prefixLift 6726641
  have htrace : WordTrace (prefixWord ++ tailWord_6726641) baseStart_6726641 baseEnd_6726641 := by
    simpa [prefixWord, tailWord_6726641, baseEnd_6726641] using wordTrace_append hprefix tailTrace_6726641
  have hstable : (prefixWord ++ tailWord_6726641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726641).length < 2 ^ (prefixWord ++ tailWord_6726641).sum := by decide
  have hdescent : baseEnd_6726641 < baseStart_6726641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726661 : List Nat := [1, 3, 1, 1, 2, 3, 1, 4, 2, 1, 4]
def baseStart_6726661 : Nat := 118140960795 + 6726661 * 2 ^ 59
def prefixEnd_6726661 : Nat := 4983230072969 + 3 ^ 40 * 6726661 * 2
def baseEnd_6726661 : Nat := 3454010292853411641602155

theorem tailTrace_6726661 : CollatzResearch.WordTrace tailWord_6726661 prefixEnd_6726661 3454010292853411641602155 := by
  unfold tailWord_6726661
  simp only [CollatzResearch.WordTrace]
  refine ⟨245341482283463494081499837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163560988188975662720999891 245341482283463494081499837)
  ·
    refine ⟨92003055856298810280562439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245341482283463494081499837 92003055856298810280562439)
    ·
      refine ⟨138004583784448215420843659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92003055856298810280562439 138004583784448215420843659)
      ·
        refine ⟨207006875676672323131265489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138004583784448215420843659 207006875676672323131265489)
        ·
          refine ⟨155255156757504242348449117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207006875676672323131265489 155255156757504242348449117)
          ·
            refine ⟨58220683784064090880668419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155255156757504242348449117 58220683784064090880668419)
            ·
              refine ⟨87331025676096136321002629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58220683784064090880668419 87331025676096136321002629)
              ·
                refine ⟨16374567314268025560187993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87331025676096136321002629 16374567314268025560187993)
                ·
                  refine ⟨12280925485701019170140995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16374567314268025560187993 12280925485701019170140995)
                  ·
                    refine ⟨18421388228551528755211493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12280925485701019170140995 18421388228551528755211493)
                    ·
                      refine ⟨3454010292853411641602155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18421388228551528755211493 3454010292853411641602155)
                      ·
                        rfl

theorem cell23_6726661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_6726661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726661 prefixEnd_6726661 := by exact prefixLift 6726661
  have htrace : WordTrace (prefixWord ++ tailWord_6726661) baseStart_6726661 baseEnd_6726661 := by
    simpa [prefixWord, tailWord_6726661, baseEnd_6726661] using wordTrace_append hprefix tailTrace_6726661
  have hstable : (prefixWord ++ tailWord_6726661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726661).length < 2 ^ (prefixWord ++ tailWord_6726661).sum := by decide
  have hdescent : baseEnd_6726661 < baseStart_6726661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726681 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 4, 2, 3]
def baseStart_6726681 : Nat := 118140960795 + 6726681 * 2 ^ 59
def prefixEnd_6726681 : Nat := 4983230072969 + 3 ^ 40 * 6726681 * 2
def baseEnd_6726681 : Nat := 3454020562466501563352063

theorem tailTrace_6726681 : CollatzResearch.WordTrace tailWord_6726681 prefixEnd_6726681 3454020562466501563352063 := by
  unfold tailWord_6726681
  simp only [CollatzResearch.WordTrace]
  refine ⟨245342211743391037497227897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163561474495594024998151931 245342211743391037497227897)
  ·
    refine ⟨184006658807543278122920923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245342211743391037497227897 184006658807543278122920923)
    ·
      refine ⟨276009988211314917184381385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184006658807543278122920923 276009988211314917184381385)
      ·
        refine ⟨207007491158486187888286039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276009988211314917184381385 207007491158486187888286039)
        ·
          refine ⟨310511236737729281832429059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207007491158486187888286039 310511236737729281832429059)
          ·
            refine ⟨465766855106593922748643589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310511236737729281832429059 465766855106593922748643589)
            ·
              refine ⟨87331285332486360515370673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 465766855106593922748643589 87331285332486360515370673)
              ·
                refine ⟨65498463999364770386528005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87331285332486360515370673 65498463999364770386528005)
                ·
                  refine ⟨12280961999880894447474001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65498463999364770386528005 12280961999880894447474001)
                  ·
                    refine ⟨9210721499910670835605501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12280961999880894447474001 9210721499910670835605501)
                    ·
                      refine ⟨3454020562466501563352063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9210721499910670835605501 3454020562466501563352063)
                      ·
                        rfl

theorem cell23_6726681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 2, 3].length) (baseStart_6726681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726681 prefixEnd_6726681 := by exact prefixLift 6726681
  have htrace : WordTrace (prefixWord ++ tailWord_6726681) baseStart_6726681 baseEnd_6726681 := by
    simpa [prefixWord, tailWord_6726681, baseEnd_6726681] using wordTrace_append hprefix tailTrace_6726681
  have hstable : (prefixWord ++ tailWord_6726681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726681).length < 2 ^ (prefixWord ++ tailWord_6726681).sum := by decide
  have hdescent : baseEnd_6726681 < baseStart_6726681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726695 : List Nat := [1, 1, 7, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_6726695 : Nat := 118140960795 + 6726695 * 2 ^ 59
def prefixEnd_6726695 : Nat := 4983230072969 + 3 ^ 40 * 6726695 * 2
def baseEnd_6726695 : Nat := 3454027751195664508576999

theorem tailTrace_6726695 : CollatzResearch.WordTrace tailWord_6726695 prefixEnd_6726695 3454027751195664508576999 := by
  unfold tailWord_6726695
  simp only [CollatzResearch.WordTrace]
  refine ⟨245342722365340317888237539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163561814910226878592158359 245342722365340317888237539)
  ·
    refine ⟨368014083548010476832356309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245342722365340317888237539 368014083548010476832356309)
    ·
      refine ⟨8625330083156495550758351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 368014083548010476832356309 8625330083156495550758351)
      ·
        refine ⟨12937995124734743326137527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8625330083156495550758351 12937995124734743326137527)
        ·
          refine ⟨19406992687102114989206291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12937995124734743326137527 19406992687102114989206291)
          ·
            refine ⟨29110489030653172483809437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19406992687102114989206291 29110489030653172483809437)
            ·
              refine ⟨10916433386494939681428539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29110489030653172483809437 10916433386494939681428539)
              ·
                refine ⟨16374650079742409522142809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10916433386494939681428539 16374650079742409522142809)
                ·
                  refine ⟨12280987559806807141607107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16374650079742409522142809 12280987559806807141607107)
                  ·
                    refine ⟨18421481339710210712410661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12280987559806807141607107 18421481339710210712410661)
                    ·
                      refine ⟨3454027751195664508576999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18421481339710210712410661 3454027751195664508576999)
                      ·
                        rfl

theorem cell23_6726695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_6726695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726695 prefixEnd_6726695 := by exact prefixLift 6726695
  have htrace : WordTrace (prefixWord ++ tailWord_6726695) baseStart_6726695 baseEnd_6726695 := by
    simpa [prefixWord, tailWord_6726695, baseEnd_6726695] using wordTrace_append hprefix tailTrace_6726695
  have hstable : (prefixWord ++ tailWord_6726695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726695).length < 2 ^ (prefixWord ++ tailWord_6726695).sum := by decide
  have hdescent : baseEnd_6726695 < baseStart_6726695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726705 : List Nat := [1, 2, 2, 3, 1, 2, 4, 3, 1, 4]
def baseStart_6726705 : Nat := 118140960795 + 6726705 * 2 ^ 59
def prefixEnd_6726705 : Nat := 4983230072969 + 3 ^ 40 * 6726705 * 2
def baseEnd_6726705 : Nat := 1151344295334069823150651

theorem tailTrace_6726705 : CollatzResearch.WordTrace tailWord_6726705 prefixEnd_6726705 1151344295334069823150651 := by
  unfold tailWord_6726705
  simp only [CollatzResearch.WordTrace]
  refine ⟨245343087095304089596101569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163562058063536059730734379 245343087095304089596101569)
  ·
    refine ⟨184007315321478067197076177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245343087095304089596101569 184007315321478067197076177)
    ·
      refine ⟨138005486491108550397807133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184007315321478067197076177 138005486491108550397807133)
      ·
        refine ⟨51752057434165706399177675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138005486491108550397807133 51752057434165706399177675)
        ·
          refine ⟨77628086151248559598766513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51752057434165706399177675 77628086151248559598766513)
          ·
            refine ⟨58221064613436419699074885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77628086151248559598766513 58221064613436419699074885)
            ·
              refine ⟨10916449615019328693576541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58221064613436419699074885 10916449615019328693576541)
              ·
                refine ⟨4093668605632248260091203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10916449615019328693576541 4093668605632248260091203)
                ·
                  refine ⟨6140502908448372390136805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4093668605632248260091203 6140502908448372390136805)
                  ·
                    refine ⟨1151344295334069823150651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6140502908448372390136805 1151344295334069823150651)
                    ·
                      rfl

theorem cell23_6726705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 1, 4].length) (baseStart_6726705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726705 prefixEnd_6726705 := by exact prefixLift 6726705
  have htrace : WordTrace (prefixWord ++ tailWord_6726705) baseStart_6726705 baseEnd_6726705 := by
    simpa [prefixWord, tailWord_6726705, baseEnd_6726705] using wordTrace_append hprefix tailTrace_6726705
  have hstable : (prefixWord ++ tailWord_6726705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726705).length < 2 ^ (prefixWord ++ tailWord_6726705).sum := by decide
  have hdescent : baseEnd_6726705 < baseStart_6726705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726708 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_6726708 : Nat := 118140960795 + 6726708 * 2 ^ 59
def prefixEnd_6726708 : Nat := 4983230072969 + 3 ^ 40 * 6726708 * 2
def baseEnd_6726708 : Nat := 3454034426444172957714439

theorem tailTrace_6726708 : CollatzResearch.WordTrace tailWord_6726708 prefixEnd_6726708 3454034426444172957714439 := by
  unfold tailWord_6726708
  simp only [CollatzResearch.WordTrace]
  refine ⟨122671598257146610554230389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163562131009528814072307185 122671598257146610554230389)
  ·
    refine ⟨11500462336607494739459099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122671598257146610554230389 11500462336607494739459099)
    ·
      refine ⟨17250693504911242109188649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11500462336607494739459099 17250693504911242109188649)
      ·
        refine ⟨12938020128683431581891487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17250693504911242109188649 12938020128683431581891487)
        ·
          refine ⟨19407030193025147372837231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12938020128683431581891487 19407030193025147372837231)
          ·
            refine ⟨29110545289537721059255847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19407030193025147372837231 29110545289537721059255847)
            ·
              refine ⟨43665817934306581588883771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29110545289537721059255847 43665817934306581588883771)
              ·
                refine ⟨65498726901459872383325657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43665817934306581588883771 65498726901459872383325657)
                ·
                  refine ⟨49124045176094904287494243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65498726901459872383325657 49124045176094904287494243)
                  ·
                    refine ⟨73686067764142356431241365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49124045176094904287494243 73686067764142356431241365)
                    ·
                      refine ⟨3454034426444172957714439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73686067764142356431241365 3454034426444172957714439)
                      ·
                        rfl

theorem cell23_6726708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_6726708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726708 prefixEnd_6726708 := by exact prefixLift 6726708
  have htrace : WordTrace (prefixWord ++ tailWord_6726708) baseStart_6726708 baseEnd_6726708 := by
    simpa [prefixWord, tailWord_6726708, baseEnd_6726708] using wordTrace_append hprefix tailTrace_6726708
  have hstable : (prefixWord ++ tailWord_6726708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726708).length < 2 ^ (prefixWord ++ tailWord_6726708).sum := by decide
  have hdescent : baseEnd_6726708 < baseStart_6726708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726718 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 8]
def baseStart_6726718 : Nat := 118140960795 + 6726718 * 2 ^ 59
def prefixEnd_6726718 : Nat := 4983230072969 + 3 ^ 40 * 6726718 * 2
def baseEnd_6726718 : Nat := 383782173472301990954377

theorem tailTrace_6726718 : CollatzResearch.WordTrace tailWord_6726718 prefixEnd_6726718 383782173472301990954377 := by
  unfold tailWord_6726718
  simp only [CollatzResearch.WordTrace]
  refine ⟨30667945155532124102040601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163562374162837995210883205 30667945155532124102040601)
  ·
    refine ⟨23000958866649093076530451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30667945155532124102040601 23000958866649093076530451)
    ·
      refine ⟨34501438299973639614795677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23000958866649093076530451 34501438299973639614795677)
      ·
        refine ⟨12938039362490114855548379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34501438299973639614795677 12938039362490114855548379)
        ·
          refine ⟨19407059043735172283322569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12938039362490114855548379 19407059043735172283322569)
          ·
            refine ⟨14555294282801379212491927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19407059043735172283322569 14555294282801379212491927)
            ·
              refine ⟨21832941424202068818737891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14555294282801379212491927 21832941424202068818737891)
              ·
                refine ⟨32749412136303103228106837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21832941424202068818737891 32749412136303103228106837)
                ·
                  refine ⟨383782173472301990954377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32749412136303103228106837 383782173472301990954377)
                  ·
                    rfl

theorem cell23_6726718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_6726718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726718 prefixEnd_6726718 := by exact prefixLift 6726718
  have htrace : WordTrace (prefixWord ++ tailWord_6726718) baseStart_6726718 baseEnd_6726718 := by
    simpa [prefixWord, tailWord_6726718, baseEnd_6726718] using wordTrace_append hprefix tailTrace_6726718
  have hstable : (prefixWord ++ tailWord_6726718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726718).length < 2 ^ (prefixWord ++ tailWord_6726718).sum := by decide
  have hdescent : baseEnd_6726718 < baseStart_6726718 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726768 : List Nat := [2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 4]
def baseStart_6726768 : Nat := 118140960795 + 6726768 * 2 ^ 59
def prefixEnd_6726768 : Nat := 4983230072969 + 3 ^ 40 * 6726768 * 2
def baseEnd_6726768 : Nat := 3454065235283442722964163

theorem tailTrace_6726768 : CollatzResearch.WordTrace tailWord_6726768 prefixEnd_6726768 3454065235283442722964163 := by
  unfold tailWord_6726768
  simp only [CollatzResearch.WordTrace]
  refine ⟨122672692447037925677822479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163563589929383900903763305 122672692447037925677822479)
  ·
    refine ⟨184009038670556888516733719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122672692447037925677822479 184009038670556888516733719)
    ·
      refine ⟨276013558005835332775100579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184009038670556888516733719 276013558005835332775100579)
      ·
        refine ⟨414020337008752999162650869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276013558005835332775100579 414020337008752999162650869)
        ·
          refine ⟨38814406594570593671498519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 414020337008752999162650869 38814406594570593671498519)
          ·
            refine ⟨58221609891855890507247779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38814406594570593671498519 58221609891855890507247779)
            ·
              refine ⟨87332414837783835760871669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58221609891855890507247779 87332414837783835760871669)
              ·
                refine ⟨8187413891042234602581719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87332414837783835760871669 8187413891042234602581719)
                ·
                  refine ⟨12281120836563351903872579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8187413891042234602581719 12281120836563351903872579)
                  ·
                    refine ⟨18421681254845027855808869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12281120836563351903872579 18421681254845027855808869)
                    ·
                      refine ⟨3454065235283442722964163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18421681254845027855808869 3454065235283442722964163)
                      ·
                        rfl

theorem cell23_6726768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 4].length) (baseStart_6726768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726768 prefixEnd_6726768 := by exact prefixLift 6726768
  have htrace : WordTrace (prefixWord ++ tailWord_6726768) baseStart_6726768 baseEnd_6726768 := by
    simpa [prefixWord, tailWord_6726768, baseEnd_6726768] using wordTrace_append hprefix tailTrace_6726768
  have hstable : (prefixWord ++ tailWord_6726768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726768).length < 2 ^ (prefixWord ++ tailWord_6726768).sum := by decide
  have hdescent : baseEnd_6726768 < baseStart_6726768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726781 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 3, 1, 6]
def baseStart_6726781 : Nat := 118140960795 + 6726781 * 2 ^ 59
def prefixEnd_6726781 : Nat := 4983230072969 + 3 ^ 40 * 6726781 * 2
def baseEnd_6726781 : Nat := 3454071910531951172101603

theorem tailTrace_6726781 : CollatzResearch.WordTrace tailWord_6726781 prefixEnd_6726781 3454071910531951172101603 := by
  unfold tailWord_6726781
  simp only [CollatzResearch.WordTrace]
  refine ⟨245345859043028754575868197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163563906028685836383912131 245345859043028754575868197)
  ·
    refine ⟨46002348570567891482975287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245345859043028754575868197 46002348570567891482975287)
    ·
      refine ⟨69003522855851837224462931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46002348570567891482975287 69003522855851837224462931)
      ·
        refine ⟨103505284283777755836694397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69003522855851837224462931 103505284283777755836694397)
        ·
          refine ⟨38814481606416658438760399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103505284283777755836694397 38814481606416658438760399)
          ·
            refine ⟨58221722409624987658140599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38814481606416658438760399 58221722409624987658140599)
            ·
              refine ⟨87332583614437481487210899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58221722409624987658140599 87332583614437481487210899)
              ·
                refine ⟨130998875421656222230816349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87332583614437481487210899 130998875421656222230816349)
                ·
                  refine ⟨49124578283121083336556131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130998875421656222230816349 49124578283121083336556131)
                  ·
                    refine ⟨73686867424681625004834197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49124578283121083336556131 73686867424681625004834197)
                    ·
                      refine ⟨3454071910531951172101603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73686867424681625004834197 3454071910531951172101603)
                      ·
                        rfl

theorem cell23_6726781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_6726781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726781 prefixEnd_6726781 := by exact prefixLift 6726781
  have htrace : WordTrace (prefixWord ++ tailWord_6726781) baseStart_6726781 baseEnd_6726781 := by
    simpa [prefixWord, tailWord_6726781, baseEnd_6726781] using wordTrace_append hprefix tailTrace_6726781
  have hstable : (prefixWord ++ tailWord_6726781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726781).length < 2 ^ (prefixWord ++ tailWord_6726781).sum := by decide
  have hdescent : baseEnd_6726781 < baseStart_6726781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726788 : List Nat := [2, 3, 2, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_6726788 : Nat := 118140960795 + 6726788 * 2 ^ 59
def prefixEnd_6726788 : Nat := 4983230072969 + 3 ^ 40 * 6726788 * 2
def baseEnd_6726788 : Nat := 3454075504896532644714071

theorem tailTrace_6726788 : CollatzResearch.WordTrace tailWord_6726788 prefixEnd_6726788 3454075504896532644714071 := by
  unfold tailWord_6726788
  simp only [CollatzResearch.WordTrace]
  refine ⟨122673057177001697385686509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163564076236002263180915345 122673057177001697385686509)
  ·
    refine ⟨46002396441375636519632441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122673057177001697385686509 46002396441375636519632441)
    ·
      refine ⟨34501797331031727389724331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46002396441375636519632441 34501797331031727389724331)
      ·
        refine ⟨51752695996547591084586497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34501797331031727389724331 51752695996547591084586497)
        ·
          refine ⟨38814521997410693313439873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51752695996547591084586497 38814521997410693313439873)
          ·
            refine ⟨29110891498058019985079905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38814521997410693313439873 29110891498058019985079905)
            ·
              refine ⟨21833168623543514988809929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29110891498058019985079905 21833168623543514988809929)
              ·
                refine ⟨16374876467657636241607447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21833168623543514988809929 16374876467657636241607447)
                ·
                  refine ⟨24562314701486454362411171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16374876467657636241607447 24562314701486454362411171)
                  ·
                    refine ⟨36843472052229681543616757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24562314701486454362411171 36843472052229681543616757)
                    ·
                      refine ⟨3454075504896532644714071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36843472052229681543616757 3454075504896532644714071)
                      ·
                        rfl

theorem cell23_6726788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_6726788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726788 prefixEnd_6726788 := by exact prefixLift 6726788
  have htrace : WordTrace (prefixWord ++ tailWord_6726788) baseStart_6726788 baseEnd_6726788 := by
    simpa [prefixWord, tailWord_6726788, baseEnd_6726788] using wordTrace_append hprefix tailTrace_6726788
  have hstable : (prefixWord ++ tailWord_6726788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726788).length < 2 ^ (prefixWord ++ tailWord_6726788).sum := by decide
  have hdescent : baseEnd_6726788 < baseStart_6726788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726798 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6]
def baseStart_6726798 : Nat := 118140960795 + 6726798 * 2 ^ 59
def prefixEnd_6726798 : Nat := 4983230072969 + 3 ^ 40 * 6726798 * 2
def baseEnd_6726798 : Nat := 3454080639703077605589025

theorem tailTrace_6726798 : CollatzResearch.WordTrace tailWord_6726798 prefixEnd_6726798 3454080639703077605589025 := by
  unfold tailWord_6726798
  simp only [CollatzResearch.WordTrace]
  refine ⟨30668309885495895809904631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163564319389311444319491365 30668309885495895809904631)
  ·
    refine ⟨46002464828243843714856947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30668309885495895809904631 46002464828243843714856947)
    ·
      refine ⟨69003697242365765572285421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46002464828243843714856947 69003697242365765572285421)
      ·
        refine ⟨25876386465887162089607033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69003697242365765572285421 25876386465887162089607033)
        ·
          refine ⟨19407289849415371567205275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25876386465887162089607033 19407289849415371567205275)
          ·
            refine ⟨29110934774123057350807913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19407289849415371567205275 29110934774123057350807913)
            ·
              refine ⟨21833201080592293013105935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29110934774123057350807913 21833201080592293013105935)
              ·
                refine ⟨32749801620888439519658903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21833201080592293013105935 32749801620888439519658903)
                ·
                  refine ⟨49124702431332659279488355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32749801620888439519658903 49124702431332659279488355)
                  ·
                    refine ⟨73687053646998988919232533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49124702431332659279488355 73687053646998988919232533)
                    ·
                      refine ⟨3454080639703077605589025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73687053646998988919232533 3454080639703077605589025)
                      ·
                        rfl

theorem cell23_6726798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_6726798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726798 prefixEnd_6726798 := by exact prefixLift 6726798
  have htrace : WordTrace (prefixWord ++ tailWord_6726798) baseStart_6726798 baseEnd_6726798 := by
    simpa [prefixWord, tailWord_6726798, baseEnd_6726798] using wordTrace_append hprefix tailTrace_6726798
  have hstable : (prefixWord ++ tailWord_6726798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726798).length < 2 ^ (prefixWord ++ tailWord_6726798).sum := by decide
  have hdescent : baseEnd_6726798 < baseStart_6726798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726802 : List Nat := [3, 2, 3, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_6726802 : Nat := 118140960795 + 6726802 * 2 ^ 59
def prefixEnd_6726802 : Nat := 4983230072969 + 3 ^ 40 * 6726802 * 2
def baseEnd_6726802 : Nat := 3454082693625695589939007

theorem tailTrace_6726802 : CollatzResearch.WordTrace tailWord_6726802 prefixEnd_6726802 3454082693625695589939007 := by
  unfold tailWord_6726802
  simp only [CollatzResearch.WordTrace]
  refine ⟨61336656243988168790595665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163564416650635116774921773 61336656243988168790595665)
  ·
    refine ⟨46002492182991126592946749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61336656243988168790595665 46002492182991126592946749)
    ·
      refine ⟨17250934568621672472355031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46002492182991126592946749 17250934568621672472355031)
      ·
        refine ⟨25876401852932508708532547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17250934568621672472355031 25876401852932508708532547)
        ·
          refine ⟨38814602779398763062798821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25876401852932508708532547 38814602779398763062798821)
          ·
            refine ⟨7277738021137268074274779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38814602779398763062798821 7277738021137268074274779)
            ·
              refine ⟨10916607031705902111412169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7277738021137268074274779 10916607031705902111412169)
              ·
                refine ⟨8187455273779426583559127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10916607031705902111412169 8187455273779426583559127)
                ·
                  refine ⟨12281182910669139875338691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8187455273779426583559127 12281182910669139875338691)
                  ·
                    refine ⟨18421774366003709813008037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12281182910669139875338691 18421774366003709813008037)
                    ·
                      refine ⟨3454082693625695589939007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18421774366003709813008037 3454082693625695589939007)
                      ·
                        rfl

theorem cell23_6726802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_6726802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726802 prefixEnd_6726802 := by exact prefixLift 6726802
  have htrace : WordTrace (prefixWord ++ tailWord_6726802) baseStart_6726802 baseEnd_6726802 := by
    simpa [prefixWord, tailWord_6726802, baseEnd_6726802] using wordTrace_append hprefix tailTrace_6726802
  have hstable : (prefixWord ++ tailWord_6726802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726802).length < 2 ^ (prefixWord ++ tailWord_6726802).sum := by decide
  have hdescent : baseEnd_6726802 < baseStart_6726802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726815 : List Nat := [1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 4]
def baseStart_6726815 : Nat := 118140960795 + 6726815 * 2 ^ 59
def prefixEnd_6726815 : Nat := 4983230072969 + 3 ^ 40 * 6726815 * 2
def baseEnd_6726815 : Nat := 3454089368874204039076447

theorem tailTrace_6726815 : CollatzResearch.WordTrace tailWord_6726815 prefixEnd_6726815 3454089368874204039076447 := by
  unfold tailWord_6726815
  simp only [CollatzResearch.WordTrace]
  refine ⟨245347099124905578382605899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163564732749937052255070599 245347099124905578382605899)
  ·
    refine ⟨368020648687358367573908849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245347099124905578382605899 368020648687358367573908849)
    ·
      refine ⟨276015486515518775680431637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368020648687358367573908849 276015486515518775680431637)
      ·
        refine ⟨12938225930414942610020233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 276015486515518775680431637 12938225930414942610020233)
        ·
          refine ⟨9703669447811206957515175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12938225930414942610020233 9703669447811206957515175)
          ·
            refine ⟨14555504171716810436272763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9703669447811206957515175 14555504171716810436272763)
            ·
              refine ⟨21833256257575215654409145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14555504171716810436272763 21833256257575215654409145)
              ·
                refine ⟨16374942193181411740806859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21833256257575215654409145 16374942193181411740806859)
                ·
                  refine ⟨24562413289772117611210289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16374942193181411740806859 24562413289772117611210289)
                  ·
                    refine ⟨18421809967329088208407717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24562413289772117611210289 18421809967329088208407717)
                    ·
                      refine ⟨3454089368874204039076447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18421809967329088208407717 3454089368874204039076447)
                      ·
                        rfl

theorem cell23_6726815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_6726815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726815 prefixEnd_6726815 := by exact prefixLift 6726815
  have htrace : WordTrace (prefixWord ++ tailWord_6726815) baseStart_6726815 baseEnd_6726815 := by
    simpa [prefixWord, tailWord_6726815, baseEnd_6726815] using wordTrace_append hprefix tailTrace_6726815
  have hstable : (prefixWord ++ tailWord_6726815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726815).length < 2 ^ (prefixWord ++ tailWord_6726815).sum := by decide
  have hdescent : baseEnd_6726815 < baseStart_6726815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726831 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 5]
def baseStart_6726831 : Nat := 118140960795 + 6726831 * 2 ^ 59
def prefixEnd_6726831 : Nat := 4983230072969 + 3 ^ 40 * 6726831 * 2
def baseEnd_6726831 : Nat := 3454097584564675976476373

theorem tailTrace_6726831 : CollatzResearch.WordTrace tailWord_6726831 prefixEnd_6726831 3454097584564675976476373 := by
  unfold tailWord_6726831
  simp only [CollatzResearch.WordTrace]
  refine ⟨245347682692847613115188347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163565121795231742076792231 245347682692847613115188347)
  ·
    refine ⟨368021524039271419672782521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245347682692847613115188347 368021524039271419672782521)
    ·
      refine ⟨276016143029453564754586891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368021524039271419672782521 276016143029453564754586891)
      ·
        refine ⟨414024214544180347131880337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276016143029453564754586891 414024214544180347131880337)
        ·
          refine ⟨310518160908135260348910253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414024214544180347131880337 310518160908135260348910253)
          ·
            refine ⟨116444310340550722630841345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 310518160908135260348910253 116444310340550722630841345)
            ·
              refine ⟨87333232755413041973131009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116444310340550722630841345 87333232755413041973131009)
              ·
                refine ⟨65499924566559781479848257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87333232755413041973131009 65499924566559781479848257)
                ·
                  refine ⟨49124943424919836109886193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65499924566559781479848257 49124943424919836109886193)
                  ·
                    refine ⟨36843707568689877082414645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49124943424919836109886193 36843707568689877082414645)
                    ·
                      refine ⟨3454097584564675976476373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36843707568689877082414645 3454097584564675976476373)
                      ·
                        rfl

theorem cell23_6726831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_6726831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726831 prefixEnd_6726831 := by exact prefixLift 6726831
  have htrace : WordTrace (prefixWord ++ tailWord_6726831) baseStart_6726831 baseEnd_6726831 := by
    simpa [prefixWord, tailWord_6726831, baseEnd_6726831] using wordTrace_append hprefix tailTrace_6726831
  have hstable : (prefixWord ++ tailWord_6726831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726831).length < 2 ^ (prefixWord ++ tailWord_6726831).sum := by decide
  have hdescent : baseEnd_6726831 < baseStart_6726831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726835 : List Nat := [1, 1, 1, 2, 3, 2, 3, 4, 2, 1, 3]
def baseStart_6726835 : Nat := 118140960795 + 6726835 * 2 ^ 59
def prefixEnd_6726835 : Nat := 4983230072969 + 3 ^ 40 * 6726835 * 2
def baseEnd_6726835 : Nat := 3454099638487293960826355

theorem tailTrace_6726835 : CollatzResearch.WordTrace tailWord_6726835 prefixEnd_6726835 3454099638487293960826355 := by
  unfold tailWord_6726835
  simp only [CollatzResearch.WordTrace]
  refine ⟨245347828584833121798333959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163565219056555414532222639 245347828584833121798333959)
  ·
    refine ⟨368021742877249682697500939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245347828584833121798333959 368021742877249682697500939)
    ·
      refine ⟨552032614315874524046251409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368021742877249682697500939 552032614315874524046251409)
      ·
        refine ⟨414024460736905893034688557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 552032614315874524046251409 414024460736905893034688557)
        ·
          refine ⟨155259172776339709888008209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 414024460736905893034688557 155259172776339709888008209)
          ·
            refine ⟨116444379582254782416006157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155259172776339709888008209 116444379582254782416006157)
            ·
              refine ⟨43666642343345543406002309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116444379582254782416006157 43666642343345543406002309)
              ·
                refine ⟨8187495439377289388625433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43666642343345543406002309 8187495439377289388625433)
                ·
                  refine ⟨6140621579532967041469075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8187495439377289388625433 6140621579532967041469075)
                  ·
                    refine ⟨9210932369299450562203613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6140621579532967041469075 9210932369299450562203613)
                    ·
                      refine ⟨3454099638487293960826355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9210932369299450562203613 3454099638487293960826355)
                      ·
                        rfl

theorem cell23_6726835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 1, 3].length) (baseStart_6726835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726835 prefixEnd_6726835 := by exact prefixLift 6726835
  have htrace : WordTrace (prefixWord ++ tailWord_6726835) baseStart_6726835 baseEnd_6726835 := by
    simpa [prefixWord, tailWord_6726835, baseEnd_6726835] using wordTrace_append hprefix tailTrace_6726835
  have hstable : (prefixWord ++ tailWord_6726835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726835).length < 2 ^ (prefixWord ++ tailWord_6726835).sum := by decide
  have hdescent : baseEnd_6726835 < baseStart_6726835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726845 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 3, 3, 2]
def baseStart_6726845 : Nat := 118140960795 + 6726845 * 2 ^ 59
def prefixEnd_6726845 : Nat := 4983230072969 + 3 ^ 40 * 6726845 * 2
def baseEnd_6726845 : Nat := 3454104773293838921701309

theorem tailTrace_6726845 : CollatzResearch.WordTrace tailWord_6726845 prefixEnd_6726845 3454104773293838921701309 := by
  unfold tailWord_6726845
  simp only [CollatzResearch.WordTrace]
  refine ⟨245348193314796893506197989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163565462209864595670798659 245348193314796893506197989)
  ·
    refine ⟨46002786246524417532412123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245348193314796893506197989 46002786246524417532412123)
    ·
      refine ⟨69004179369786626298618185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46002786246524417532412123 69004179369786626298618185)
      ·
        refine ⟨51753134527339969723963639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69004179369786626298618185 51753134527339969723963639)
        ·
          refine ⟨77629701791009954585945459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51753134527339969723963639 77629701791009954585945459)
          ·
            refine ⟨116444552686514931878918189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77629701791009954585945459 116444552686514931878918189)
            ·
              refine ⟨43666707257443099454594321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116444552686514931878918189 43666707257443099454594321)
              ·
                refine ⟨32750030443082324590945741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43666707257443099454594321 32750030443082324590945741)
                ·
                  refine ⟨12281261416155871721604653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32750030443082324590945741 12281261416155871721604653)
                  ·
                    refine ⟨4605473031058451895601745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12281261416155871721604653 4605473031058451895601745)
                    ·
                      refine ⟨3454104773293838921701309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4605473031058451895601745 3454104773293838921701309)
                      ·
                        rfl

theorem cell23_6726845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_6726845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726845 prefixEnd_6726845 := by exact prefixLift 6726845
  have htrace : WordTrace (prefixWord ++ tailWord_6726845) baseStart_6726845 baseEnd_6726845 := by
    simpa [prefixWord, tailWord_6726845, baseEnd_6726845] using wordTrace_append hprefix tailTrace_6726845
  have hstable : (prefixWord ++ tailWord_6726845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726845).length < 2 ^ (prefixWord ++ tailWord_6726845).sum := by decide
  have hdescent : baseEnd_6726845 < baseStart_6726845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726852 : List Nat := [2, 3, 3, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_6726852 : Nat := 118140960795 + 6726852 * 2 ^ 59
def prefixEnd_6726852 : Nat := 4983230072969 + 3 ^ 40 * 6726852 * 2
def baseEnd_6726852 : Nat := 3454108367658420394313777

theorem tailTrace_6726852 : CollatzResearch.WordTrace tailWord_6726852 prefixEnd_6726852 3454108367658420394313777 := by
  unfold tailWord_6726852
  simp only [CollatzResearch.WordTrace]
  refine ⟨122674224312885766850851405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163565632417181022467801873 122674224312885766850851405)
  ·
    refine ⟨46002834117332162569069277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122674224312885766850851405 46002834117332162569069277)
    ·
      refine ⟨17251062793999560963400979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46002834117332162569069277 17251062793999560963400979)
      ·
        refine ⟨25876594190999341445101469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17251062793999560963400979 25876594190999341445101469)
        ·
          refine ⟨9703722821624753041913051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25876594190999341445101469 9703722821624753041913051)
          ·
            refine ⟨14555584232437129562869577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9703722821624753041913051 14555584232437129562869577)
            ·
              refine ⟨10916688174327847172152183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14555584232437129562869577 10916688174327847172152183)
              ·
                refine ⟨16375032261491770758228275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10916688174327847172152183 16375032261491770758228275)
                ·
                  refine ⟨24562548392237656137342413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16375032261491770758228275 24562548392237656137342413)
                  ·
                    refine ⟨9210955647089121051503405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24562548392237656137342413 9210955647089121051503405)
                    ·
                      refine ⟨3454108367658420394313777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9210955647089121051503405 3454108367658420394313777)
                      ·
                        rfl

theorem cell23_6726852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_6726852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726852 prefixEnd_6726852 := by exact prefixLift 6726852
  have htrace : WordTrace (prefixWord ++ tailWord_6726852) baseStart_6726852 baseEnd_6726852 := by
    simpa [prefixWord, tailWord_6726852, baseEnd_6726852] using wordTrace_append hprefix tailTrace_6726852
  have hstable : (prefixWord ++ tailWord_6726852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726852).length < 2 ^ (prefixWord ++ tailWord_6726852).sum := by decide
  have hdescent : baseEnd_6726852 < baseStart_6726852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726888 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_6726888 : Nat := 118140960795 + 6726888 * 2 ^ 59
def prefixEnd_6726888 : Nat := 4983230072969 + 3 ^ 40 * 6726888 * 2
def baseEnd_6726888 : Nat := 3454126852961982253463611

theorem tailTrace_6726888 : CollatzResearch.WordTrace tailWord_6726888 prefixEnd_6726888 3454126852961982253463611 := by
  unfold tailWord_6726888
  simp only [CollatzResearch.WordTrace]
  refine ⟨122674880826820555925006659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163566507769094074566675545 122674880826820555925006659)
  ·
    refine ⟨184012321240230833887509989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122674880826820555925006659 184012321240230833887509989)
    ·
      refine ⟨34502310232543281353908123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184012321240230833887509989 34502310232543281353908123)
      ·
        refine ⟨51753465348814922030862185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34502310232543281353908123 51753465348814922030862185)
        ·
          refine ⟨38815099011611191523146639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51753465348814922030862185 38815099011611191523146639)
          ·
            refine ⟨58222648517416787284719959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38815099011611191523146639 58222648517416787284719959)
            ·
              refine ⟨87333972776125180927079939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58222648517416787284719959 87333972776125180927079939)
              ·
                refine ⟨131000959164187771390619909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87333972776125180927079939 131000959164187771390619909)
                ·
                  refine ⟨24562679843285207135741233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131000959164187771390619909 24562679843285207135741233)
                  ·
                    refine ⟨18422009882463905351805925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24562679843285207135741233 18422009882463905351805925)
                    ·
                      refine ⟨3454126852961982253463611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18422009882463905351805925 3454126852961982253463611)
                      ·
                        rfl

theorem cell23_6726888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_6726888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726888 prefixEnd_6726888 := by exact prefixLift 6726888
  have htrace : WordTrace (prefixWord ++ tailWord_6726888) baseStart_6726888 baseEnd_6726888 := by
    simpa [prefixWord, tailWord_6726888, baseEnd_6726888] using wordTrace_append hprefix tailTrace_6726888
  have hstable : (prefixWord ++ tailWord_6726888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726888).length < 2 ^ (prefixWord ++ tailWord_6726888).sum := by decide
  have hdescent : baseEnd_6726888 < baseStart_6726888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726892 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 4, 2, 2]
def baseStart_6726892 : Nat := 118140960795 + 6726892 * 2 ^ 59
def prefixEnd_6726892 : Nat := 4983230072969 + 3 ^ 40 * 6726892 * 2
def baseEnd_6726892 : Nat := 3454128906884600237813593

theorem tailTrace_6726892 : CollatzResearch.WordTrace tailWord_6726892 prefixEnd_6726892 3454128906884600237813593 := by
  unfold tailWord_6726892
  simp only [CollatzResearch.WordTrace]
  refine ⟨122674953772813310266579465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163566605030417747022105953 122674953772813310266579465)
  ·
    refine ⟨92006215329609982699934599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122674953772813310266579465 92006215329609982699934599)
    ·
      refine ⟨138009322994414974049901899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92006215329609982699934599 138009322994414974049901899)
      ·
        refine ⟨207013984491622461074852849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138009322994414974049901899 207013984491622461074852849)
        ·
          refine ⟨155260488368716845806139637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207013984491622461074852849 155260488368716845806139637)
          ·
            refine ⟨14555670784567204294325591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155260488368716845806139637 14555670784567204294325591)
            ·
              refine ⟨21833506176850806441488387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14555670784567204294325591 21833506176850806441488387)
              ·
                refine ⟨32750259265276209662232581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21833506176850806441488387 32750259265276209662232581)
                ·
                  refine ⟨6140673612239289311668609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32750259265276209662232581 6140673612239289311668609)
                  ·
                    refine ⟨4605505209179466983751457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6140673612239289311668609 4605505209179466983751457)
                    ·
                      refine ⟨3454128906884600237813593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4605505209179466983751457 3454128906884600237813593)
                      ·
                        rfl

theorem cell23_6726892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 2, 2].length) (baseStart_6726892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726892 prefixEnd_6726892 := by exact prefixLift 6726892
  have htrace : WordTrace (prefixWord ++ tailWord_6726892) baseStart_6726892 baseEnd_6726892 := by
    simpa [prefixWord, tailWord_6726892, baseEnd_6726892] using wordTrace_append hprefix tailTrace_6726892
  have hstable : (prefixWord ++ tailWord_6726892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726892).length < 2 ^ (prefixWord ++ tailWord_6726892).sum := by decide
  have hdescent : baseEnd_6726892 < baseStart_6726892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726985 : List Nat := [1, 2, 1, 1, 2, 3, 3, 3, 2, 2, 3]
def baseStart_6726985 : Nat := 118140960795 + 6726985 * 2 ^ 59
def prefixEnd_6726985 : Nat := 4983230072969 + 3 ^ 40 * 6726985 * 2
def baseEnd_6726985 : Nat := 3454176660585468373950665

theorem tailTrace_6726985 : CollatzResearch.WordTrace tailWord_6726985 prefixEnd_6726985 3454176660585468373950665 := by
  unfold tailWord_6726985
  simp only [CollatzResearch.WordTrace]
  refine ⟨245353299534289697416294409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163568866356193131610862939 245353299534289697416294409)
  ·
    refine ⟨184014974650717273062220807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245353299534289697416294409 184014974650717273062220807)
    ·
      refine ⟨276022461976075909593331211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184014974650717273062220807 276022461976075909593331211)
      ·
        refine ⟨414033692964113864389996817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276022461976075909593331211 414033692964113864389996817)
        ·
          refine ⟨310525269723085398292497613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414033692964113864389996817 310525269723085398292497613)
          ·
            refine ⟨116446976146157024359686605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 310525269723085398292497613 116446976146157024359686605)
            ·
              refine ⟨43667616054808884134882477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116446976146157024359686605 43667616054808884134882477)
              ·
                refine ⟨16375356020553331550580929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43667616054808884134882477 16375356020553331550580929)
                ·
                  refine ⟨12281517015414998662935697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16375356020553331550580929 12281517015414998662935697)
                  ·
                    refine ⟨9211137761561248997201773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12281517015414998662935697 9211137761561248997201773)
                    ·
                      refine ⟨3454176660585468373950665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9211137761561248997201773 3454176660585468373950665)
                      ·
                        rfl

theorem cell23_6726985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 2, 3].length) (baseStart_6726985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726985 prefixEnd_6726985 := by exact prefixLift 6726985
  have htrace : WordTrace (prefixWord ++ tailWord_6726985) baseStart_6726985 baseEnd_6726985 := by
    simpa [prefixWord, tailWord_6726985, baseEnd_6726985] using wordTrace_append hprefix tailTrace_6726985
  have hstable : (prefixWord ++ tailWord_6726985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726985).length < 2 ^ (prefixWord ++ tailWord_6726985).sum := by decide
  have hdescent : baseEnd_6726985 < baseStart_6726985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6726992 : List Nat := [2, 1, 1, 1, 1, 5, 2, 5, 1, 4]
def baseStart_6726992 : Nat := 118140960795 + 6726992 * 2 ^ 59
def prefixEnd_6726992 : Nat := 4983230072969 + 3 ^ 40 * 6726992 * 2
def baseEnd_6726992 : Nat := 1151393418316683282187711

theorem tailTrace_6726992 : CollatzResearch.WordTrace tailWord_6726992 prefixEnd_6726992 1151393418316683282187711 := by
  unfold tailWord_6726992
  simp only [CollatzResearch.WordTrace]
  refine ⟨122676777422632168805899615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163569036563509558407866153 122676777422632168805899615)
  ·
    refine ⟨184015166133948253208849423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122676777422632168805899615 184015166133948253208849423)
    ·
      refine ⟨276022749200922379813274135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184015166133948253208849423 276022749200922379813274135)
      ·
        refine ⟨414034123801383569719911203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276022749200922379813274135 414034123801383569719911203)
        ·
          refine ⟨621051185702075354579866805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414034123801383569719911203 621051185702075354579866805)
          ·
            refine ⟨58223548659569564491862513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 621051185702075354579866805 58223548659569564491862513)
            ·
              refine ⟨43667661494677173368896885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58223548659569564491862513 43667661494677173368896885)
              ·
                refine ⟨4093843265125985003334083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43667661494677173368896885 4093843265125985003334083)
                ·
                  refine ⟨6140764897688977505001125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4093843265125985003334083 6140764897688977505001125)
                  ·
                    refine ⟨1151393418316683282187711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6140764897688977505001125 1151393418316683282187711)
                    ·
                      rfl

theorem cell23_6726992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 1, 4].length) (baseStart_6726992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6726992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6726992 prefixEnd_6726992 := by exact prefixLift 6726992
  have htrace : WordTrace (prefixWord ++ tailWord_6726992) baseStart_6726992 baseEnd_6726992 := by
    simpa [prefixWord, tailWord_6726992, baseEnd_6726992] using wordTrace_append hprefix tailTrace_6726992
  have hstable : (prefixWord ++ tailWord_6726992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6726992).length < 2 ^ (prefixWord ++ tailWord_6726992).sum := by decide
  have hdescent : baseEnd_6726992 < baseStart_6726992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6726992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727035 : List Nat := [1, 1, 1, 1, 1, 6, 2, 4, 1, 5]
def baseStart_6727035 : Nat := 118140960795 + 6727035 * 2 ^ 59
def prefixEnd_6727035 : Nat := 4983230072969 + 3 ^ 40 * 6727035 * 2
def baseEnd_6727035 : Nat := 1151400778206064392775145

theorem tailTrace_6727035 : CollatzResearch.WordTrace tailWord_6727035 prefixEnd_6727035 1151400778206064392775145 := by
  unfold tailWord_6727035
  simp only [CollatzResearch.WordTrace]
  refine ⟨245355123184108555955614559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163570082122739037303743039 245355123184108555955614559)
  ·
    refine ⟨368032684776162833933421839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245355123184108555955614559 368032684776162833933421839)
    ·
      refine ⟨552049027164244250900132759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368032684776162833933421839 552049027164244250900132759)
      ·
        refine ⟨828073540746366376350199139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552049027164244250900132759 828073540746366376350199139)
        ·
          refine ⟨1242110311119549564525298709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 828073540746366376350199139 1242110311119549564525298709)
          ·
            refine ⟨58223920833728885837123377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1242110311119549564525298709 58223920833728885837123377)
            ·
              refine ⟨43667940625296664377842533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58223920833728885837123377 43667940625296664377842533)
              ·
                refine ⟨8187738867243124570845475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43667940625296664377842533 8187738867243124570845475)
                ·
                  refine ⟨12281608300864686856268213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8187738867243124570845475 12281608300864686856268213)
                  ·
                    refine ⟨1151400778206064392775145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12281608300864686856268213 1151400778206064392775145)
                    ·
                      rfl

theorem cell23_6727035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 5].length) (baseStart_6727035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727035 prefixEnd_6727035 := by exact prefixLift 6727035
  have htrace : WordTrace (prefixWord ++ tailWord_6727035) baseStart_6727035 baseEnd_6727035 := by
    simpa [prefixWord, tailWord_6727035, baseEnd_6727035] using wordTrace_append hprefix tailTrace_6727035
  have hstable : (prefixWord ++ tailWord_6727035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727035).length < 2 ^ (prefixWord ++ tailWord_6727035).sum := by decide
  have hdescent : baseEnd_6727035 < baseStart_6727035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727075 : List Nat := [1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 5]
def baseStart_6727075 : Nat := 118140960795 + 6727075 * 2 ^ 59
def prefixEnd_6727075 : Nat := 4983230072969 + 3 ^ 40 * 6727075 * 2
def baseEnd_6727075 : Nat := 3454222873844373021825251

theorem tailTrace_6727075 : CollatzResearch.WordTrace tailWord_6727075 prefixEnd_6727075 3454222873844373021825251 := by
  unfold tailWord_6727075
  simp only [CollatzResearch.WordTrace]
  refine ⟨245356582103963642787070679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163571054735975761858047119 245356582103963642787070679)
  ·
    refine ⟨368034873155945464180606019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245356582103963642787070679 368034873155945464180606019)
    ·
      refine ⟨552052309733918196270909029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368034873155945464180606019 552052309733918196270909029)
      ·
        refine ⟨103509808075109661800795443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 552052309733918196270909029 103509808075109661800795443)
        ·
          refine ⟨155264712112664492701193165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103509808075109661800795443 155264712112664492701193165)
          ·
            refine ⟨58224267042249184762947437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155264712112664492701193165 58224267042249184762947437)
            ·
              refine ⟨21834100140843444286105289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58224267042249184762947437 21834100140843444286105289)
              ·
                refine ⟨16375575105632583214578967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21834100140843444286105289 16375575105632583214578967)
                ·
                  refine ⟨24563362658448874821868451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16375575105632583214578967 24563362658448874821868451)
                  ·
                    refine ⟨36845043987673312232802677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24563362658448874821868451 36845043987673312232802677)
                    ·
                      refine ⟨3454222873844373021825251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36845043987673312232802677 3454222873844373021825251)
                      ·
                        rfl

theorem cell23_6727075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_6727075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727075 prefixEnd_6727075 := by exact prefixLift 6727075
  have htrace : WordTrace (prefixWord ++ tailWord_6727075) baseStart_6727075 baseEnd_6727075 := by
    simpa [prefixWord, tailWord_6727075, baseEnd_6727075] using wordTrace_append hprefix tailTrace_6727075
  have hstable : (prefixWord ++ tailWord_6727075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727075).length < 2 ^ (prefixWord ++ tailWord_6727075).sum := by decide
  have hdescent : baseEnd_6727075 < baseStart_6727075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727089 : List Nat := [1, 2, 2, 4, 1, 1, 1, 4, 3, 2, 2]
def baseStart_6727089 : Nat := 118140960795 + 6727089 * 2 ^ 59
def prefixEnd_6727089 : Nat := 4983230072969 + 3 ^ 40 * 6727089 * 2
def baseEnd_6727089 : Nat := 3454230062573535967050187

theorem tailTrace_6727089 : CollatzResearch.WordTrace tailWord_6727089 prefixEnd_6727089 3454230062573535967050187 := by
  unfold tailWord_6727089
  simp only [CollatzResearch.WordTrace]
  refine ⟨245357092725912923178080321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163571395150608615452053547 245357092725912923178080321)
  ·
    refine ⟨184017819544434692383560241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245357092725912923178080321 184017819544434692383560241)
    ·
      refine ⟨138013364658326019287670181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184017819544434692383560241 138013364658326019287670181)
      ·
        refine ⟨25877505873436128616438159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138013364658326019287670181 25877505873436128616438159)
        ·
          refine ⟨38816258810154192924657239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25877505873436128616438159 38816258810154192924657239)
          ·
            refine ⟨58224388215231289386985859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38816258810154192924657239 58224388215231289386985859)
            ·
              refine ⟨87336582322846934080478789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58224388215231289386985859 87336582322846934080478789)
              ·
                refine ⟨16375609185533800140089773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87336582322846934080478789 16375609185533800140089773)
                ·
                  refine ⟨6140853444575175052533665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16375609185533800140089773 6140853444575175052533665)
                  ·
                    refine ⟨4605640083431381289400249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6140853444575175052533665 4605640083431381289400249)
                    ·
                      refine ⟨3454230062573535967050187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4605640083431381289400249 3454230062573535967050187)
                      ·
                        rfl

theorem cell23_6727089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_6727089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727089 prefixEnd_6727089 := by exact prefixLift 6727089
  have htrace : WordTrace (prefixWord ++ tailWord_6727089) baseStart_6727089 baseEnd_6727089 := by
    simpa [prefixWord, tailWord_6727089, baseEnd_6727089] using wordTrace_append hprefix tailTrace_6727089
  have hstable : (prefixWord ++ tailWord_6727089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727089).length < 2 ^ (prefixWord ++ tailWord_6727089).sum := by decide
  have hdescent : baseEnd_6727089 < baseStart_6727089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727100 : List Nat := [2, 2, 2, 4, 3, 1, 1, 3, 1, 1, 3]
def baseStart_6727100 : Nat := 118140960795 + 6727100 * 2 ^ 59
def prefixEnd_6727100 : Nat := 4983230072969 + 3 ^ 40 * 6727100 * 2
def baseEnd_6727100 : Nat := 3454235710860735424012637

theorem tailTrace_6727100 : CollatzResearch.WordTrace tailWord_6727100 prefixEnd_6727100 3454235710860735424012637 := by
  unfold tailWord_6727100
  simp only [CollatzResearch.WordTrace]
  refine ⟨122678746964436536028365377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163571662619248714704487169 122678746964436536028365377)
  ·
    refine ⟨92009060223327402021274033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122678746964436536028365377 92009060223327402021274033)
    ·
      refine ⟨69006795167495551515955525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92009060223327402021274033 69006795167495551515955525)
      ·
        refine ⟨12938774093905415909241661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69006795167495551515955525 12938774093905415909241661)
        ·
          refine ⟨4852040285214530965965623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12938774093905415909241661 4852040285214530965965623)
          ·
            refine ⟨7278060427821796448948435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4852040285214530965965623 7278060427821796448948435)
            ·
              refine ⟨10917090641732694673422653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7278060427821796448948435 10917090641732694673422653)
              ·
                refine ⟨4093908990649760502533495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10917090641732694673422653 4093908990649760502533495)
                ·
                  refine ⟨6140863485974640753800243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4093908990649760502533495 6140863485974640753800243)
                  ·
                    refine ⟨9211295228961961130700365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6140863485974640753800243 9211295228961961130700365)
                    ·
                      refine ⟨3454235710860735424012637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9211295228961961130700365 3454235710860735424012637)
                      ·
                        rfl

theorem cell23_6727100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_6727100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727100 prefixEnd_6727100 := by exact prefixLift 6727100
  have htrace : WordTrace (prefixWord ++ tailWord_6727100) baseStart_6727100 baseEnd_6727100 := by
    simpa [prefixWord, tailWord_6727100, baseEnd_6727100] using wordTrace_append hprefix tailTrace_6727100
  have hstable : (prefixWord ++ tailWord_6727100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727100).length < 2 ^ (prefixWord ++ tailWord_6727100).sum := by decide
  have hdescent : baseEnd_6727100 < baseStart_6727100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727125 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 2, 7]
def baseStart_6727125 : Nat := 118140960795 + 6727125 * 2 ^ 59
def prefixEnd_6727125 : Nat := 4983230072969 + 3 ^ 40 * 6727125 * 2
def baseEnd_6727125 : Nat := 1151416182625699275400007

theorem tailTrace_6727125 : CollatzResearch.WordTrace tailWord_6727125 prefixEnd_6727125 1151416182625699275400007 := by
  unfold tailWord_6727125
  simp only [CollatzResearch.WordTrace]
  refine ⟨245358405753782501326390829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163572270502521667550927219 245358405753782501326390829)
  ·
    refine ⟨92009402157668437997396561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245358405753782501326390829 92009402157668437997396561)
    ·
      refine ⟨69007051618251328498047421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92009402157668437997396561 69007051618251328498047421)
      ·
        refine ⟨25877644356844248186767783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69007051618251328498047421 25877644356844248186767783)
        ·
          refine ⟨38816466535266372280151675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25877644356844248186767783 38816466535266372280151675)
          ·
            refine ⟨58224699802899558420227513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38816466535266372280151675 58224699802899558420227513)
            ·
              refine ⟨43668524852174668815170635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58224699802899558420227513 43668524852174668815170635)
              ·
                refine ⟨65502787278262003222755953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43668524852174668815170635 65502787278262003222755953)
                ·
                  refine ⟨49127090458696502417066965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65502787278262003222755953 49127090458696502417066965)
                  ·
                    refine ⟨1151416182625699275400007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49127090458696502417066965 1151416182625699275400007)
                    ·
                      rfl

theorem cell23_6727125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_6727125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727125 prefixEnd_6727125 := by exact prefixLift 6727125
  have htrace : WordTrace (prefixWord ++ tailWord_6727125) baseStart_6727125 baseEnd_6727125 := by
    simpa [prefixWord, tailWord_6727125, baseEnd_6727125] using wordTrace_append hprefix tailTrace_6727125
  have hstable : (prefixWord ++ tailWord_6727125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727125).length < 2 ^ (prefixWord ++ tailWord_6727125).sum := by decide
  have hdescent : baseEnd_6727125 < baseStart_6727125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727174 : List Nat := [6, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_6727174 : Nat := 118140960795 + 6727174 * 2 ^ 59
def prefixEnd_6727174 : Nat := 4983230072969 + 3 ^ 40 * 6727174 * 2
def baseEnd_6727174 : Nat := 3454273708429168134487297

theorem tailTrace_6727174 : CollatzResearch.WordTrace tailWord_6727174 prefixEnd_6727174 3454273708429168134487297 := by
  unfold tailWord_6727174
  simp only [CollatzResearch.WordTrace]
  refine ⟨7667506029081405709216393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 163573461953736655129949717 7667506029081405709216393)
  ·
    refine ⟨5750629521811054281912295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7667506029081405709216393 5750629521811054281912295)
    ·
      refine ⟨8625944282716581422868443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5750629521811054281912295 8625944282716581422868443)
      ·
        refine ⟨12938916424074872134302665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8625944282716581422868443 12938916424074872134302665)
        ·
          refine ⟨9704187318056154100726999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12938916424074872134302665 9704187318056154100726999)
          ·
            refine ⟨14556280977084231151090499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9704187318056154100726999 14556280977084231151090499)
            ·
              refine ⟨21834421465626346726635749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14556280977084231151090499 21834421465626346726635749)
              ·
                refine ⟨4093954024804940011244203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21834421465626346726635749 4093954024804940011244203)
                ·
                  refine ⟨6140931037207410016866305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4093954024804940011244203 6140931037207410016866305)
                  ·
                    refine ⟨4605698277905557512649729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6140931037207410016866305 4605698277905557512649729)
                    ·
                      refine ⟨3454273708429168134487297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4605698277905557512649729 3454273708429168134487297)
                      ·
                        rfl

theorem cell23_6727174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_6727174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727174 prefixEnd_6727174 := by exact prefixLift 6727174
  have htrace : WordTrace (prefixWord ++ tailWord_6727174) baseStart_6727174 baseEnd_6727174 := by
    simpa [prefixWord, tailWord_6727174, baseEnd_6727174] using wordTrace_append hprefix tailTrace_6727174
  have hstable : (prefixWord ++ tailWord_6727174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727174).length < 2 ^ (prefixWord ++ tailWord_6727174).sum := by decide
  have hdescent : baseEnd_6727174 < baseStart_6727174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727185 : List Nat := [1, 2, 2, 1, 1, 2, 4, 3, 7]
def baseStart_6727185 : Nat := 118140960795 + 6727185 * 2 ^ 59
def prefixEnd_6727185 : Nat := 4983230072969 + 3 ^ 40 * 6727185 * 2
def baseEnd_6727185 : Nat := 383808817412929732383305

theorem tailTrace_6727185 : CollatzResearch.WordTrace tailWord_6727185 prefixEnd_6727185 383808817412929732383305 := by
  unfold tailWord_6727185
  simp only [CollatzResearch.WordTrace]
  refine ⟨245360594133565131573575009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163573729422376754382383339 245360594133565131573575009)
  ·
    refine ⟨184020445600173848680181257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245360594133565131573575009 184020445600173848680181257)
    ·
      refine ⟨138015334200130386510135943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184020445600173848680181257 138015334200130386510135943)
      ·
        refine ⟨207023001300195579765203915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138015334200130386510135943 207023001300195579765203915)
        ·
          refine ⟨310534501950293369647805873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207023001300195579765203915 310534501950293369647805873)
          ·
            refine ⟨232900876462720027235854405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310534501950293369647805873 232900876462720027235854405)
            ·
              refine ⟨43668914336760005106722701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232900876462720027235854405 43668914336760005106722701)
              ·
                refine ⟨16375842876285001915021013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43668914336760005106722701 16375842876285001915021013)
                ·
                  refine ⟨383808817412929732383305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16375842876285001915021013 383808817412929732383305)
                  ·
                    rfl

theorem cell23_6727185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 7].length) (baseStart_6727185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727185 prefixEnd_6727185 := by exact prefixLift 6727185
  have htrace : WordTrace (prefixWord ++ tailWord_6727185) baseStart_6727185 baseEnd_6727185 := by
    simpa [prefixWord, tailWord_6727185, baseEnd_6727185] using wordTrace_append hprefix tailTrace_6727185
  have hstable : (prefixWord ++ tailWord_6727185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727185).length < 2 ^ (prefixWord ++ tailWord_6727185).sum := by decide
  have hdescent : baseEnd_6727185 < baseStart_6727185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727196 : List Nat := [2, 2, 3, 1, 2, 1, 1, 5, 2, 2, 2]
def baseStart_6727196 : Nat := 118140960795 + 6727196 * 2 ^ 59
def prefixEnd_6727196 : Nat := 4983230072969 + 3 ^ 40 * 6727196 * 2
def baseEnd_6727196 : Nat := 3454285005003567048412195

theorem tailTrace_6727196 : CollatzResearch.WordTrace tailWord_6727196 prefixEnd_6727196 3454285005003567048412195 := by
  unfold tailWord_6727196
  simp only [CollatzResearch.WordTrace]
  refine ⟨122680497668262640226112721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163573996891016853634816961 122680497668262640226112721)
  ·
    refine ⟨92010373251196980169584541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122680497668262640226112721 92010373251196980169584541)
    ·
      refine ⟨34503889969198867563594203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92010373251196980169584541 34503889969198867563594203)
      ·
        refine ⟨51755834953798301345391305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34503889969198867563594203 51755834953798301345391305)
        ·
          refine ⟨38816876215348726009043479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51755834953798301345391305 38816876215348726009043479)
          ·
            refine ⟨58225314323023089013565219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38816876215348726009043479 58225314323023089013565219)
            ·
              refine ⟨87337971484534633520347829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58225314323023089013565219 87337971484534633520347829)
              ·
                refine ⟨8187934826675121892532609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87337971484534633520347829 8187934826675121892532609)
                ·
                  refine ⟨6140951120006341419399457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8187934826675121892532609 6140951120006341419399457)
                  ·
                    refine ⟨4605713340004756064549593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6140951120006341419399457 4605713340004756064549593)
                    ·
                      refine ⟨3454285005003567048412195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4605713340004756064549593 3454285005003567048412195)
                      ·
                        rfl

theorem cell23_6727196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_6727196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727196 prefixEnd_6727196 := by exact prefixLift 6727196
  have htrace : WordTrace (prefixWord ++ tailWord_6727196) baseStart_6727196 baseEnd_6727196 := by
    simpa [prefixWord, tailWord_6727196, baseEnd_6727196] using wordTrace_append hprefix tailTrace_6727196
  have hstable : (prefixWord ++ tailWord_6727196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727196).length < 2 ^ (prefixWord ++ tailWord_6727196).sum := by decide
  have hdescent : baseEnd_6727196 < baseStart_6727196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727219 : List Nat := [1, 1, 1, 2, 4, 4, 2, 3, 5]
def baseStart_6727219 : Nat := 118140960795 + 6727219 * 2 ^ 59
def prefixEnd_6727219 : Nat := 4983230072969 + 3 ^ 40 * 6727219 * 2
def baseEnd_6727219 : Nat := 383810757228735606491621

theorem tailTrace_6727219 : CollatzResearch.WordTrace tailWord_6727219 prefixEnd_6727219 383810757228735606491621 := by
  unfold tailWord_6727219
  simp only [CollatzResearch.WordTrace]
  refine ⟨245361834215441955380312711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163574556143627970253541807 245361834215441955380312711)
  ·
    refine ⟨368042751323162933070469067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245361834215441955380312711 368042751323162933070469067)
    ·
      refine ⟨552064126984744399605703601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368042751323162933070469067 552064126984744399605703601)
      ·
        refine ⟨414048095238558299704277701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 552064126984744399605703601 414048095238558299704277701)
        ·
          refine ⟨77634017857229681194552069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 414048095238558299704277701 77634017857229681194552069)
          ·
            refine ⟨14556378348230565223978513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77634017857229681194552069 14556378348230565223978513)
            ·
              refine ⟨10917283761172923917983885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14556378348230565223978513 10917283761172923917983885)
              ·
                refine ⟨4093981410439846469243957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10917283761172923917983885 4093981410439846469243957)
                ·
                  refine ⟨383810757228735606491621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4093981410439846469243957 383810757228735606491621)
                  ·
                    rfl

theorem cell23_6727219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 5].length) (baseStart_6727219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727219 prefixEnd_6727219 := by exact prefixLift 6727219
  have htrace : WordTrace (prefixWord ++ tailWord_6727219) baseStart_6727219 baseEnd_6727219 := by
    simpa [prefixWord, tailWord_6727219, baseEnd_6727219] using wordTrace_append hprefix tailTrace_6727219
  have hstable : (prefixWord ++ tailWord_6727219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727219).length < 2 ^ (prefixWord ++ tailWord_6727219).sum := by decide
  have hdescent : baseEnd_6727219 < baseStart_6727219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727252 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_6727252 : Nat := 118140960795 + 6727252 * 2 ^ 59
def prefixEnd_6727252 : Nat := 4983230072969 + 3 ^ 40 * 6727252 * 2
def baseEnd_6727252 : Nat := 3454313759920218829311937

theorem tailTrace_6727252 : CollatzResearch.WordTrace tailWord_6727252 prefixEnd_6727252 3454313759920218829311937 := by
  unfold tailWord_6727252
  simp only [CollatzResearch.WordTrace]
  refine ⟨122681518912161201008132005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163575358549548268010842673 122681518912161201008132005)
  ·
    refine ⟨23002784796030225189024751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122681518912161201008132005 23002784796030225189024751)
    ·
      refine ⟨34504177194045337783537127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23002784796030225189024751 34504177194045337783537127)
      ·
        refine ⟨51756265791068006675305691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34504177194045337783537127 51756265791068006675305691)
        ·
          refine ⟨77634398686602010012958537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51756265791068006675305691 77634398686602010012958537)
          ·
            refine ⟨58225799014951507509718903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77634398686602010012958537 58225799014951507509718903)
            ·
              refine ⟨87338698522427261264578355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58225799014951507509718903 87338698522427261264578355)
              ·
                refine ⟨131008047783640891896867533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87338698522427261264578355 131008047783640891896867533)
                ·
                  refine ⟨49128017918865334461325325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131008047783640891896867533 49128017918865334461325325)
                  ·
                    refine ⟨18423006719574500422996997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49128017918865334461325325 18423006719574500422996997)
                    ·
                      refine ⟨3454313759920218829311937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18423006719574500422996997 3454313759920218829311937)
                      ·
                        rfl

theorem cell23_6727252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_6727252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727252 prefixEnd_6727252 := by exact prefixLift 6727252
  have htrace : WordTrace (prefixWord ++ tailWord_6727252) baseStart_6727252 baseEnd_6727252 := by
    simpa [prefixWord, tailWord_6727252, baseEnd_6727252] using wordTrace_append hprefix tailTrace_6727252
  have hstable : (prefixWord ++ tailWord_6727252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727252).length < 2 ^ (prefixWord ++ tailWord_6727252).sum := by decide
  have hdescent : baseEnd_6727252 < baseStart_6727252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727286 : List Nat := [5, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_6727286 : Nat := 118140960795 + 6727286 * 2 ^ 59
def prefixEnd_6727286 : Nat := 4983230072969 + 3 ^ 40 * 6727286 * 2
def baseEnd_6727286 : Nat := 3454331218262471696286781

theorem tailTrace_6727286 : CollatzResearch.WordTrace tailWord_6727286 prefixEnd_6727286 3454331218262471696286781 := by
  unfold tailWord_6727286
  simp only [CollatzResearch.WordTrace]
  refine ⟨15335267369137451613937607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163576185270799483882001141 15335267369137451613937607)
  ·
    refine ⟨23002901053706177420906411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15335267369137451613937607 23002901053706177420906411)
    ·
      refine ⟨34504351580559266131359617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23002901053706177420906411 34504351580559266131359617)
      ·
        refine ⟨25878263685419449598519713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34504351580559266131359617 25878263685419449598519713)
        ·
          refine ⟨19408697764064587198889785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25878263685419449598519713 19408697764064587198889785)
          ·
            refine ⟨14556523323048440399167339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19408697764064587198889785 14556523323048440399167339)
            ·
              refine ⟨21834784984572660598751009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14556523323048440399167339 21834784984572660598751009)
              ·
                refine ⟨16376088738429495449063257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21834784984572660598751009 16376088738429495449063257)
                ·
                  refine ⟨12282066553822121586797443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16376088738429495449063257 12282066553822121586797443)
                  ·
                    refine ⟨18423099830733182380196165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12282066553822121586797443 18423099830733182380196165)
                    ·
                      refine ⟨3454331218262471696286781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18423099830733182380196165 3454331218262471696286781)
                      ·
                        rfl

theorem cell23_6727286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_6727286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727286 prefixEnd_6727286 := by exact prefixLift 6727286
  have htrace : WordTrace (prefixWord ++ tailWord_6727286) baseStart_6727286 baseEnd_6727286 := by
    simpa [prefixWord, tailWord_6727286, baseEnd_6727286] using wordTrace_append hprefix tailTrace_6727286
  have hstable : (prefixWord ++ tailWord_6727286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727286).length < 2 ^ (prefixWord ++ tailWord_6727286).sum := by decide
  have hdescent : baseEnd_6727286 < baseStart_6727286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727289 : List Nat := [1, 2, 1, 3, 3, 1, 3, 2, 2, 2, 3]
def baseStart_6727289 : Nat := 118140960795 + 6727289 * 2 ^ 59
def prefixEnd_6727289 : Nat := 4983230072969 + 3 ^ 40 * 6727289 * 2
def baseEnd_6727289 : Nat := 3454332758704435184549267

theorem tailTrace_6727289 : CollatzResearch.WordTrace tailWord_6727289 prefixEnd_6727289 3454332758704435184549267 := by
  unfold tailWord_6727289
  simp only [CollatzResearch.WordTrace]
  refine ⟨245364387325188357335360921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163576258216792238223573947 245364387325188357335360921)
  ·
    refine ⟨184023290493891268001520691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245364387325188357335360921 184023290493891268001520691)
    ·
      refine ⟨276034935740836902002281037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184023290493891268001520691 276034935740836902002281037)
      ·
        refine ⟨103513100902813838250855389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276034935740836902002281037 103513100902813838250855389)
        ·
          refine ⟨38817412838555189344070771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103513100902813838250855389 38817412838555189344070771)
          ·
            refine ⟨58226119257832784016106157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38817412838555189344070771 58226119257832784016106157)
            ·
              refine ⟨21834794721687294006039809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58226119257832784016106157 21834794721687294006039809)
              ·
                refine ⟨16376096041265470504529857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21834794721687294006039809 16376096041265470504529857)
                ·
                  refine ⟨12282072030949102878397393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16376096041265470504529857 12282072030949102878397393)
                  ·
                    refine ⟨9211554023211827158798045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12282072030949102878397393 9211554023211827158798045)
                    ·
                      refine ⟨3454332758704435184549267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9211554023211827158798045 3454332758704435184549267)
                      ·
                        rfl

theorem cell23_6727289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_6727289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727289 prefixEnd_6727289 := by exact prefixLift 6727289
  have htrace : WordTrace (prefixWord ++ tailWord_6727289) baseStart_6727289 baseEnd_6727289 := by
    simpa [prefixWord, tailWord_6727289, baseEnd_6727289] using wordTrace_append hprefix tailTrace_6727289
  have hstable : (prefixWord ++ tailWord_6727289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727289).length < 2 ^ (prefixWord ++ tailWord_6727289).sum := by decide
  have hdescent : baseEnd_6727289 < baseStart_6727289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727292 : List Nat := [2, 2, 2, 1, 1, 2, 1, 6, 6]
def baseStart_6727292 : Nat := 118140960795 + 6727292 * 2 ^ 59
def prefixEnd_6727292 : Nat := 4983230072969 + 3 ^ 40 * 6727292 * 2
def baseEnd_6727292 : Nat := 383814922127377630312417

theorem tailTrace_6727292 : CollatzResearch.WordTrace tailWord_6727292 prefixEnd_6727292 383814922127377630312417 := by
  unfold tailWord_6727292
  simp only [CollatzResearch.WordTrace]
  refine ⟨122682248372088744423860065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163576331162784992565146753 122682248372088744423860065)
  ·
    refine ⟨92011686279066558317895049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122682248372088744423860065 92011686279066558317895049)
    ·
      refine ⟨69008764709299918738421287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92011686279066558317895049 69008764709299918738421287)
      ·
        refine ⟨103513147063949878107631931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69008764709299918738421287 103513147063949878107631931)
        ·
          refine ⟨155269720595924817161447897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103513147063949878107631931 155269720595924817161447897)
          ·
            refine ⟨116452290446943612871085923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155269720595924817161447897 116452290446943612871085923)
            ·
              refine ⟨174678435670415419306628885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116452290446943612871085923 174678435670415419306628885)
              ·
                refine ⟨8188051672050722779998229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 174678435670415419306628885 8188051672050722779998229)
                ·
                  refine ⟨383814922127377630312417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8188051672050722779998229 383814922127377630312417)
                  ·
                    rfl

theorem cell23_6727292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 6].length) (baseStart_6727292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727292 prefixEnd_6727292 := by exact prefixLift 6727292
  have htrace : WordTrace (prefixWord ++ tailWord_6727292) baseStart_6727292 baseEnd_6727292 := by
    simpa [prefixWord, tailWord_6727292, baseEnd_6727292] using wordTrace_append hprefix tailTrace_6727292
  have hstable : (prefixWord ++ tailWord_6727292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727292).length < 2 ^ (prefixWord ++ tailWord_6727292).sum := by decide
  have hdescent : baseEnd_6727292 < baseStart_6727292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727346 : List Nat := [3, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2]
def baseStart_6727346 : Nat := 118140960795 + 6727346 * 2 ^ 59
def prefixEnd_6727346 : Nat := 4983230072969 + 3 ^ 40 * 6727346 * 2
def baseEnd_6727346 : Nat := 3454362027101741461536505

theorem tailTrace_6727346 : CollatzResearch.WordTrace tailWord_6727346 prefixEnd_6727346 3454362027101741461536505 := by
  unfold tailWord_6727346
  simp only [CollatzResearch.WordTrace]
  refine ⟨61341616571495464017546473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163577644190654570713457261 61341616571495464017546473)
  ·
    refine ⟨46006212428621598013159855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61341616571495464017546473 46006212428621598013159855)
    ·
      refine ⟨69009318642932397019739783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46006212428621598013159855 69009318642932397019739783)
      ·
        refine ⟨103513977964398595529609675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69009318642932397019739783 103513977964398595529609675)
        ·
          refine ⟨155270966946597893294414513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103513977964398595529609675 155270966946597893294414513)
          ·
            refine ⟨116453225209948419970810885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155270966946597893294414513 116453225209948419970810885)
            ·
              refine ⟨21834979726865328744527041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116453225209948419970810885 21834979726865328744527041)
              ·
                refine ⟨16376234795148996558395281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21834979726865328744527041 16376234795148996558395281)
                ·
                  refine ⟨12282176096361747418796461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16376234795148996558395281 12282176096361747418796461)
                  ·
                    refine ⟨4605816036135655282048673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12282176096361747418796461 4605816036135655282048673)
                    ·
                      refine ⟨3454362027101741461536505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4605816036135655282048673 3454362027101741461536505)
                      ·
                        rfl

theorem cell23_6727346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2].length) (baseStart_6727346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727346 prefixEnd_6727346 := by exact prefixLift 6727346
  have htrace : WordTrace (prefixWord ++ tailWord_6727346) baseStart_6727346 baseEnd_6727346 := by
    simpa [prefixWord, tailWord_6727346, baseEnd_6727346] using wordTrace_append hprefix tailTrace_6727346
  have hstable : (prefixWord ++ tailWord_6727346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727346).length < 2 ^ (prefixWord ++ tailWord_6727346).sum := by decide
  have hdescent : baseEnd_6727346 < baseStart_6727346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727380 : List Nat := [2, 4, 1, 3, 1, 3, 1, 1, 2, 3, 2]
def baseStart_6727380 : Nat := 118140960795 + 6727380 * 2 ^ 59
def prefixEnd_6727380 : Nat := 4983230072969 + 3 ^ 40 * 6727380 * 2
def baseEnd_6727380 : Nat := 3454379485443994328511349

theorem tailTrace_6727380 : CollatzResearch.WordTrace tailWord_6727380 prefixEnd_6727380 3454379485443994328511349 := by
  unfold tailWord_6727380
  simp only [CollatzResearch.WordTrace]
  refine ⟨122683853183929339938461797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163578470911905786584615729 122683853183929339938461797)
  ·
    refine ⟨23003222471986751238461587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122683853183929339938461797 23003222471986751238461587)
    ·
      refine ⟨34504833707980126857692381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23003222471986751238461587 34504833707980126857692381)
      ·
        refine ⟨12939312640492547571634643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34504833707980126857692381 12939312640492547571634643)
        ·
          refine ⟨19408968960738821357451965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12939312640492547571634643 19408968960738821357451965)
          ·
            refine ⟨7278363360277058009044487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19408968960738821357451965 7278363360277058009044487)
            ·
              refine ⟨10917545040415587013566731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7278363360277058009044487 10917545040415587013566731)
              ·
                refine ⟨16376317560623380520350097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10917545040415587013566731 16376317560623380520350097)
                ·
                  refine ⟨12282238170467535390262573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16376317560623380520350097 12282238170467535390262573)
                  ·
                    refine ⟨4605839313925325771348465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12282238170467535390262573 4605839313925325771348465)
                    ·
                      refine ⟨3454379485443994328511349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4605839313925325771348465 3454379485443994328511349)
                      ·
                        rfl

theorem cell23_6727380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_6727380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727380 prefixEnd_6727380 := by exact prefixLift 6727380
  have htrace : WordTrace (prefixWord ++ tailWord_6727380) baseStart_6727380 baseEnd_6727380 := by
    simpa [prefixWord, tailWord_6727380, baseEnd_6727380] using wordTrace_append hprefix tailTrace_6727380
  have hstable : (prefixWord ++ tailWord_6727380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727380).length < 2 ^ (prefixWord ++ tailWord_6727380).sum := by decide
  have hdescent : baseEnd_6727380 < baseStart_6727380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727396 : List Nat := [2, 3, 1, 1, 1, 3, 3, 3, 1, 2, 3]
def baseStart_6727396 : Nat := 118140960795 + 6727396 * 2 ^ 59
def prefixEnd_6727396 : Nat := 4983230072969 + 3 ^ 40 * 6727396 * 2
def baseEnd_6727396 : Nat := 3454387701134466265911275

theorem tailTrace_6727396 : CollatzResearch.WordTrace tailWord_6727396 prefixEnd_6727396 3454387701134466265911275 := by
  unfold tailWord_6727396
  simp only [CollatzResearch.WordTrace]
  refine ⟨122684144967900357304753021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163578859957200476406337361 122684144967900357304753021)
  ·
    refine ⟨46006554362962633989282383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122684144967900357304753021 46006554362962633989282383)
    ·
      refine ⟨69009831544443950983923575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46006554362962633989282383 69009831544443950983923575)
      ·
        refine ⟨103514747316665926475885363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69009831544443950983923575 103514747316665926475885363)
        ·
          refine ⟨155272120974998889713828045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103514747316665926475885363 155272120974998889713828045)
          ·
            refine ⟨58227045365624583642685517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155272120974998889713828045 58227045365624583642685517)
            ·
              refine ⟨21835142012109218866007069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58227045365624583642685517 21835142012109218866007069)
              ·
                refine ⟨8188178254540957074752651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21835142012109218866007069 8188178254540957074752651)
                ·
                  refine ⟨12282267381811435612128977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8188178254540957074752651 12282267381811435612128977)
                  ·
                    refine ⟨9211700536358576709096733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12282267381811435612128977 9211700536358576709096733)
                    ·
                      refine ⟨3454387701134466265911275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9211700536358576709096733 3454387701134466265911275)
                      ·
                        rfl

theorem cell23_6727396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_6727396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727396 prefixEnd_6727396 := by exact prefixLift 6727396
  have htrace : WordTrace (prefixWord ++ tailWord_6727396) baseStart_6727396 baseEnd_6727396 := by
    simpa [prefixWord, tailWord_6727396, baseEnd_6727396] using wordTrace_append hprefix tailTrace_6727396
  have hstable : (prefixWord ++ tailWord_6727396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727396).length < 2 ^ (prefixWord ++ tailWord_6727396).sum := by decide
  have hdescent : baseEnd_6727396 < baseStart_6727396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727410 : List Nat := [3, 2, 1, 3, 1, 1, 1, 6, 1, 2, 2]
def baseStart_6727410 : Nat := 118140960795 + 6727410 * 2 ^ 59
def prefixEnd_6727410 : Nat := 4983230072969 + 3 ^ 40 * 6727410 * 2
def baseEnd_6727410 : Nat := 3454394889863629211136211

theorem tailTrace_6727410 : CollatzResearch.WordTrace tailWord_6727410 prefixEnd_6727410 3454394889863629211136211 := by
  unfold tailWord_6727410
  simp only [CollatzResearch.WordTrace]
  refine ⟨61342200139437498750128921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163579200371833330000343789 61342200139437498750128921)
  ·
    refine ⟨46006650104578124062596691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61342200139437498750128921 46006650104578124062596691)
    ·
      refine ⟨69009975156867186093895037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46006650104578124062596691 69009975156867186093895037)
      ·
        refine ⟨25878740683825194785210639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69009975156867186093895037 25878740683825194785210639)
        ·
          refine ⟨38818111025737792177815959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25878740683825194785210639 38818111025737792177815959)
          ·
            refine ⟨58227166538606688266723939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38818111025737792177815959 58227166538606688266723939)
            ·
              refine ⟨87340749807910032400085909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58227166538606688266723939 87340749807910032400085909)
              ·
                refine ⟨4094097647245782768754027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87340749807910032400085909 4094097647245782768754027)
                ·
                  refine ⟨6141146470868674153131041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4094097647245782768754027 6141146470868674153131041)
                  ·
                    refine ⟨4605859853151505614848281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6141146470868674153131041 4605859853151505614848281)
                    ·
                      refine ⟨3454394889863629211136211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4605859853151505614848281 3454394889863629211136211)
                      ·
                        rfl

theorem cell23_6727410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_6727410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727410 prefixEnd_6727410 := by exact prefixLift 6727410
  have htrace : WordTrace (prefixWord ++ tailWord_6727410) baseStart_6727410 baseEnd_6727410 := by
    simpa [prefixWord, tailWord_6727410, baseEnd_6727410] using wordTrace_append hprefix tailTrace_6727410
  have hstable : (prefixWord ++ tailWord_6727410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727410).length < 2 ^ (prefixWord ++ tailWord_6727410).sum := by decide
  have hdescent : baseEnd_6727410 < baseStart_6727410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727419 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 2, 7, 2]
def baseStart_6727419 : Nat := 118140960795 + 6727419 * 2 ^ 59
def prefixEnd_6727419 : Nat := 4983230072969 + 3 ^ 40 * 6727419 * 2
def baseEnd_6727419 : Nat := 3454399511189519675923669

theorem tailTrace_6727419 : CollatzResearch.WordTrace tailWord_6727419 prefixEnd_6727419 3454399511189519675923669 := by
  unfold tailWord_6727419
  simp only [CollatzResearch.WordTrace]
  refine ⟨245369128814717389537593311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163579419209811593025062207 245369128814717389537593311)
  ·
    refine ⟨368053693222076084306389967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245369128814717389537593311 368053693222076084306389967)
    ·
      refine ⟨552080539833114126459584951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368053693222076084306389967 552080539833114126459584951)
      ·
        refine ⟨828120809749671189689377427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552080539833114126459584951 828120809749671189689377427)
        ·
          refine ⟨1242181214624506784534066141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 828120809749671189689377427 1242181214624506784534066141)
          ·
            refine ⟨465817955484190044200274803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1242181214624506784534066141 465817955484190044200274803)
            ·
              refine ⟨698726933226285066300412205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465817955484190044200274803 698726933226285066300412205)
              ·
                refine ⟨262022599959856899862654577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 698726933226285066300412205 262022599959856899862654577)
                ·
                  refine ⟨196516949969892674896990933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262022599959856899862654577 196516949969892674896990933)
                  ·
                    refine ⟨4605866014919359567898225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 196516949969892674896990933 4605866014919359567898225)
                    ·
                      refine ⟨3454399511189519675923669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4605866014919359567898225 3454399511189519675923669)
                      ·
                        rfl

theorem cell23_6727419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 7, 2].length) (baseStart_6727419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727419 prefixEnd_6727419 := by exact prefixLift 6727419
  have htrace : WordTrace (prefixWord ++ tailWord_6727419) baseStart_6727419 baseEnd_6727419 := by
    simpa [prefixWord, tailWord_6727419, baseEnd_6727419] using wordTrace_append hprefix tailTrace_6727419
  have hstable : (prefixWord ++ tailWord_6727419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727419).length < 2 ^ (prefixWord ++ tailWord_6727419).sum := by decide
  have hdescent : baseEnd_6727419 < baseStart_6727419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727436 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 3, 3, 2]
def baseStart_6727436 : Nat := 118140960795 + 6727436 * 2 ^ 59
def prefixEnd_6727436 : Nat := 4983230072969 + 3 ^ 40 * 6727436 * 2
def baseEnd_6727436 : Nat := 3454408240360646109411091

theorem tailTrace_6727436 : CollatzResearch.WordTrace tailWord_6727436 prefixEnd_6727436 3454408240360646109411091 := by
  unfold tailWord_6727436
  simp only [CollatzResearch.WordTrace]
  refine ⟨122684874427827900720481081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163579832570437200960641441 122684874427827900720481081)
  ·
    refine ⟨92013655820870925540360811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122684874427827900720481081 92013655820870925540360811)
    ·
      refine ⟨138020483731306388310541217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92013655820870925540360811 138020483731306388310541217)
      ·
        refine ⟨103515362798479791232905913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138020483731306388310541217 103515362798479791232905913)
        ·
          refine ⟨77636522098859843424679435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103515362798479791232905913 77636522098859843424679435)
          ·
            refine ⟨116454783148289765137019153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77636522098859843424679435 116454783148289765137019153)
            ·
              refine ⟨87341087361217323852764365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116454783148289765137019153 87341087361217323852764365)
              ·
                refine ⟨32752907760456496444786637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87341087361217323852764365 32752907760456496444786637)
                ·
                  refine ⟨12282340410171186166794989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32752907760456496444786637 12282340410171186166794989)
                  ·
                    refine ⟨4605877653814194812548121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12282340410171186166794989 4605877653814194812548121)
                    ·
                      refine ⟨3454408240360646109411091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4605877653814194812548121 3454408240360646109411091)
                      ·
                        rfl

theorem cell23_6727436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 3, 3, 2].length) (baseStart_6727436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727436 prefixEnd_6727436 := by exact prefixLift 6727436
  have htrace : WordTrace (prefixWord ++ tailWord_6727436) baseStart_6727436 baseEnd_6727436 := by
    simpa [prefixWord, tailWord_6727436, baseEnd_6727436] using wordTrace_append hprefix tailTrace_6727436
  have hstable : (prefixWord ++ tailWord_6727436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727436).length < 2 ^ (prefixWord ++ tailWord_6727436).sum := by decide
  have hdescent : baseEnd_6727436 < baseStart_6727436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727477 : List Nat := [1, 3, 3, 1, 4, 2, 2, 1, 2, 1, 3]
def baseStart_6727477 : Nat := 118140960795 + 6727477 * 2 ^ 59
def prefixEnd_6727477 : Nat := 4983230072969 + 3 ^ 40 * 6727477 * 2
def baseEnd_6727477 : Nat := 3454429293067480448998403

theorem tailTrace_6727477 : CollatzResearch.WordTrace tailWord_6727477 prefixEnd_6727477 3454429293067480448998403 := by
  unfold tailWord_6727477
  simp only [CollatzResearch.WordTrace]
  refine ⟨245371244248507265443204685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163580829499004843628803123 245371244248507265443204685)
  ·
    refine ⟨92014216593190224541201757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245371244248507265443204685 92014216593190224541201757)
    ·
      refine ⟨34505331222446334202950659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92014216593190224541201757 34505331222446334202950659)
      ·
        refine ⟨51757996833669501304425989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34505331222446334202950659 51757996833669501304425989)
        ·
          refine ⟨9704624406313031494579873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51757996833669501304425989 9704624406313031494579873)
          ·
            refine ⟨7278468304734773620934905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9704624406313031494579873 7278468304734773620934905)
            ·
              refine ⟨5458851228551080215701179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7278468304734773620934905 5458851228551080215701179)
              ·
                refine ⟨8188276842826620323551769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5458851228551080215701179 8188276842826620323551769)
                ·
                  refine ⟨6141207632119965242663827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8188276842826620323551769 6141207632119965242663827)
                  ·
                    refine ⟨9211811448179947863995741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6141207632119965242663827 9211811448179947863995741)
                    ·
                      refine ⟨3454429293067480448998403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9211811448179947863995741 3454429293067480448998403)
                      ·
                        rfl

theorem cell23_6727477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_6727477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727477 prefixEnd_6727477 := by exact prefixLift 6727477
  have htrace : WordTrace (prefixWord ++ tailWord_6727477) baseStart_6727477 baseEnd_6727477 := by
    simpa [prefixWord, tailWord_6727477, baseEnd_6727477] using wordTrace_append hprefix tailTrace_6727477
  have hstable : (prefixWord ++ tailWord_6727477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727477).length < 2 ^ (prefixWord ++ tailWord_6727477).sum := by decide
  have hdescent : baseEnd_6727477 < baseStart_6727477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727486 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_6727486 : Nat := 118140960795 + 6727486 * 2 ^ 59
def prefixEnd_6727486 : Nat := 4983230072969 + 3 ^ 40 * 6727486 * 2
def baseEnd_6727486 : Nat := 3454433914393370913785861

theorem tailTrace_6727486 : CollatzResearch.WordTrace tailWord_6727486 prefixEnd_6727486 3454433914393370913785861 := by
  unfold tailWord_6727486
  simp only [CollatzResearch.WordTrace]
  refine ⟨30671446563184332497535289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163581048336983106653521541 30671446563184332497535289)
  ·
    refine ⟨23003584922388249373151467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30671446563184332497535289 23003584922388249373151467)
    ·
      refine ⟨34505377383582374059727201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23003584922388249373151467 34505377383582374059727201)
      ·
        refine ⟨25879033037686780544795401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34505377383582374059727201 25879033037686780544795401)
        ·
          refine ⟨19409274778265085408596551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25879033037686780544795401 19409274778265085408596551)
          ·
            refine ⟨29113912167397628112894827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19409274778265085408596551 29113912167397628112894827)
            ·
              refine ⟨43670868251096442169342241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29113912167397628112894827 43670868251096442169342241)
              ·
                refine ⟨32753151188322331627006681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43670868251096442169342241 32753151188322331627006681)
                ·
                  refine ⟨24564863391241748720255011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32753151188322331627006681 24564863391241748720255011)
                  ·
                    refine ⟨36847295086862623080382517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24564863391241748720255011 36847295086862623080382517)
                    ·
                      refine ⟨3454433914393370913785861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36847295086862623080382517 3454433914393370913785861)
                      ·
                        rfl

theorem cell23_6727486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_6727486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727486 prefixEnd_6727486 := by exact prefixLift 6727486
  have htrace : WordTrace (prefixWord ++ tailWord_6727486) baseStart_6727486 baseEnd_6727486 := by
    simpa [prefixWord, tailWord_6727486, baseEnd_6727486] using wordTrace_append hprefix tailTrace_6727486
  have hstable : (prefixWord ++ tailWord_6727486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727486).length < 2 ^ (prefixWord ++ tailWord_6727486).sum := by decide
  have hdescent : baseEnd_6727486 < baseStart_6727486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727487 : List Nat := [1, 1, 2, 2, 7, 1, 1, 2, 1, 3, 2]
def baseStart_6727487 : Nat := 118140960795 + 6727487 * 2 ^ 59
def prefixEnd_6727487 : Nat := 4983230072969 + 3 ^ 40 * 6727487 * 2
def baseEnd_6727487 : Nat := 3454434427874025409873357

theorem tailTrace_6727487 : CollatzResearch.WordTrace tailWord_6727487 prefixEnd_6727487 3454434427874025409873357 := by
  unfold tailWord_6727487
  simp only [CollatzResearch.WordTrace]
  refine ⟨245371608978471037151068715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163581072652314024767379143 245371608978471037151068715)
  ·
    refine ⟨368057413467706555726603073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245371608978471037151068715 368057413467706555726603073)
    ·
      refine ⟨276043060100779916794952305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368057413467706555726603073 276043060100779916794952305)
      ·
        refine ⟨207032295075584937596214229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276043060100779916794952305 207032295075584937596214229)
        ·
          refine ⟨4852319415834021974911271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 207032295075584937596214229 4852319415834021974911271)
          ·
            refine ⟨7278479123751032962366907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4852319415834021974911271 7278479123751032962366907)
            ·
              refine ⟨10917718685626549443550361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7278479123751032962366907 10917718685626549443550361)
              ·
                refine ⟨8188289014219912082662771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10917718685626549443550361 8188289014219912082662771)
                ·
                  refine ⟨12282433521329868123994157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8188289014219912082662771 12282433521329868123994157)
                  ·
                    refine ⟨4605912570498700546497809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12282433521329868123994157 4605912570498700546497809)
                    ·
                      refine ⟨3454434427874025409873357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4605912570498700546497809 3454434427874025409873357)
                      ·
                        rfl

theorem cell23_6727487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 1, 3, 2].length) (baseStart_6727487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727487 prefixEnd_6727487 := by exact prefixLift 6727487
  have htrace : WordTrace (prefixWord ++ tailWord_6727487) baseStart_6727487 baseEnd_6727487 := by
    simpa [prefixWord, tailWord_6727487, baseEnd_6727487] using wordTrace_append hprefix tailTrace_6727487
  have hstable : (prefixWord ++ tailWord_6727487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727487).length < 2 ^ (prefixWord ++ tailWord_6727487).sum := by decide
  have hdescent : baseEnd_6727487 < baseStart_6727487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727523 : List Nat := [1, 1, 1, 5, 4, 1, 1, 4, 5]
def baseStart_6727523 : Nat := 118140960795 + 6727523 * 2 ^ 59
def prefixEnd_6727523 : Nat := 4983230072969 + 3 ^ 40 * 6727523 * 2
def baseEnd_6727523 : Nat := 383828101464176363224799

theorem tailTrace_6727523 : CollatzResearch.WordTrace tailWord_6727523 prefixEnd_6727523 383828101464176363224799 := by
  unfold tailWord_6727523
  simp only [CollatzResearch.WordTrace]
  refine ⟨245372922006340615299379223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163581948004227076866252815 245372922006340615299379223)
  ·
    refine ⟨368059383009510922949068835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245372922006340615299379223 368059383009510922949068835)
    ·
      refine ⟨552089074514266384423603253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368059383009510922949068835 552089074514266384423603253)
      ·
        refine ⟨51758350735712473539712805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 552089074514266384423603253 51758350735712473539712805)
        ·
          refine ⟨9704690762946088788696151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51758350735712473539712805 9704690762946088788696151)
          ·
            refine ⟨14557036144419133183044227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9704690762946088788696151 14557036144419133183044227)
            ·
              refine ⟨21835554216628699774566341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14557036144419133183044227 21835554216628699774566341)
              ·
                refine ⟨4094166415617881207731189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21835554216628699774566341 4094166415617881207731189)
                ·
                  refine ⟨383828101464176363224799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4094166415617881207731189 383828101464176363224799)
                  ·
                    rfl

theorem cell23_6727523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 5].length) (baseStart_6727523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727523 prefixEnd_6727523 := by exact prefixLift 6727523
  have htrace : WordTrace (prefixWord ++ tailWord_6727523) baseStart_6727523 baseEnd_6727523 := by
    simpa [prefixWord, tailWord_6727523, baseEnd_6727523] using wordTrace_append hprefix tailTrace_6727523
  have hstable : (prefixWord ++ tailWord_6727523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727523).length < 2 ^ (prefixWord ++ tailWord_6727523).sum := by decide
  have hdescent : baseEnd_6727523 < baseStart_6727523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727539 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 4]
def baseStart_6727539 : Nat := 118140960795 + 6727539 * 2 ^ 59
def prefixEnd_6727539 : Nat := 4983230072969 + 3 ^ 40 * 6727539 * 2
def baseEnd_6727539 : Nat := 3454461128868059206423117

theorem tailTrace_6727539 : CollatzResearch.WordTrace tailWord_6727539 prefixEnd_6727539 3454461128868059206423117 := by
  unfold tailWord_6727539
  simp only [CollatzResearch.WordTrace]
  refine ⟨245373505574282650031961671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163582337049521766687974447 245373505574282650031961671)
  ·
    refine ⟨368060258361423975047942507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245373505574282650031961671 368060258361423975047942507)
    ·
      refine ⟨552090387542135962571913761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368060258361423975047942507 552090387542135962571913761)
      ·
        refine ⟨414067790656601971928935321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 552090387542135962571913761 414067790656601971928935321)
        ·
          refine ⟨310550842992451478946701491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414067790656601971928935321 310550842992451478946701491)
          ·
            refine ⟨465826264488677218420052237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310550842992451478946701491 465826264488677218420052237)
            ·
              refine ⟨174684849183253956907519589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 465826264488677218420052237 174684849183253956907519589)
              ·
                refine ⟨32753409221860116920159923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174684849183253956907519589 32753409221860116920159923)
                ·
                  refine ⟨49130113832790175380239885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32753409221860116920159923 49130113832790175380239885)
                  ·
                    refine ⟨18423792687296315767589957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49130113832790175380239885 18423792687296315767589957)
                    ·
                      refine ⟨3454461128868059206423117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18423792687296315767589957 3454461128868059206423117)
                      ·
                        rfl

theorem cell23_6727539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 4].length) (baseStart_6727539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727539 prefixEnd_6727539 := by exact prefixLift 6727539
  have htrace : WordTrace (prefixWord ++ tailWord_6727539) baseStart_6727539 baseEnd_6727539 := by
    simpa [prefixWord, tailWord_6727539, baseEnd_6727539] using wordTrace_append hprefix tailTrace_6727539
  have hstable : (prefixWord ++ tailWord_6727539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727539).length < 2 ^ (prefixWord ++ tailWord_6727539).sum := by decide
  have hdescent : baseEnd_6727539 < baseStart_6727539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727553 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 1, 7]
def baseStart_6727553 : Nat := 118140960795 + 6727553 * 2 ^ 59
def prefixEnd_6727553 : Nat := 4983230072969 + 3 ^ 40 * 6727553 * 2
def baseEnd_6727553 : Nat := 1151489439199074050549351

theorem tailTrace_6727553 : CollatzResearch.WordTrace tailWord_6727553 prefixEnd_6727553 1151489439199074050549351 := by
  unfold tailWord_6727553
  simp only [CollatzResearch.WordTrace]
  refine ⟨245374016196231930422971313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163582677464154620281980875 245374016196231930422971313)
  ·
    refine ⟨184030512147173947817228485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245374016196231930422971313 184030512147173947817228485)
    ·
      refine ⟨34505721027595115215730341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184030512147173947817228485 34505721027595115215730341)
      ·
        refine ⟨6469822692674084102949439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34505721027595115215730341 6469822692674084102949439)
        ·
          refine ⟨9704734039011126154424159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6469822692674084102949439 9704734039011126154424159)
          ·
            refine ⟨14557101058516689231636239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9704734039011126154424159 14557101058516689231636239)
            ·
              refine ⟨21835651587775033847454359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14557101058516689231636239 21835651587775033847454359)
              ·
                refine ⟨32753477381662550771181539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21835651587775033847454359 32753477381662550771181539)
                ·
                  refine ⟨49130216072493826156772309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32753477381662550771181539 49130216072493826156772309)
                  ·
                    refine ⟨1151489439199074050549351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49130216072493826156772309 1151489439199074050549351)
                    ·
                      rfl

theorem cell23_6727553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_6727553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727553 prefixEnd_6727553 := by exact prefixLift 6727553
  have htrace : WordTrace (prefixWord ++ tailWord_6727553) baseStart_6727553 baseEnd_6727553 := by
    simpa [prefixWord, tailWord_6727553, baseEnd_6727553] using wordTrace_append hprefix tailTrace_6727553
  have hstable : (prefixWord ++ tailWord_6727553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727553).length < 2 ^ (prefixWord ++ tailWord_6727553).sum := by decide
  have hdescent : baseEnd_6727553 < baseStart_6727553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727569 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 6]
def baseStart_6727569 : Nat := 118140960795 + 6727569 * 2 ^ 59
def prefixEnd_6727569 : Nat := 4983230072969 + 3 ^ 40 * 6727569 * 2
def baseEnd_6727569 : Nat := 3454476533287694089047979

theorem tailTrace_6727569 : CollatzResearch.WordTrace tailWord_6727569 prefixEnd_6727569 3454476533287694089047979 := by
  unfold tailWord_6727569
  simp only [CollatzResearch.WordTrace]
  refine ⟨245374599764173965155553761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163583066509449310103702507 245374599764173965155553761)
  ·
    refine ⟨184030949823130473866665321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245374599764173965155553761 184030949823130473866665321)
    ·
      refine ⟨138023212367347855399998991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184030949823130473866665321 138023212367347855399998991)
      ·
        refine ⟨207034818551021783099998487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138023212367347855399998991 207034818551021783099998487)
        ·
          refine ⟨310552227826532674649997731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207034818551021783099998487 310552227826532674649997731)
          ·
            refine ⟨465828341739799011974996597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310552227826532674649997731 465828341739799011974996597)
            ·
              refine ⟨43671407038106157372655931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 465828341739799011974996597 43671407038106157372655931)
              ·
                refine ⟨65507110557159236058983897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43671407038106157372655931 65507110557159236058983897)
                ·
                  refine ⟨49130332917869427044237923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65507110557159236058983897 49130332917869427044237923)
                  ·
                    refine ⟨73695499376804140566356885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49130332917869427044237923 73695499376804140566356885)
                    ·
                      refine ⟨3454476533287694089047979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73695499376804140566356885 3454476533287694089047979)
                      ·
                        rfl

theorem cell23_6727569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_6727569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727569 prefixEnd_6727569 := by exact prefixLift 6727569
  have htrace : WordTrace (prefixWord ++ tailWord_6727569) baseStart_6727569 baseEnd_6727569 := by
    simpa [prefixWord, tailWord_6727569, baseEnd_6727569] using wordTrace_append hprefix tailTrace_6727569
  have hstable : (prefixWord ++ tailWord_6727569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727569).length < 2 ^ (prefixWord ++ tailWord_6727569).sum := by decide
  have hdescent : baseEnd_6727569 < baseStart_6727569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727599 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 6]
def baseStart_6727599 : Nat := 118140960795 + 6727599 * 2 ^ 59
def prefixEnd_6727599 : Nat := 4983230072969 + 3 ^ 40 * 6727599 * 2
def baseEnd_6727599 : Nat := 3454491937707328971672841

theorem tailTrace_6727599 : CollatzResearch.WordTrace tailWord_6727599 prefixEnd_6727599 3454491937707328971672841 := by
  unfold tailWord_6727599
  simp only [CollatzResearch.WordTrace]
  refine ⟨245375693954065280279145851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163583795969376853519430567 245375693954065280279145851)
  ·
    refine ⟨368063540931097920418718777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245375693954065280279145851 368063540931097920418718777)
    ·
      refine ⟨276047655698323440314039083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368063540931097920418718777 276047655698323440314039083)
      ·
        refine ⟨414071483547485160471058625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276047655698323440314039083 414071483547485160471058625)
        ·
          refine ⟨310553612660613870353293969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414071483547485160471058625 310553612660613870353293969)
          ·
            refine ⟨232915209495460402764970477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310553612660613870353293969 232915209495460402764970477)
            ·
              refine ⟨87343203560797651036863929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232915209495460402764970477 87343203560797651036863929)
              ·
                refine ⟨65507402670598238277647947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87343203560797651036863929 65507402670598238277647947)
                ·
                  refine ⟨98261104005897357416471921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65507402670598238277647947 98261104005897357416471921)
                  ·
                    refine ⟨73695828004423018062353941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98261104005897357416471921 73695828004423018062353941)
                    ·
                      refine ⟨3454491937707328971672841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73695828004423018062353941 3454491937707328971672841)
                      ·
                        rfl

theorem cell23_6727599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_6727599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727599 prefixEnd_6727599 := by exact prefixLift 6727599
  have htrace : WordTrace (prefixWord ++ tailWord_6727599) baseStart_6727599 baseEnd_6727599 := by
    simpa [prefixWord, tailWord_6727599, baseEnd_6727599] using wordTrace_append hprefix tailTrace_6727599
  have hstable : (prefixWord ++ tailWord_6727599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727599).length < 2 ^ (prefixWord ++ tailWord_6727599).sum := by decide
  have hdescent : baseEnd_6727599 < baseStart_6727599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727619 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 5]
def baseStart_6727619 : Nat := 118140960795 + 6727619 * 2 ^ 59
def prefixEnd_6727619 : Nat := 4983230072969 + 3 ^ 40 * 6727619 * 2
def baseEnd_6727619 : Nat := 3454502207320418893422749

theorem tailTrace_6727619 : CollatzResearch.WordTrace tailWord_6727619 prefixEnd_6727619 3454502207320418893422749 := by
  unfold tailWord_6727619
  simp only [CollatzResearch.WordTrace]
  refine ⟨245376423413992823694873911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163584282275995215796582607 245376423413992823694873911)
  ·
    refine ⟨368064635120989235542310867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245376423413992823694873911 368064635120989235542310867)
    ·
      refine ⟨552096952681483853313466301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368064635120989235542310867 552096952681483853313466301)
      ·
        refine ⟨207036357255556444992549863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 552096952681483853313466301 207036357255556444992549863)
        ·
          refine ⟨310554535883334667488824795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207036357255556444992549863 310554535883334667488824795)
          ·
            refine ⟨465831803825002001233237193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310554535883334667488824795 465831803825002001233237193)
            ·
              refine ⟨349373852868751500924927895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465831803825002001233237193 349373852868751500924927895)
              ·
                refine ⟨524060779303127251387391843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349373852868751500924927895 524060779303127251387391843)
                ·
                  refine ⟨786091168954690877081087765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 524060779303127251387391843 786091168954690877081087765)
                  ·
                    refine ⟨36848023544751134863175989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 786091168954690877081087765 36848023544751134863175989)
                    ·
                      refine ⟨3454502207320418893422749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36848023544751134863175989 3454502207320418893422749)
                      ·
                        rfl

theorem cell23_6727619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_6727619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727619 prefixEnd_6727619 := by exact prefixLift 6727619
  have htrace : WordTrace (prefixWord ++ tailWord_6727619) baseStart_6727619 baseEnd_6727619 := by
    simpa [prefixWord, tailWord_6727619, baseEnd_6727619] using wordTrace_append hprefix tailTrace_6727619
  have hstable : (prefixWord ++ tailWord_6727619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727619).length < 2 ^ (prefixWord ++ tailWord_6727619).sum := by decide
  have hdescent : baseEnd_6727619 < baseStart_6727619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727634 : List Nat := [3, 2, 2, 3, 2, 1, 3, 2, 1, 4]
def baseStart_6727634 : Nat := 118140960795 + 6727634 * 2 ^ 59
def prefixEnd_6727634 : Nat := 4983230072969 + 3 ^ 40 * 6727634 * 2
def baseEnd_6727634 : Nat := 1151503303176745444911727

theorem tailTrace_6727634 : CollatzResearch.WordTrace tailWord_6727634 prefixEnd_6727634 1151503303176745444911727 := by
  unfold tailWord_6727634
  simp only [CollatzResearch.WordTrace]
  refine ⟨61344242627234620314167489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163584647005958987504446637 61344242627234620314167489)
  ·
    refine ⟨46008181970425965235625617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61344242627234620314167489 46008181970425965235625617)
    ·
      refine ⟨34506136477819473926719213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46008181970425965235625617 34506136477819473926719213)
      ·
        refine ⟨12939801179182302722519705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34506136477819473926719213 12939801179182302722519705)
        ·
          refine ⟨9704850884386727041889779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12939801179182302722519705 9704850884386727041889779)
          ·
            refine ⟨14557276326580090562834669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9704850884386727041889779 14557276326580090562834669)
            ·
              refine ⟨5458978622467533961063001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14557276326580090562834669 5458978622467533961063001)
              ·
                refine ⟨4094233966850650470797251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5458978622467533961063001 4094233966850650470797251)
                ·
                  refine ⟨6141350950275975706195877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4094233966850650470797251 6141350950275975706195877)
                  ·
                    refine ⟨1151503303176745444911727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6141350950275975706195877 1151503303176745444911727)
                    ·
                      rfl

theorem cell23_6727634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_6727634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727634 prefixEnd_6727634 := by exact prefixLift 6727634
  have htrace : WordTrace (prefixWord ++ tailWord_6727634) baseStart_6727634 baseEnd_6727634 := by
    simpa [prefixWord, tailWord_6727634, baseEnd_6727634] using wordTrace_append hprefix tailTrace_6727634
  have hstable : (prefixWord ++ tailWord_6727634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727634).length < 2 ^ (prefixWord ++ tailWord_6727634).sum := by decide
  have hdescent : baseEnd_6727634 < baseStart_6727634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727656 : List Nat := [2, 1, 4, 1, 1, 1, 1, 5, 1, 6]
def baseStart_6727656 : Nat := 118140960795 + 6727656 * 2 ^ 59
def prefixEnd_6727656 : Nat := 4983230072969 + 3 ^ 40 * 6727656 * 2
def baseEnd_6727656 : Nat := 1151507068701545082886693

theorem tailTrace_6727656 : CollatzResearch.WordTrace tailWord_6727656 prefixEnd_6727656 1151507068701545082886693 := by
  unfold tailWord_6727656
  simp only [CollatzResearch.WordTrace]
  refine ⟨122688886457429389506985411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163585181943239186009313881 122688886457429389506985411)
  ·
    refine ⟨184033329686144084260478117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122688886457429389506985411 184033329686144084260478117)
    ·
      refine ⟨34506249316152015798839647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184033329686144084260478117 34506249316152015798839647)
      ·
        refine ⟨51759373974228023698259471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34506249316152015798839647 51759373974228023698259471)
        ·
          refine ⟨77639060961342035547389207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51759373974228023698259471 77639060961342035547389207)
          ·
            refine ⟨116458591442013053321083811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77639060961342035547389207 116458591442013053321083811)
            ·
              refine ⟨174687887163019579981625717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116458591442013053321083811 174687887163019579981625717)
              ·
                refine ⟨16376989421533085623277411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 174687887163019579981625717 16376989421533085623277411)
                ·
                  refine ⟨24565484132299628434916117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16376989421533085623277411 24565484132299628434916117)
                  ·
                    refine ⟨1151507068701545082886693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24565484132299628434916117 1151507068701545082886693)
                    ·
                      rfl

theorem cell23_6727656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_6727656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727656 prefixEnd_6727656 := by exact prefixLift 6727656
  have htrace : WordTrace (prefixWord ++ tailWord_6727656) baseStart_6727656 baseEnd_6727656 := by
    simpa [prefixWord, tailWord_6727656, baseEnd_6727656] using wordTrace_append hprefix tailTrace_6727656
  have hstable : (prefixWord ++ tailWord_6727656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727656).length < 2 ^ (prefixWord ++ tailWord_6727656).sum := by decide
  have hdescent : baseEnd_6727656 < baseStart_6727656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727683 : List Nat := [1, 1, 1, 3, 2, 1, 1, 7, 1, 2, 3]
def baseStart_6727683 : Nat := 118140960795 + 6727683 * 2 ^ 59
def prefixEnd_6727683 : Nat := 4983230072969 + 3 ^ 40 * 6727683 * 2
def baseEnd_6727683 : Nat := 3454535070082306643022455

theorem tailTrace_6727683 : CollatzResearch.WordTrace tailWord_6727683 prefixEnd_6727683 3454535070082306643022455 := by
  unfold tailWord_6727683
  simp only [CollatzResearch.WordTrace]
  refine ⟨245378757685760962625203703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163585838457173975083469135 245378757685760962625203703)
  ·
    refine ⟨368068136528641443937805555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245378757685760962625203703 368068136528641443937805555)
    ·
      refine ⟨552102204792962165906708333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368068136528641443937805555 552102204792962165906708333)
      ·
        refine ⟨207038326797360812215015625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 552102204792962165906708333 207038326797360812215015625)
        ·
          refine ⟨155278745098020609161261719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207038326797360812215015625 155278745098020609161261719)
          ·
            refine ⟨232918117647030913741892579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155278745098020609161261719 232918117647030913741892579)
            ·
              refine ⟨349377176470546370612838869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232918117647030913741892579 349377176470546370612838869)
              ·
                refine ⟨8188527573528430561238411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 349377176470546370612838869 8188527573528430561238411)
                ·
                  refine ⟨12282791360292645841857617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8188527573528430561238411 12282791360292645841857617)
                  ·
                    refine ⟨9212093520219484381393213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12282791360292645841857617 9212093520219484381393213)
                    ·
                      refine ⟨3454535070082306643022455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9212093520219484381393213 3454535070082306643022455)
                      ·
                        rfl

theorem cell23_6727683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 2, 3].length) (baseStart_6727683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727683 prefixEnd_6727683 := by exact prefixLift 6727683
  have htrace : WordTrace (prefixWord ++ tailWord_6727683) baseStart_6727683 baseEnd_6727683 := by
    simpa [prefixWord, tailWord_6727683, baseEnd_6727683] using wordTrace_append hprefix tailTrace_6727683
  have hstable : (prefixWord ++ tailWord_6727683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727683).length < 2 ^ (prefixWord ++ tailWord_6727683).sum := by decide
  have hdescent : baseEnd_6727683 < baseStart_6727683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727840 : List Nat := [2, 1, 1, 4, 2, 3, 2, 1, 2, 5]
def baseStart_6727840 : Nat := 118140960795 + 6727840 * 2 ^ 59
def prefixEnd_6727840 : Nat := 4983230072969 + 3 ^ 40 * 6727840 * 2
def baseEnd_6727840 : Nat := 1151538562181687509586411

theorem tailTrace_6727840 : CollatzResearch.WordTrace tailWord_6727840 prefixEnd_6727840 1151538562181687509586411 := by
  unfold tailWord_6727840
  simp only [CollatzResearch.WordTrace]
  refine ⟨122692241973096089219334487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163589655964128118959112649 122692241973096089219334487)
  ·
    refine ⟨184038362959644133829001731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122692241973096089219334487 184038362959644133829001731)
    ·
      refine ⟨276057544439466200743502597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184038362959644133829001731 276057544439466200743502597)
      ·
        refine ⟨51760789582399912639406737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 276057544439466200743502597 51760789582399912639406737)
        ·
          refine ⟨38820592186799934479555053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51760789582399912639406737 38820592186799934479555053)
          ·
            refine ⟨14557722070049975429833145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38820592186799934479555053 14557722070049975429833145)
            ·
              refine ⟨10918291552537481572374859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14557722070049975429833145 10918291552537481572374859)
              ·
                refine ⟨16377437328806222358562289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10918291552537481572374859 16377437328806222358562289)
                ·
                  refine ⟨12283077996604666768921717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16377437328806222358562289 12283077996604666768921717)
                  ·
                    refine ⟨1151538562181687509586411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12283077996604666768921717 1151538562181687509586411)
                    ·
                      rfl

theorem cell23_6727840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 2, 5].length) (baseStart_6727840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727840 prefixEnd_6727840 := by exact prefixLift 6727840
  have htrace : WordTrace (prefixWord ++ tailWord_6727840) baseStart_6727840 baseEnd_6727840 := by
    simpa [prefixWord, tailWord_6727840, baseEnd_6727840] using wordTrace_append hprefix tailTrace_6727840
  have hstable : (prefixWord ++ tailWord_6727840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727840).length < 2 ^ (prefixWord ++ tailWord_6727840).sum := by decide
  have hdescent : baseEnd_6727840 < baseStart_6727840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727861 : List Nat := [1, 3, 3, 4, 1, 2, 2, 2, 5]
def baseStart_6727861 : Nat := 118140960795 + 6727861 * 2 ^ 59
def prefixEnd_6727861 : Nat := 4983230072969 + 3 ^ 40 * 6727861 * 2
def baseEnd_6727861 : Nat := 383847385515422994066293

theorem tailTrace_6727861 : CollatzResearch.WordTrace tailWord_6727861 prefixEnd_6727861 383847385515422994066293 := by
  unfold tailWord_6727861
  simp only [CollatzResearch.WordTrace]
  refine ⟨245385249879116099025183437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163590166586077399350122291 245385249879116099025183437)
  ·
    refine ⟨92019468704668537134443789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245385249879116099025183437 92019468704668537134443789)
    ·
      refine ⟨34507300764250701425416421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92019468704668537134443789 34507300764250701425416421)
      ·
        refine ⟨6470118893297006517265579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34507300764250701425416421 6470118893297006517265579)
        ·
          refine ⟨9705178339945509775898369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6470118893297006517265579 9705178339945509775898369)
          ·
            refine ⟨7278883754959132331923777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9705178339945509775898369 7278883754959132331923777)
            ·
              refine ⟨5459162816219349248942833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7278883754959132331923777 5459162816219349248942833)
              ·
                refine ⟨4094372112164511936707125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5459162816219349248942833 4094372112164511936707125)
                ·
                  refine ⟨383847385515422994066293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4094372112164511936707125 383847385515422994066293)
                  ·
                    rfl

theorem cell23_6727861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 5].length) (baseStart_6727861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727861 prefixEnd_6727861 := by exact prefixLift 6727861
  have htrace : WordTrace (prefixWord ++ tailWord_6727861) baseStart_6727861 baseEnd_6727861 := by
    simpa [prefixWord, tailWord_6727861, baseEnd_6727861] using wordTrace_append hprefix tailTrace_6727861
  have hstable : (prefixWord ++ tailWord_6727861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727861).length < 2 ^ (prefixWord ++ tailWord_6727861).sum := by decide
  have hdescent : baseEnd_6727861 < baseStart_6727861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727883 : List Nat := [1, 1, 1, 1, 3, 2, 3, 5, 6]
def baseStart_6727883 : Nat := 118140960795 + 6727883 * 2 ^ 59
def prefixEnd_6727883 : Nat := 4983230072969 + 3 ^ 40 * 6727883 * 2
def baseEnd_6727883 : Nat := 383848640690356206724615

theorem tailTrace_6727883 : CollatzResearch.WordTrace tailWord_6727883 prefixEnd_6727883 383848640690356206724615 := by
  unfold tailWord_6727883
  simp only [CollatzResearch.WordTrace]
  refine ⟨245386052285036396782484303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163590701523357597854989535 245386052285036396782484303)
  ·
    refine ⟨368079078427554595173726455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245386052285036396782484303 368079078427554595173726455)
    ·
      refine ⟨552118617641331892760589683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368079078427554595173726455 552118617641331892760589683)
      ·
        refine ⟨828177926461997839140884525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552118617641331892760589683 828177926461997839140884525)
        ·
          refine ⟨310566722423249189677831697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 828177926461997839140884525 310566722423249189677831697)
          ·
            refine ⟨232925041817436892258373773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310566722423249189677831697 232925041817436892258373773)
            ·
              refine ⟨87346890681538834596890165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232925041817436892258373773 87346890681538834596890165)
              ·
                refine ⟨8188771001394265743458453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87346890681538834596890165 8188771001394265743458453)
                ·
                  refine ⟨383848640690356206724615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8188771001394265743458453 383848640690356206724615)
                  ·
                    rfl

theorem cell23_6727883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 6].length) (baseStart_6727883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727883 prefixEnd_6727883 := by exact prefixLift 6727883
  have htrace : WordTrace (prefixWord ++ tailWord_6727883) baseStart_6727883 baseEnd_6727883 := by
    simpa [prefixWord, tailWord_6727883, baseEnd_6727883] using wordTrace_append hprefix tailTrace_6727883
  have hstable : (prefixWord ++ tailWord_6727883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727883).length < 2 ^ (prefixWord ++ tailWord_6727883).sum := by decide
  have hdescent : baseEnd_6727883 < baseStart_6727883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727894 : List Nat := [5, 2, 1, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_6727894 : Nat := 118140960795 + 6727894 * 2 ^ 59
def prefixEnd_6727894 : Nat := 4983230072969 + 3 ^ 40 * 6727894 * 2
def baseEnd_6727894 : Nat := 3454643414500405317483985

theorem tailTrace_6727894 : CollatzResearch.WordTrace tailWord_6727894 prefixEnd_6727894 3454643414500405317483985 := by
  unfold tailWord_6727894
  simp only [CollatzResearch.WordTrace]
  refine ⟨15336653342999784103820921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163590968991997697107423157 15336653342999784103820921)
  ·
    refine ⟨11502490007249838077865691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15336653342999784103820921 11502490007249838077865691)
    ·
      refine ⟨17253735010874757116798537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11502490007249838077865691 17253735010874757116798537)
      ·
        refine ⟨12940301258156067837598903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17253735010874757116798537 12940301258156067837598903)
        ·
          refine ⟨19410451887234101756398355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12940301258156067837598903 19410451887234101756398355)
          ·
            refine ⟨29115677830851152634597533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19410451887234101756398355 29115677830851152634597533)
            ·
              refine ⟨10918379186569182237974075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29115677830851152634597533 10918379186569182237974075)
              ·
                refine ⟨16377568779853773356961113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10918379186569182237974075 16377568779853773356961113)
                ·
                  refine ⟨12283176584890330017720835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16377568779853773356961113 12283176584890330017720835)
                  ·
                    refine ⟨18424764877335495026581253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12283176584890330017720835 18424764877335495026581253)
                    ·
                      refine ⟨3454643414500405317483985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18424764877335495026581253 3454643414500405317483985)
                      ·
                        rfl

theorem cell23_6727894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_6727894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727894 prefixEnd_6727894 := by exact prefixLift 6727894
  have htrace : WordTrace (prefixWord ++ tailWord_6727894) baseStart_6727894 baseEnd_6727894 := by
    simpa [prefixWord, tailWord_6727894, baseEnd_6727894] using wordTrace_append hprefix tailTrace_6727894
  have hstable : (prefixWord ++ tailWord_6727894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727894).length < 2 ^ (prefixWord ++ tailWord_6727894).sum := by decide
  have hdescent : baseEnd_6727894 < baseStart_6727894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727960 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 6, 4]
def baseStart_6727960 : Nat := 118140960795 + 6727960 * 2 ^ 59
def prefixEnd_6727960 : Nat := 4983230072969 + 3 ^ 40 * 6727960 * 2
def baseEnd_6727960 : Nat := 1151559101407867353086227

theorem tailTrace_6727960 : CollatzResearch.WordTrace tailWord_6727960 prefixEnd_6727960 1151559101407867353086227 := by
  unfold tailWord_6727960
  simp only [CollatzResearch.WordTrace]
  refine ⟨122694430352878719466518667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163592573803838292622024889 122694430352878719466518667)
  ·
    refine ⟨184041645529318079199778001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122694430352878719466518667 184041645529318079199778001)
    ·
      refine ⟨138031234146988559399833501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184041645529318079199778001 138031234146988559399833501)
      ·
        refine ⟨51761712805120709774937563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138031234146988559399833501 51761712805120709774937563)
        ·
          refine ⟨77642569207681064662406345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51761712805120709774937563 77642569207681064662406345)
          ·
            refine ⟨58231926905760798496804759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77642569207681064662406345 58231926905760798496804759)
            ·
              refine ⟨87347890358641197745207139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58231926905760798496804759 87347890358641197745207139)
              ·
                refine ⟨131021835537961796617810709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87347890358641197745207139 131021835537961796617810709)
                ·
                  refine ⟨6141648540841959216459877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 131021835537961796617810709 6141648540841959216459877)
                  ·
                    refine ⟨1151559101407867353086227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6141648540841959216459877 1151559101407867353086227)
                    ·
                      rfl

theorem cell23_6727960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 6, 4].length) (baseStart_6727960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727960 prefixEnd_6727960 := by exact prefixLift 6727960
  have htrace : WordTrace (prefixWord ++ tailWord_6727960) baseStart_6727960 baseEnd_6727960 := by
    simpa [prefixWord, tailWord_6727960, baseEnd_6727960] using wordTrace_append hprefix tailTrace_6727960
  have hstable : (prefixWord ++ tailWord_6727960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727960).length < 2 ^ (prefixWord ++ tailWord_6727960).sum := by decide
  have hdescent : baseEnd_6727960 < baseStart_6727960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727967 : List Nat := [1, 1, 2, 4, 3, 1, 2, 3, 1, 1, 4]
def baseStart_6727967 : Nat := 118140960795 + 6727967 * 2 ^ 59
def prefixEnd_6727967 : Nat := 4983230072969 + 3 ^ 40 * 6727967 * 2
def baseEnd_6727967 : Nat := 3454680898588183531871149

theorem tailTrace_6727967 : CollatzResearch.WordTrace tailWord_6727967 prefixEnd_6727967 3454680898588183531871149 := by
  unfold tailWord_6727967
  simp only [CollatzResearch.WordTrace]
  refine ⟨245389116016732079128542155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163592744011154719419028103 245389116016732079128542155)
  ·
    refine ⟨368083674025098118692813233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245389116016732079128542155 368083674025098118692813233)
    ·
      refine ⟨276062755518823589019609925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368083674025098118692813233 276062755518823589019609925)
      ·
        refine ⟨51761766659779422941176861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 276062755518823589019609925 51761766659779422941176861)
        ·
          refine ⟨19410662497417283602941323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51761766659779422941176861 19410662497417283602941323)
          ·
            refine ⟨29115993746125925404411985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19410662497417283602941323 29115993746125925404411985)
            ·
              refine ⟨21836995309594444053308989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29115993746125925404411985 21836995309594444053308989)
              ·
                refine ⟨8188873241097916519990871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21836995309594444053308989 8188873241097916519990871)
                ·
                  refine ⟨12283309861646874779986307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8188873241097916519990871 12283309861646874779986307)
                  ·
                    refine ⟨18424964792470312169979461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12283309861646874779986307 18424964792470312169979461)
                    ·
                      refine ⟨3454680898588183531871149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18424964792470312169979461 3454680898588183531871149)
                      ·
                        rfl

theorem cell23_6727967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_6727967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727967 prefixEnd_6727967 := by exact prefixLift 6727967
  have htrace : WordTrace (prefixWord ++ tailWord_6727967) baseStart_6727967 baseEnd_6727967 := by
    simpa [prefixWord, tailWord_6727967, baseEnd_6727967] using wordTrace_append hprefix tailTrace_6727967
  have hstable : (prefixWord ++ tailWord_6727967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727967).length < 2 ^ (prefixWord ++ tailWord_6727967).sum := by decide
  have hdescent : baseEnd_6727967 < baseStart_6727967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727978 : List Nat := [3, 1, 4, 2, 3, 1, 1, 1, 3, 1, 3]
def baseStart_6727978 : Nat := 118140960795 + 6727978 * 2 ^ 59
def prefixEnd_6727978 : Nat := 4983230072969 + 3 ^ 40 * 6727978 * 2
def baseEnd_6727978 : Nat := 3454686546875382988833599

theorem tailTrace_6727978 : CollatzResearch.WordTrace tailWord_6727978 prefixEnd_6727978 3454686546875382988833599 := by
  unfold tailWord_6727978
  simp only [CollatzResearch.WordTrace]
  refine ⟨61347379304923057001798147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163593011479794818671461725 61347379304923057001798147)
  ·
    refine ⟨92021068957384585502697221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61347379304923057001798147 92021068957384585502697221)
    ·
      refine ⟨17253950429509609781755729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92021068957384585502697221 17253950429509609781755729)
      ·
        refine ⟨12940462822132207336316797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17253950429509609781755729 12940462822132207336316797)
        ·
          refine ⟨4852673558299577751118799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12940462822132207336316797 4852673558299577751118799)
          ·
            refine ⟨7279010337449366626678199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4852673558299577751118799 7279010337449366626678199)
            ·
              refine ⟨10918515506174049940017299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7279010337449366626678199 10918515506174049940017299)
              ·
                refine ⟨16377773259261074910025949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10918515506174049940017299 16377773259261074910025949)
                ·
                  refine ⟨6141664972222903091259731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16377773259261074910025949 6141664972222903091259731)
                  ·
                    refine ⟨9212497458334354636889597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6141664972222903091259731 9212497458334354636889597)
                    ·
                      refine ⟨3454686546875382988833599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9212497458334354636889597 3454686546875382988833599)
                      ·
                        rfl

theorem cell23_6727978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_6727978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727978 prefixEnd_6727978 := by exact prefixLift 6727978
  have htrace : WordTrace (prefixWord ++ tailWord_6727978) baseStart_6727978 baseEnd_6727978 := by
    simpa [prefixWord, tailWord_6727978, baseEnd_6727978] using wordTrace_append hprefix tailTrace_6727978
  have hstable : (prefixWord ++ tailWord_6727978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727978).length < 2 ^ (prefixWord ++ tailWord_6727978).sum := by decide
  have hdescent : baseEnd_6727978 < baseStart_6727978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6727994 : List Nat := [3, 1, 1, 1, 4, 2, 4, 1, 2, 4]
def baseStart_6727994 : Nat := 118140960795 + 6727994 * 2 ^ 59
def prefixEnd_6727994 : Nat := 4983230072969 + 3 ^ 40 * 6727994 * 2
def baseEnd_6727994 : Nat := 1151564920855284975411175

theorem tailTrace_6727994 : CollatzResearch.WordTrace tailWord_6727994 prefixEnd_6727994 1151564920855284975411175 := by
  unfold tailWord_6727994
  simp only [CollatzResearch.WordTrace]
  refine ⟨61347525196908565684943759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163593400525089508493183357 61347525196908565684943759)
  ·
    refine ⟨92021287795362848527415639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61347525196908565684943759 92021287795362848527415639)
    ·
      refine ⟨138031931693044272791123459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92021287795362848527415639 138031931693044272791123459)
      ·
        refine ⟨207047897539566409186685189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138031931693044272791123459 207047897539566409186685189)
        ·
          refine ⟨38821480788668701722503473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207047897539566409186685189 38821480788668701722503473)
          ·
            refine ⟨29116110591501526291877605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38821480788668701722503473 29116110591501526291877605)
            ·
              refine ⟨5459270735906536179727051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29116110591501526291877605 5459270735906536179727051)
              ·
                refine ⟨8188906103859804269590577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5459270735906536179727051 8188906103859804269590577)
                ·
                  refine ⟨6141679577894853202192933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8188906103859804269590577 6141679577894853202192933)
                  ·
                    refine ⟨1151564920855284975411175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6141679577894853202192933 1151564920855284975411175)
                    ·
                      rfl

theorem cell23_6727994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 2, 4].length) (baseStart_6727994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6727994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6727994 prefixEnd_6727994 := by exact prefixLift 6727994
  have htrace : WordTrace (prefixWord ++ tailWord_6727994) baseStart_6727994 baseEnd_6727994 := by
    simpa [prefixWord, tailWord_6727994, baseEnd_6727994] using wordTrace_append hprefix tailTrace_6727994
  have hstable : (prefixWord ++ tailWord_6727994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6727994).length < 2 ^ (prefixWord ++ tailWord_6727994).sum := by decide
  have hdescent : baseEnd_6727994 < baseStart_6727994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6727994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728001 : List Nat := [1, 2, 5, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_6728001 : Nat := 118140960795 + 6728001 * 2 ^ 59
def prefixEnd_6728001 : Nat := 4983230072969 + 3 ^ 40 * 6728001 * 2
def baseEnd_6728001 : Nat := 3454698356930436398845993

theorem tailTrace_6728001 : CollatzResearch.WordTrace tailWord_6728001 prefixEnd_6728001 3454698356930436398845993 := by
  unfold tailWord_6728001
  simp only [CollatzResearch.WordTrace]
  refine ⟨245390356098608902935279857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163593570732405935290186571 245390356098608902935279857)
  ·
    refine ⟨184042767073956677201459893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245390356098608902935279857 184042767073956677201459893)
    ·
      refine ⟨17254009413183438487636865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184042767073956677201459893 17254009413183438487636865)
      ·
        refine ⟨12940507059887578865727649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17254009413183438487636865 12940507059887578865727649)
        ·
          refine ⟨9705380294915684149295737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12940507059887578865727649 9705380294915684149295737)
          ·
            refine ⟨7279035221186763111971803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9705380294915684149295737 7279035221186763111971803)
            ·
              refine ⟨10918552831780144667957705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7279035221186763111971803 10918552831780144667957705)
              ·
                refine ⟨8188914623835108500968279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10918552831780144667957705 8188914623835108500968279)
                ·
                  refine ⟨12283371935752662751452419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8188914623835108500968279 12283371935752662751452419)
                  ·
                    refine ⟨18425057903628994127178629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12283371935752662751452419 18425057903628994127178629)
                    ·
                      refine ⟨3454698356930436398845993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18425057903628994127178629 3454698356930436398845993)
                      ·
                        rfl

theorem cell23_6728001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_6728001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728001 prefixEnd_6728001 := by exact prefixLift 6728001
  have htrace : WordTrace (prefixWord ++ tailWord_6728001) baseStart_6728001 baseEnd_6728001 := by
    simpa [prefixWord, tailWord_6728001, baseEnd_6728001] using wordTrace_append hprefix tailTrace_6728001
  have hstable : (prefixWord ++ tailWord_6728001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728001).length < 2 ^ (prefixWord ++ tailWord_6728001).sum := by decide
  have hdescent : baseEnd_6728001 < baseStart_6728001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728017 : List Nat := [1, 2, 2, 1, 4, 3, 1, 2, 1, 3, 3]
def baseStart_6728017 : Nat := 118140960795 + 6728017 * 2 ^ 59
def prefixEnd_6728017 : Nat := 4983230072969 + 3 ^ 40 * 6728017 * 2
def baseEnd_6728017 : Nat := 3454706572620908336245919

theorem tailTrace_6728017 : CollatzResearch.WordTrace tailWord_6728017 prefixEnd_6728017 3454706572620908336245919 := by
  unfold tailWord_6728017
  simp only [CollatzResearch.WordTrace]
  refine ⟨245390939666550937667862305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163593959777700625111908203 245390939666550937667862305)
  ·
    refine ⟨184043204749913203250896729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245390939666550937667862305 184043204749913203250896729)
    ·
      refine ⟨138032403562434902438172547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184043204749913203250896729 138032403562434902438172547)
      ·
        refine ⟨207048605343652353657258821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138032403562434902438172547 207048605343652353657258821)
        ·
          refine ⟨38821613501934816310736029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207048605343652353657258821 38821613501934816310736029)
          ·
            refine ⟨14558105063225556116526011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38821613501934816310736029 14558105063225556116526011)
            ·
              refine ⟨21837157594838334174789017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14558105063225556116526011 21837157594838334174789017)
              ·
                refine ⟨16377868196128750631091763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21837157594838334174789017 16377868196128750631091763)
                ·
                  refine ⟨24566802294193125946637645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16377868196128750631091763 24566802294193125946637645)
                  ·
                    refine ⟨9212550860322422229989117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24566802294193125946637645 9212550860322422229989117)
                    ·
                      refine ⟨3454706572620908336245919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9212550860322422229989117 3454706572620908336245919)
                      ·
                        rfl

theorem cell23_6728017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 3, 3].length) (baseStart_6728017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728017 prefixEnd_6728017 := by exact prefixLift 6728017
  have htrace : WordTrace (prefixWord ++ tailWord_6728017) baseStart_6728017 baseEnd_6728017 := by
    simpa [prefixWord, tailWord_6728017, baseEnd_6728017] using wordTrace_append hprefix tailTrace_6728017
  have hstable : (prefixWord ++ tailWord_6728017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728017).length < 2 ^ (prefixWord ++ tailWord_6728017).sum := by decide
  have hdescent : baseEnd_6728017 < baseStart_6728017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728021 : List Nat := [1, 3, 2, 2, 4, 1, 3, 1, 1, 2, 3]
def baseStart_6728021 : Nat := 118140960795 + 6728021 * 2 ^ 59
def prefixEnd_6728021 : Nat := 4983230072969 + 3 ^ 40 * 6728021 * 2
def baseEnd_6728021 : Nat := 3454708626543526320595901

theorem tailTrace_6728021 : CollatzResearch.WordTrace tailWord_6728021 prefixEnd_6728021 3454708626543526320595901 := by
  unfold tailWord_6728021
  simp only [CollatzResearch.WordTrace]
  refine ⟨245391085558536446351007917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163594057039024297567338611 245391085558536446351007917)
  ·
    refine ⟨92021657084451167381627969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245391085558536446351007917 92021657084451167381627969)
    ·
      refine ⟨69016242813338375536220977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92021657084451167381627969 69016242813338375536220977)
      ·
        refine ⟨51762182110003781652165733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69016242813338375536220977 51762182110003781652165733)
        ·
          refine ⟨9705409145625709059781075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51762182110003781652165733 9705409145625709059781075)
          ·
            refine ⟨14558113718438563589671613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9705409145625709059781075 14558113718438563589671613)
            ·
              refine ⟨5459292644414461346126855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14558113718438563589671613 5459292644414461346126855)
              ·
                refine ⟨8188938966621692019190283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5459292644414461346126855 8188938966621692019190283)
                ·
                  refine ⟨12283408449932538028785425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8188938966621692019190283 12283408449932538028785425)
                  ·
                    refine ⟨9212556337449403521589069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12283408449932538028785425 9212556337449403521589069)
                    ·
                      refine ⟨3454708626543526320595901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9212556337449403521589069 3454708626543526320595901)
                      ·
                        rfl

theorem cell23_6728021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_6728021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728021 prefixEnd_6728021 := by exact prefixLift 6728021
  have htrace : WordTrace (prefixWord ++ tailWord_6728021) baseStart_6728021 baseEnd_6728021 := by
    simpa [prefixWord, tailWord_6728021, baseEnd_6728021] using wordTrace_append hprefix tailTrace_6728021
  have hstable : (prefixWord ++ tailWord_6728021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728021).length < 2 ^ (prefixWord ++ tailWord_6728021).sum := by decide
  have hdescent : baseEnd_6728021 < baseStart_6728021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728050 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 1, 8]
def baseStart_6728050 : Nat := 118140960795 + 6728050 * 2 ^ 59
def prefixEnd_6728050 : Nat := 4983230072969 + 3 ^ 40 * 6728050 * 2
def baseEnd_6728050 : Nat := 1151574505827502235711089

theorem tailTrace_6728050 : CollatzResearch.WordTrace tailWord_6728050 prefixEnd_6728050 1151574505827502235711089 := by
  unfold tailWord_6728050
  simp only [CollatzResearch.WordTrace]
  refine ⟨61348035818857846075953401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163594762183620922869209069 61348035818857846075953401)
  ·
    refine ⟨46011026864143384556965051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61348035818857846075953401 46011026864143384556965051)
    ·
      refine ⟨69016540296215076835447577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46011026864143384556965051 69016540296215076835447577)
      ·
        refine ⟨51762405222161307626585683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69016540296215076835447577 51762405222161307626585683)
        ·
          refine ⟨77643607833241961439878525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51762405222161307626585683 77643607833241961439878525)
          ·
            refine ⟨29116352937465735539954447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77643607833241961439878525 29116352937465735539954447)
            ·
              refine ⟨43674529406198603309931671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29116352937465735539954447 43674529406198603309931671)
              ·
                refine ⟨65511794109297904964897507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43674529406198603309931671 65511794109297904964897507)
                ·
                  refine ⟨98267691163946857447346261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65511794109297904964897507 98267691163946857447346261)
                  ·
                    refine ⟨1151574505827502235711089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98267691163946857447346261 1151574505827502235711089)
                    ·
                      rfl

theorem cell23_6728050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_6728050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728050 prefixEnd_6728050 := by exact prefixLift 6728050
  have htrace : WordTrace (prefixWord ++ tailWord_6728050) baseStart_6728050 baseEnd_6728050 := by
    simpa [prefixWord, tailWord_6728050, baseEnd_6728050] using wordTrace_append hprefix tailTrace_6728050
  have hstable : (prefixWord ++ tailWord_6728050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728050).length < 2 ^ (prefixWord ++ tailWord_6728050).sum := by decide
  have hdescent : baseEnd_6728050 < baseStart_6728050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728060 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 2, 1, 5]
def baseStart_6728060 : Nat := 118140960795 + 6728060 * 2 ^ 59
def prefixEnd_6728060 : Nat := 4983230072969 + 3 ^ 40 * 6728060 * 2
def baseEnd_6728060 : Nat := 3454728652289051668008221

theorem tailTrace_6728060 : CollatzResearch.WordTrace tailWord_6728060 prefixEnd_6728060 3454728652289051668008221 := by
  unfold tailWord_6728060
  simp only [CollatzResearch.WordTrace]
  refine ⟨122696254002697578005838817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163595005336930104007785089 122696254002697578005838817)
  ·
    refine ⟨92022190502023183504379113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122696254002697578005838817 92022190502023183504379113)
    ·
      refine ⟨69016642876517387628284335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92022190502023183504379113 69016642876517387628284335)
      ·
        refine ⟨103524964314776081442426503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69016642876517387628284335 103524964314776081442426503)
        ·
          refine ⟨155287446472164122163639755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103524964314776081442426503 155287446472164122163639755)
          ·
            refine ⟨232931169708246183245459633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155287446472164122163639755 232931169708246183245459633)
            ·
              refine ⟨174698377281184637434094725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232931169708246183245459633 174698377281184637434094725)
              ·
                refine ⟨32755945740222119518892761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174698377281184637434094725 32755945740222119518892761)
                ·
                  refine ⟨24566959305166589639169571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32755945740222119518892761 24566959305166589639169571)
                  ·
                    refine ⟨36850438957749884458754357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24566959305166589639169571 36850438957749884458754357)
                    ·
                      refine ⟨3454728652289051668008221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36850438957749884458754357 3454728652289051668008221)
                      ·
                        rfl

theorem cell23_6728060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_6728060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728060 prefixEnd_6728060 := by exact prefixLift 6728060
  have htrace : WordTrace (prefixWord ++ tailWord_6728060) baseStart_6728060 baseEnd_6728060 := by
    simpa [prefixWord, tailWord_6728060, baseEnd_6728060] using wordTrace_append hprefix tailTrace_6728060
  have hstable : (prefixWord ++ tailWord_6728060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728060).length < 2 ^ (prefixWord ++ tailWord_6728060).sum := by decide
  have hdescent : baseEnd_6728060 < baseStart_6728060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728078 : List Nat := [4, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2]
def baseStart_6728078 : Nat := 118140960795 + 6728078 * 2 ^ 59
def prefixEnd_6728078 : Nat := 4983230072969 + 3 ^ 40 * 6728078 * 2
def baseEnd_6728078 : Nat := 3454737894940832597583139

theorem tailTrace_6728078 : CollatzResearch.WordTrace tailWord_6728078 prefixEnd_6728078 3454737894940832597583139 := by
  unfold tailWord_6728078
  simp only [CollatzResearch.WordTrace]
  refine ⟨30674145564916243135729111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163595443012886630057221925 30674145564916243135729111)
  ·
    refine ⟨46011218347374364703593667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30674145564916243135729111 46011218347374364703593667)
    ·
      refine ⟨69016827521061547055390501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46011218347374364703593667 69016827521061547055390501)
      ·
        refine ⟨12940655160199040072885719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69016827521061547055390501 12940655160199040072885719)
        ·
          refine ⟨19410982740298560109328579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12940655160199040072885719 19410982740298560109328579)
          ·
            refine ⟨29116474110447840163992869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19410982740298560109328579 29116474110447840163992869)
            ·
              refine ⟨5459338895708970030748663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29116474110447840163992869 5459338895708970030748663)
              ·
                refine ⟨8189008343563455046122995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5459338895708970030748663 8189008343563455046122995)
                ·
                  refine ⟨12283512515345182569184493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8189008343563455046122995 12283512515345182569184493)
                  ·
                    refine ⟨4606317193254443463444185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12283512515345182569184493 4606317193254443463444185)
                    ·
                      refine ⟨3454737894940832597583139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4606317193254443463444185 3454737894940832597583139)
                      ·
                        rfl

theorem cell23_6728078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_6728078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728078 prefixEnd_6728078 := by exact prefixLift 6728078
  have htrace : WordTrace (prefixWord ++ tailWord_6728078) baseStart_6728078 baseEnd_6728078 := by
    simpa [prefixWord, tailWord_6728078, baseEnd_6728078] using wordTrace_append hprefix tailTrace_6728078
  have hstable : (prefixWord ++ tailWord_6728078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728078).length < 2 ^ (prefixWord ++ tailWord_6728078).sum := by decide
  have hdescent : baseEnd_6728078 < baseStart_6728078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728104 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_6728104 : Nat := 118140960795 + 6728104 * 2 ^ 59
def prefixEnd_6728104 : Nat := 4983230072969 + 3 ^ 40 * 6728104 * 2
def baseEnd_6728104 : Nat := 3454751245437849495858019

theorem tailTrace_6728104 : CollatzResearch.WordTrace tailWord_6728104 prefixEnd_6728104 3454751245437849495858019 := by
  unfold tailWord_6728104
  simp only [CollatzResearch.WordTrace]
  refine ⟨122697056408617875763139683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163596075211490501017519577 122697056408617875763139683)
  ·
    refine ⟨184045584612926813644709525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122697056408617875763139683 184045584612926813644709525)
    ·
      refine ⟨8627136778730944389595759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 184045584612926813644709525 8627136778730944389595759)
      ·
        refine ⟨12940705168096416584393639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8627136778730944389595759 12940705168096416584393639)
        ·
          refine ⟨19411057752144624876590459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12940705168096416584393639 19411057752144624876590459)
          ·
            refine ⟨29116586628216937314885689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19411057752144624876590459 29116586628216937314885689)
            ·
              refine ⟨21837439971162702986164267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29116586628216937314885689 21837439971162702986164267)
              ·
                refine ⟨32756159956744054479246401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21837439971162702986164267 32756159956744054479246401)
                ·
                  refine ⟨24567119967558040859434801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32756159956744054479246401 24567119967558040859434801)
                  ·
                    refine ⟨18425339975668530644576101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24567119967558040859434801 18425339975668530644576101)
                    ·
                      refine ⟨3454751245437849495858019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18425339975668530644576101 3454751245437849495858019)
                      ·
                        rfl

theorem cell23_6728104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_6728104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728104 prefixEnd_6728104 := by exact prefixLift 6728104
  have htrace : WordTrace (prefixWord ++ tailWord_6728104) baseStart_6728104 baseEnd_6728104 := by
    simpa [prefixWord, tailWord_6728104, baseEnd_6728104] using wordTrace_append hprefix tailTrace_6728104
  have hstable : (prefixWord ++ tailWord_6728104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728104).length < 2 ^ (prefixWord ++ tailWord_6728104).sum := by decide
  have hdescent : baseEnd_6728104 < baseStart_6728104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728120 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 3, 2, 5]
def baseStart_6728120 : Nat := 118140960795 + 6728120 * 2 ^ 59
def prefixEnd_6728120 : Nat := 4983230072969 + 3 ^ 40 * 6728120 * 2
def baseEnd_6728120 : Nat := 3454759461128321433257945

theorem tailTrace_6728120 : CollatzResearch.WordTrace tailWord_6728120 prefixEnd_6728120 3454759461128321433257945 := by
  unfold tailWord_6728120
  simp only [CollatzResearch.WordTrace]
  refine ⟨122697348192588893129430907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163596464256785190839241209 122697348192588893129430907)
  ·
    refine ⟨184046022288883339694146361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122697348192588893129430907 184046022288883339694146361)
    ·
      refine ⟨138034516716662504770609771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184046022288883339694146361 138034516716662504770609771)
      ·
        refine ⟨207051775074993757155914657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138034516716662504770609771 207051775074993757155914657)
        ·
          refine ⟨155288831306245317866935993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207051775074993757155914657 155288831306245317866935993)
          ·
            refine ⟨116466623479683988400201995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155288831306245317866935993 116466623479683988400201995)
            ·
              refine ⟨174699935219525982600302993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116466623479683988400201995 174699935219525982600302993)
              ·
                refine ⟨131024951414644486950227245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174699935219525982600302993 131024951414644486950227245)
                ·
                  refine ⟨49134356780491682606335217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131024951414644486950227245 49134356780491682606335217)
                  ·
                    refine ⟨36850767585368761954751413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49134356780491682606335217 36850767585368761954751413)
                    ·
                      refine ⟨3454759461128321433257945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36850767585368761954751413 3454759461128321433257945)
                      ·
                        rfl

theorem cell23_6728120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_6728120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728120 prefixEnd_6728120 := by exact prefixLift 6728120
  have htrace : WordTrace (prefixWord ++ tailWord_6728120) baseStart_6728120 baseEnd_6728120 := by
    simpa [prefixWord, tailWord_6728120, baseEnd_6728120] using wordTrace_append hprefix tailTrace_6728120
  have hstable : (prefixWord ++ tailWord_6728120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728120).length < 2 ^ (prefixWord ++ tailWord_6728120).sum := by decide
  have hdescent : baseEnd_6728120 < baseStart_6728120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728184 : List Nat := [2, 1, 2, 1, 1, 4, 4, 1, 2, 2, 3]
def baseStart_6728184 : Nat := 118140960795 + 6728184 * 2 ^ 59
def prefixEnd_6728184 : Nat := 4983230072969 + 3 ^ 40 * 6728184 * 2
def baseEnd_6728184 : Nat := 3454792323890209182857651

theorem tailTrace_6728184 : CollatzResearch.WordTrace tailWord_6728184 prefixEnd_6728184 3454792323890209182857651 := by
  unfold tailWord_6728184
  simp only [CollatzResearch.WordTrace]
  refine ⟨122698515328472962594595803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163598020437963950126127737 122698515328472962594595803)
  ·
    refine ⟨184047772992709443891893705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122698515328472962594595803 184047772992709443891893705)
    ·
      refine ⟨138035829744532082918920279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184047772992709443891893705 138035829744532082918920279)
      ·
        refine ⟨207053744616798124378380419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138035829744532082918920279 207053744616798124378380419)
        ·
          refine ⟨310580616925197186567570629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207053744616798124378380419 310580616925197186567570629)
          ·
            refine ⟨58233865673474472481419493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 310580616925197186567570629 58233865673474472481419493)
            ·
              refine ⟨10918849813776463590266155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58233865673474472481419493 10918849813776463590266155)
              ·
                refine ⟨16378274720664695385399233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10918849813776463590266155 16378274720664695385399233)
                ·
                  refine ⟨12283706040498521539049425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16378274720664695385399233 12283706040498521539049425)
                  ·
                    refine ⟨9212779530373891154287069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12283706040498521539049425 9212779530373891154287069)
                    ·
                      refine ⟨3454792323890209182857651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9212779530373891154287069 3454792323890209182857651)
                      ·
                        rfl

theorem cell23_6728184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 2, 2, 3].length) (baseStart_6728184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728184 prefixEnd_6728184 := by exact prefixLift 6728184
  have htrace : WordTrace (prefixWord ++ tailWord_6728184) baseStart_6728184 baseEnd_6728184 := by
    simpa [prefixWord, tailWord_6728184, baseEnd_6728184] using wordTrace_append hprefix tailTrace_6728184
  have hstable : (prefixWord ++ tailWord_6728184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728184).length < 2 ^ (prefixWord ++ tailWord_6728184).sum := by decide
  have hdescent : baseEnd_6728184 < baseStart_6728184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728204 : List Nat := [2, 2, 1, 2, 4, 2, 2, 2, 6]
def baseStart_6728204 : Nat := 118140960795 + 6728204 * 2 ^ 59
def prefixEnd_6728204 : Nat := 4983230072969 + 3 ^ 40 * 6728204 * 2
def baseEnd_6728204 : Nat := 383866954833699900511951

theorem tailTrace_6728204 : CollatzResearch.WordTrace tailWord_6728204 prefixEnd_6728204 383866954833699900511951 := by
  unfold tailWord_6728204
  simp only [CollatzResearch.WordTrace]
  refine ⟨122698880058436734302459833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163598506744582312403279777 122698880058436734302459833)
  ·
    refine ⟨92024160043827550726844875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122698880058436734302459833 92024160043827550726844875)
    ·
      refine ⟨138036240065741326090267313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92024160043827550726844875 138036240065741326090267313)
      ·
        refine ⟨103527180049305994567700485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138036240065741326090267313 103527180049305994567700485)
        ·
          refine ⟨19411346259244873981443841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103527180049305994567700485 19411346259244873981443841)
          ·
            refine ⟨14558509694433655486082881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19411346259244873981443841 14558509694433655486082881)
            ·
              refine ⟨10918882270825241614562161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14558509694433655486082881 10918882270825241614562161)
              ·
                refine ⟨8189161703118931210921621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10918882270825241614562161 8189161703118931210921621)
                ·
                  refine ⟨383866954833699900511951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8189161703118931210921621 383866954833699900511951)
                  ·
                    rfl

theorem cell23_6728204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 6].length) (baseStart_6728204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728204 prefixEnd_6728204 := by exact prefixLift 6728204
  have htrace : WordTrace (prefixWord ++ tailWord_6728204) baseStart_6728204 baseEnd_6728204 := by
    simpa [prefixWord, tailWord_6728204, baseEnd_6728204] using wordTrace_append hprefix tailTrace_6728204
  have hstable : (prefixWord ++ tailWord_6728204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728204).length < 2 ^ (prefixWord ++ tailWord_6728204).sum := by decide
  have hdescent : baseEnd_6728204 < baseStart_6728204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728234 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 3, 5]
def baseStart_6728234 : Nat := 118140960795 + 6728234 * 2 ^ 59
def prefixEnd_6728234 : Nat := 4983230072969 + 3 ^ 40 * 6728234 * 2
def baseEnd_6728234 : Nat := 1151605999307644662410807

theorem tailTrace_6728234 : CollatzResearch.WordTrace tailWord_6728234 prefixEnd_6728234 1151605999307644662410807 := by
  unfold tailWord_6728234
  simp only [CollatzResearch.WordTrace]
  refine ⟨61349713576691195932127939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163599236204509855819007837 61349713576691195932127939)
  ·
    refine ⟨92024570365036793898191909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61349713576691195932127939 92024570365036793898191909)
    ·
      refine ⟨17254606943444398855910983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92024570365036793898191909 17254606943444398855910983)
      ·
        refine ⟨25881910415166598283866475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17254606943444398855910983 25881910415166598283866475)
        ·
          refine ⟨38822865622749897425799713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25881910415166598283866475 38822865622749897425799713)
          ·
            refine ⟨29117149217062423069349785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38822865622749897425799713 29117149217062423069349785)
            ·
              refine ⟨21837861912796817302012339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29117149217062423069349785 21837861912796817302012339)
              ·
                refine ⟨32756792869195225953018509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21837861912796817302012339 32756792869195225953018509)
                ·
                  refine ⟨12283797325948209732381941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32756792869195225953018509 12283797325948209732381941)
                  ·
                    refine ⟨1151605999307644662410807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12283797325948209732381941 1151605999307644662410807)
                    ·
                      rfl

theorem cell23_6728234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_6728234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728234 prefixEnd_6728234 := by exact prefixLift 6728234
  have htrace : WordTrace (prefixWord ++ tailWord_6728234) baseStart_6728234 baseEnd_6728234 := by
    simpa [prefixWord, tailWord_6728234, baseEnd_6728234] using wordTrace_append hprefix tailTrace_6728234
  have hstable : (prefixWord ++ tailWord_6728234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728234).length < 2 ^ (prefixWord ++ tailWord_6728234).sum := by decide
  have hdescent : baseEnd_6728234 < baseStart_6728234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728241 : List Nat := [1, 2, 2, 3, 1, 1, 5, 1, 2, 3, 2]
def baseStart_6728241 : Nat := 118140960795 + 6728241 * 2 ^ 59
def prefixEnd_6728241 : Nat := 4983230072969 + 3 ^ 40 * 6728241 * 2
def baseEnd_6728241 : Nat := 3454821592287515459844889

theorem tailTrace_6728241 : CollatzResearch.WordTrace tailWord_6728241 prefixEnd_6728241 3454821592287515459844889 := by
  unfold tailWord_6728241
  simp only [CollatzResearch.WordTrace]
  refine ⟨245399109617739423924016577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163599406411826282616011051 245399109617739423924016577)
  ·
    refine ⟨184049332213304567943012433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245399109617739423924016577 184049332213304567943012433)
    ·
      refine ⟨138036999159978425957259325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184049332213304567943012433 138036999159978425957259325)
      ·
        refine ⟨51763874684991909733972247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138036999159978425957259325 51763874684991909733972247)
        ·
          refine ⟨77645812027487864600958371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51763874684991909733972247 77645812027487864600958371)
          ·
            refine ⟨116468718041231796901437557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77645812027487864600958371 116468718041231796901437557)
            ·
              refine ⟨10918942316365480959509771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116468718041231796901437557 10918942316365480959509771)
              ·
                refine ⟨16378413474548221439264657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10918942316365480959509771 16378413474548221439264657)
                ·
                  refine ⟨12283810105911166079448493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16378413474548221439264657 12283810105911166079448493)
                  ·
                    refine ⟨4606428789716687279793185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12283810105911166079448493 4606428789716687279793185)
                    ·
                      refine ⟨3454821592287515459844889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4606428789716687279793185 3454821592287515459844889)
                      ·
                        rfl

theorem cell23_6728241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_6728241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728241 prefixEnd_6728241 := by exact prefixLift 6728241
  have htrace : WordTrace (prefixWord ++ tailWord_6728241) baseStart_6728241 baseEnd_6728241 := by
    simpa [prefixWord, tailWord_6728241, baseEnd_6728241] using wordTrace_append hprefix tailTrace_6728241
  have hstable : (prefixWord ++ tailWord_6728241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728241).length < 2 ^ (prefixWord ++ tailWord_6728241).sum := by decide
  have hdescent : baseEnd_6728241 < baseStart_6728241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728247 : List Nat := [1, 1, 3, 1, 2, 3, 1, 4, 1, 6]
def baseStart_6728247 : Nat := 118140960795 + 6728247 * 2 ^ 59
def prefixEnd_6728247 : Nat := 4983230072969 + 3 ^ 40 * 6728247 * 2
def baseEnd_6728247 : Nat := 1151608224390480812123287

theorem tailTrace_6728247 : CollatzResearch.WordTrace tailWord_6728247 prefixEnd_6728247 1151608224390480812123287 := by
  unfold tailWord_6728247
  simp only [CollatzResearch.WordTrace]
  refine ⟨245399328455717686948734995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163599552303811791299156663 245399328455717686948734995)
  ·
    refine ⟨368098992683576530423102493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245399328455717686948734995 368098992683576530423102493)
    ·
      refine ⟨138037122256341198908663435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368098992683576530423102493 138037122256341198908663435)
      ·
        refine ⟨207055683384511798362995153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138037122256341198908663435 207055683384511798362995153)
        ·
          refine ⟨155291762538383848772246365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207055683384511798362995153 155291762538383848772246365)
          ·
            refine ⟨58234410951893943289592387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155291762538383848772246365 58234410951893943289592387)
            ·
              refine ⟨87351616427840914934388581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58234410951893943289592387 87351616427840914934388581)
              ·
                refine ⟨16378428080220171550197859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87351616427840914934388581 16378428080220171550197859)
                ·
                  refine ⟨24567642120330257325296789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16378428080220171550197859 24567642120330257325296789)
                  ·
                    refine ⟨1151608224390480812123287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24567642120330257325296789 1151608224390480812123287)
                    ·
                      rfl

theorem cell23_6728247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_6728247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728247 prefixEnd_6728247 := by exact prefixLift 6728247
  have htrace : WordTrace (prefixWord ++ tailWord_6728247) baseStart_6728247 baseEnd_6728247 := by
    simpa [prefixWord, tailWord_6728247, baseEnd_6728247] using wordTrace_append hprefix tailTrace_6728247
  have hstable : (prefixWord ++ tailWord_6728247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728247).length < 2 ^ (prefixWord ++ tailWord_6728247).sum := by decide
  have hdescent : baseEnd_6728247 < baseStart_6728247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728248 : List Nat := [2, 1, 2, 1, 4, 1, 4, 3, 1, 1, 3]
def baseStart_6728248 : Nat := 118140960795 + 6728248 * 2 ^ 59
def prefixEnd_6728248 : Nat := 4983230072969 + 3 ^ 40 * 6728248 * 2
def baseEnd_6728248 : Nat := 3454825186652096932457357

theorem tailTrace_6728248 : CollatzResearch.WordTrace tailWord_6728248 prefixEnd_6728248 3454825186652096932457357 := by
  unfold tailWord_6728248
  simp only [CollatzResearch.WordTrace]
  refine ⟨122699682464357032059760699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163599576619142709413014265 122699682464357032059760699)
  ·
    refine ⟨184049523696535548089641049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122699682464357032059760699 184049523696535548089641049)
    ·
      refine ⟨138037142772401661067230787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184049523696535548089641049 138037142772401661067230787)
      ·
        refine ⟨207055714158602491600846181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138037142772401661067230787 207055714158602491600846181)
        ·
          refine ⟨38822946404737967175158659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207055714158602491600846181 38822946404737967175158659)
          ·
            refine ⟨58234419607106950762737989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38822946404737967175158659 58234419607106950762737989)
            ·
              refine ⟨10918953676332553268013373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58234419607106950762737989 10918953676332553268013373)
              ·
                refine ⟨4094607628624707475505015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10918953676332553268013373 4094607628624707475505015)
                ·
                  refine ⟨6141911442937061213257523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4094607628624707475505015 6141911442937061213257523)
                  ·
                    refine ⟨9212867164405591819886285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6141911442937061213257523 9212867164405591819886285)
                    ·
                      refine ⟨3454825186652096932457357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9212867164405591819886285 3454825186652096932457357)
                      ·
                        rfl

theorem cell23_6728248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 1, 1, 3].length) (baseStart_6728248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728248 prefixEnd_6728248 := by exact prefixLift 6728248
  have htrace : WordTrace (prefixWord ++ tailWord_6728248) baseStart_6728248 baseEnd_6728248 := by
    simpa [prefixWord, tailWord_6728248, baseEnd_6728248] using wordTrace_append hprefix tailTrace_6728248
  have hstable : (prefixWord ++ tailWord_6728248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728248).length < 2 ^ (prefixWord ++ tailWord_6728248).sum := by decide
  have hdescent : baseEnd_6728248 < baseStart_6728248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728267 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 4]
def baseStart_6728267 : Nat := 118140960795 + 6728267 * 2 ^ 59
def prefixEnd_6728267 : Nat := 4983230072969 + 3 ^ 40 * 6728267 * 2
def baseEnd_6728267 : Nat := 3454834942784532358119769

theorem tailTrace_6728267 : CollatzResearch.WordTrace tailWord_6728267 prefixEnd_6728267 3454834942784532358119769 := by
  unfold tailWord_6728267
  simp only [CollatzResearch.WordTrace]
  refine ⟨245400057915645230364463055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163600038610430153576308703 245400057915645230364463055)
  ·
    refine ⟨368100086873467845546694583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245400057915645230364463055 368100086873467845546694583)
    ·
      refine ⟨552150130310201768320041875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368100086873467845546694583 552150130310201768320041875)
      ·
        refine ⟨828225195465302652480062813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552150130310201768320041875 828225195465302652480062813)
        ·
          refine ⟨310584448299488494680023555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 828225195465302652480062813 310584448299488494680023555)
          ·
            refine ⟨465876672449232742020035333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310584448299488494680023555 465876672449232742020035333)
            ·
              refine ⟨87351876084231139128756625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 465876672449232742020035333 87351876084231139128756625)
              ·
                refine ⟨65513907063173354346567469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87351876084231139128756625 65513907063173354346567469)
                ·
                  refine ⟨24567715148690007879962801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65513907063173354346567469 24567715148690007879962801)
                  ·
                    refine ⟨18425786361517505909972101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24567715148690007879962801 18425786361517505909972101)
                    ·
                      refine ⟨3454834942784532358119769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18425786361517505909972101 3454834942784532358119769)
                      ·
                        rfl

theorem cell23_6728267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 4].length) (baseStart_6728267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728267 prefixEnd_6728267 := by exact prefixLift 6728267
  have htrace : WordTrace (prefixWord ++ tailWord_6728267) baseStart_6728267 baseEnd_6728267 := by
    simpa [prefixWord, tailWord_6728267, baseEnd_6728267] using wordTrace_append hprefix tailTrace_6728267
  have hstable : (prefixWord ++ tailWord_6728267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728267).length < 2 ^ (prefixWord ++ tailWord_6728267).sum := by decide
  have hdescent : baseEnd_6728267 < baseStart_6728267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728271 : List Nat := [1, 1, 2, 1, 1, 2, 5, 3, 3, 2, 2]
def baseStart_6728271 : Nat := 118140960795 + 6728271 * 2 ^ 59
def prefixEnd_6728271 : Nat := 4983230072969 + 3 ^ 40 * 6728271 * 2
def baseEnd_6728271 : Nat := 3454836996707150342469751

theorem tailTrace_6728271 : CollatzResearch.WordTrace tailWord_6728271 prefixEnd_6728271 3454836996707150342469751 := by
  unfold tailWord_6728271
  simp only [CollatzResearch.WordTrace]
  refine ⟨245400203807630739047608667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163600135871753826031739111 245400203807630739047608667)
  ·
    refine ⟨368100305711446108571413001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245400203807630739047608667 368100305711446108571413001)
    ·
      refine ⟨276075229283584581428559751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368100305711446108571413001 276075229283584581428559751)
      ·
        refine ⟨414112843925376872142839627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276075229283584581428559751 414112843925376872142839627)
        ·
          refine ⟨621169265888065308214259441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414112843925376872142839627 621169265888065308214259441)
          ·
            refine ⟨465876949416048981160694581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 621169265888065308214259441 465876949416048981160694581)
            ·
              refine ⟨43675964007754591983815117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 465876949416048981160694581 43675964007754591983815117)
              ·
                refine ⟨16378486502907971993930669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43675964007754591983815117 16378486502907971993930669)
                ·
                  refine ⟨6141932438590489497724001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16378486502907971993930669 6141932438590489497724001)
                  ·
                    refine ⟨4606449328942867123293001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6141932438590489497724001 4606449328942867123293001)
                    ·
                      refine ⟨3454836996707150342469751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4606449328942867123293001 3454836996707150342469751)
                      ·
                        rfl

theorem cell23_6728271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 2, 2].length) (baseStart_6728271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728271 prefixEnd_6728271 := by exact prefixLift 6728271
  have htrace : WordTrace (prefixWord ++ tailWord_6728271) baseStart_6728271 baseEnd_6728271 := by
    simpa [prefixWord, tailWord_6728271, baseEnd_6728271] using wordTrace_append hprefix tailTrace_6728271
  have hstable : (prefixWord ++ tailWord_6728271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728271).length < 2 ^ (prefixWord ++ tailWord_6728271).sum := by decide
  have hdescent : baseEnd_6728271 < baseStart_6728271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728274 : List Nat := [3, 2, 2, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_6728274 : Nat := 118140960795 + 6728274 * 2 ^ 59
def prefixEnd_6728274 : Nat := 4983230072969 + 3 ^ 40 * 6728274 * 2
def baseEnd_6728274 : Nat := 3454838537149113830732237

theorem tailTrace_6728274 : CollatzResearch.WordTrace tailWord_6728274 prefixEnd_6728274 3454838537149113830732237 := by
  unfold tailWord_6728274
  simp only [CollatzResearch.WordTrace]
  refine ⟨61350078306654967639991969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163600208817746580373311917 61350078306654967639991969)
  ·
    refine ⟨46012558729991225729993977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61350078306654967639991969 46012558729991225729993977)
    ·
      refine ⟨34509419047493419297495483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46012558729991225729993977 34509419047493419297495483)
      ·
        refine ⟨51764128571240128946243225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34509419047493419297495483 51764128571240128946243225)
        ·
          refine ⟨38823096428430096709682419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51764128571240128946243225 38823096428430096709682419)
          ·
            refine ⟨58234644642645145064523629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38823096428430096709682419 58234644642645145064523629)
            ·
              refine ⟨21837991740991929399196361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58234644642645145064523629 21837991740991929399196361)
              ·
                refine ⟨16378493805743947049397271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21837991740991929399196361 16378493805743947049397271)
                ·
                  refine ⟨24567740708615920574095907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16378493805743947049397271 24567740708615920574095907)
                  ·
                    refine ⟨36851611062923880861143861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24567740708615920574095907 36851611062923880861143861)
                    ·
                      refine ⟨3454838537149113830732237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36851611062923880861143861 3454838537149113830732237)
                      ·
                        rfl

theorem cell23_6728274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_6728274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728274 prefixEnd_6728274 := by exact prefixLift 6728274
  have htrace : WordTrace (prefixWord ++ tailWord_6728274) baseStart_6728274 baseEnd_6728274 := by
    simpa [prefixWord, tailWord_6728274, baseEnd_6728274] using wordTrace_append hprefix tailTrace_6728274
  have hstable : (prefixWord ++ tailWord_6728274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728274).length < 2 ^ (prefixWord ++ tailWord_6728274).sum := by decide
  have hdescent : baseEnd_6728274 < baseStart_6728274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728291 : List Nat := [1, 1, 1, 5, 1, 2, 4, 2, 1, 2, 3]
def baseStart_6728291 : Nat := 118140960795 + 6728291 * 2 ^ 59
def prefixEnd_6728291 : Nat := 4983230072969 + 3 ^ 40 * 6728291 * 2
def baseEnd_6728291 : Nat := 3454847266320240264219659

theorem tailTrace_6728291 : CollatzResearch.WordTrace tailWord_6728291 prefixEnd_6728291 3454847266320240264219659 := by
  unfold tailWord_6728291
  simp only [CollatzResearch.WordTrace]
  refine ⟨245400933267558282463336727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163600622178372188308891151 245400933267558282463336727)
  ·
    refine ⟨368101399901337423695005091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245400933267558282463336727 368101399901337423695005091)
    ·
      refine ⟨552152099852006135542507637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368101399901337423695005091 552152099852006135542507637)
      ·
        refine ⟨51764259361125575207110091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 552152099852006135542507637 51764259361125575207110091)
        ·
          refine ⟨77646389041688362810665137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51764259361125575207110091 77646389041688362810665137)
          ·
            refine ⟨58234791781266272107998853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77646389041688362810665137 58234791781266272107998853)
            ·
              refine ⟨10919023458987426020249785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58234791781266272107998853 10919023458987426020249785)
              ·
                refine ⟨8189267594240569515187339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10919023458987426020249785 8189267594240569515187339)
                ·
                  refine ⟨12283901391360854272781009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8189267594240569515187339 12283901391360854272781009)
                  ·
                    refine ⟨9212926043520640704585757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12283901391360854272781009 9212926043520640704585757)
                    ·
                      refine ⟨3454847266320240264219659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9212926043520640704585757 3454847266320240264219659)
                      ·
                        rfl

theorem cell23_6728291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_6728291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728291 prefixEnd_6728291 := by exact prefixLift 6728291
  have htrace : WordTrace (prefixWord ++ tailWord_6728291) baseStart_6728291 baseEnd_6728291 := by
    simpa [prefixWord, tailWord_6728291, baseEnd_6728291] using wordTrace_append hprefix tailTrace_6728291
  have hstable : (prefixWord ++ tailWord_6728291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728291).length < 2 ^ (prefixWord ++ tailWord_6728291).sum := by decide
  have hdescent : baseEnd_6728291 < baseStart_6728291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728314 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2]
def baseStart_6728314 : Nat := 118140960795 + 6728314 * 2 ^ 59
def prefixEnd_6728314 : Nat := 4983230072969 + 3 ^ 40 * 6728314 * 2
def baseEnd_6728314 : Nat := 3454859076375293674232053

theorem tailTrace_6728314 : CollatzResearch.WordTrace tailWord_6728314 prefixEnd_6728314 3454859076375293674232053 := by
  unfold tailWord_6728314
  simp only [CollatzResearch.WordTrace]
  refine ⟨61350443036618739347855999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163601181430983304927615997 61350443036618739347855999)
  ·
    refine ⟨92025664554928109021783999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61350443036618739347855999 92025664554928109021783999)
    ·
      refine ⟨138038496832392163532675999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92025664554928109021783999 138038496832392163532675999)
      ·
        refine ⟨207057745248588245299013999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138038496832392163532675999 207057745248588245299013999)
        ·
          refine ⟨310586617872882367948520999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207057745248588245299013999 310586617872882367948520999)
          ·
            refine ⟨465879926809323551922781499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310586617872882367948520999 465879926809323551922781499)
            ·
              refine ⟨698819890213985327884172249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465879926809323551922781499 698819890213985327884172249)
              ·
                refine ⟨524114917660488995913129187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698819890213985327884172249 524114917660488995913129187)
                ·
                  refine ⟨786172376490733493869693781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 524114917660488995913129187 786172376490733493869693781)
                  ·
                    refine ⟨4606478768500391565642737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 786172376490733493869693781 4606478768500391565642737)
                    ·
                      refine ⟨3454859076375293674232053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4606478768500391565642737 3454859076375293674232053)
                      ·
                        rfl

theorem cell23_6728314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2].length) (baseStart_6728314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728314 prefixEnd_6728314 := by exact prefixLift 6728314
  have htrace : WordTrace (prefixWord ++ tailWord_6728314) baseStart_6728314 baseEnd_6728314 := by
    simpa [prefixWord, tailWord_6728314, baseEnd_6728314] using wordTrace_append hprefix tailTrace_6728314
  have hstable : (prefixWord ++ tailWord_6728314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728314).length < 2 ^ (prefixWord ++ tailWord_6728314).sum := by decide
  have hdescent : baseEnd_6728314 < baseStart_6728314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728321 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 4, 1, 3]
def baseStart_6728321 : Nat := 118140960795 + 6728321 * 2 ^ 59
def prefixEnd_6728321 : Nat := 4983230072969 + 3 ^ 40 * 6728321 * 2
def baseEnd_6728321 : Nat := 3454862670739875146844521

theorem tailTrace_6728321 : CollatzResearch.WordTrace tailWord_6728321 prefixEnd_6728321 3454862670739875146844521 := by
  unfold tailWord_6728321
  simp only [CollatzResearch.WordTrace]
  refine ⟨245402027457449597586928817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163601351638299731724619211 245402027457449597586928817)
  ·
    refine ⟨184051520593087198190196613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245402027457449597586928817 184051520593087198190196613)
    ·
      refine ⟨34509660111203849660661865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184051520593087198190196613 34509660111203849660661865)
      ·
        refine ⟨25882245083402887245496399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34509660111203849660661865 25882245083402887245496399)
        ·
          refine ⟨38823367625104330868244599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25882245083402887245496399 38823367625104330868244599)
          ·
            refine ⟨58235051437656496302366899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38823367625104330868244599 58235051437656496302366899)
            ·
              refine ⟨87352577156484744453550349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58235051437656496302366899 87352577156484744453550349)
              ·
                refine ⟨32757216433681779170081381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87352577156484744453550349 32757216433681779170081381)
                ·
                  refine ⟨6141978081315333594390259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32757216433681779170081381 6141978081315333594390259)
                  ·
                    refine ⟨9212967121973000391585389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6141978081315333594390259 9212967121973000391585389)
                    ·
                      refine ⟨3454862670739875146844521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9212967121973000391585389 3454862670739875146844521)
                      ·
                        rfl

theorem cell23_6728321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_6728321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728321 prefixEnd_6728321 := by exact prefixLift 6728321
  have htrace : WordTrace (prefixWord ++ tailWord_6728321) baseStart_6728321 baseEnd_6728321 := by
    simpa [prefixWord, tailWord_6728321, baseEnd_6728321] using wordTrace_append hprefix tailTrace_6728321
  have hstable : (prefixWord ++ tailWord_6728321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728321).length < 2 ^ (prefixWord ++ tailWord_6728321).sum := by decide
  have hdescent : baseEnd_6728321 < baseStart_6728321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728337 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 6, 6]
def baseStart_6728337 : Nat := 118140960795 + 6728337 * 2 ^ 59
def prefixEnd_6728337 : Nat := 4983230072969 + 3 ^ 40 * 6728337 * 2
def baseEnd_6728337 : Nat := 1151623628810115694748149

theorem tailTrace_6728337 : CollatzResearch.WordTrace tailWord_6728337 prefixEnd_6728337 1151623628810115694748149 := by
  unfold tailWord_6728337
  simp only [CollatzResearch.WordTrace]
  refine ⟨245402611025391632319511265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163601740683594421546340843 245402611025391632319511265)
  ·
    refine ⟨184051958269043724239633449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245402611025391632319511265 184051958269043724239633449)
    ·
      refine ⟨138038968701782793179725087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184051958269043724239633449 138038968701782793179725087)
      ·
        refine ⟨207058453052674189769587631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138038968701782793179725087 207058453052674189769587631)
        ·
          refine ⟨310587679579011284654381447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207058453052674189769587631 310587679579011284654381447)
          ·
            refine ⟨465881519368516926981572171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310587679579011284654381447 465881519368516926981572171)
            ·
              refine ⟨698822279052775390472358257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465881519368516926981572171 698822279052775390472358257)
              ·
                refine ⟨524116709289581542854268693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698822279052775390472358257 524116709289581542854268693)
                ·
                  refine ⟨24567970747949134821293845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 524116709289581542854268693 24567970747949134821293845)
                  ·
                    refine ⟨1151623628810115694748149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24567970747949134821293845 1151623628810115694748149)
                    ·
                      rfl

theorem cell23_6728337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_6728337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728337 prefixEnd_6728337 := by exact prefixLift 6728337
  have htrace : WordTrace (prefixWord ++ tailWord_6728337) baseStart_6728337 baseEnd_6728337 := by
    simpa [prefixWord, tailWord_6728337, baseEnd_6728337] using wordTrace_append hprefix tailTrace_6728337
  have hstable : (prefixWord ++ tailWord_6728337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728337).length < 2 ^ (prefixWord ++ tailWord_6728337).sum := by decide
  have hdescent : baseEnd_6728337 < baseStart_6728337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
