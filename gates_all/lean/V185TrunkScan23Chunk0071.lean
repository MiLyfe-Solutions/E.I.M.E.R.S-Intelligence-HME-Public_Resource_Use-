import V185TrunkScan23Chunk0070

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_422401 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 2, 6]
def baseStart_422401 : Nat := 118140960795 + 422401 * 2 ^ 59
def prefixEnd_422401 : Nat := 4983230072969 + 3 ^ 40 * 422401 * 2
def baseEnd_422401 : Nat := 72298247313302362614973

theorem tailTrace_422401 : CollatzResearch.WordTrace tailWord_422401 prefixEnd_422401 72298247313302362614973 := by
  unfold tailWord_422401
  simp only [CollatzResearch.WordTrace]
  refine ⟨15406230142720792192523057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10270820095147194795015371 15406230142720792192523057)
  ·
    refine ⟨11554672607040594144392293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15406230142720792192523057 11554672607040594144392293)
    ·
      refine ⟨2166501113820111402073555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11554672607040594144392293 2166501113820111402073555)
      ·
        refine ⟨3249751670730167103110333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2166501113820111402073555 3249751670730167103110333)
        ·
          refine ⟨1218656876523812663666375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3249751670730167103110333 1218656876523812663666375)
          ·
            refine ⟨1827985314785718995499563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1218656876523812663666375 1827985314785718995499563)
            ·
              refine ⟨2741977972178578493249345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1827985314785718995499563 2741977972178578493249345)
              ·
                refine ⟨2056483479133933869937009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2741977972178578493249345 2056483479133933869937009)
                ·
                  refine ⟨1542362609350450402452757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2056483479133933869937009 1542362609350450402452757)
                  ·
                    refine ⟨72298247313302362614973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1542362609350450402452757 72298247313302362614973)
                    ·
                      rfl

theorem cell23_422401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_422401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422401 prefixEnd_422401 := by exact prefixLift 422401
  have htrace : WordTrace (prefixWord ++ tailWord_422401) baseStart_422401 baseEnd_422401 := by
    simpa [prefixWord, tailWord_422401, baseEnd_422401] using wordTrace_append hprefix tailTrace_422401
  have hstable : (prefixWord ++ tailWord_422401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422401).length < 2 ^ (prefixWord ++ tailWord_422401).sum := by decide
  have hdescent : baseEnd_422401 < baseStart_422401 := by decide
  rcases family_descends (prefixWord ++ tailWord_422401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422402 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_422402 : Nat := 118140960795 + 422402 * 2 ^ 59
def prefixEnd_422402 : Nat := 4983230072969 + 3 ^ 40 * 422402 * 2
def baseEnd_422402 : Nat := 216895255420561583932415

theorem tailTrace_422402 : CollatzResearch.WordTrace tailWord_422402 prefixEnd_422402 216895255420561583932415 := by
  unfold tailWord_422402
  simp only [CollatzResearch.WordTrace]
  refine ⟨3851566653929292340827365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10270844410478112908872973 3851566653929292340827365)
  ·
    refine ⟨722168747611742313905131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3851566653929292340827365 722168747611742313905131)
    ·
      refine ⟨1083253121417613470857697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 722168747611742313905131 1083253121417613470857697)
      ·
        refine ⟨812439841063210103143273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1083253121417613470857697 812439841063210103143273)
        ·
          refine ⟨609329880797407577357455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 812439841063210103143273 609329880797407577357455)
          ·
            refine ⟨913994821196111366036183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609329880797407577357455 913994821196111366036183)
            ·
              refine ⟨1370992231794167049054275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913994821196111366036183 1370992231794167049054275)
              ·
                refine ⟨2056488347691250573581413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370992231794167049054275 2056488347691250573581413)
                ·
                  refine ⟨385591565192109482546515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2056488347691250573581413 385591565192109482546515)
                  ·
                    refine ⟨578387347788164223819773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 385591565192109482546515 578387347788164223819773)
                    ·
                      refine ⟨216895255420561583932415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 578387347788164223819773 216895255420561583932415)
                      ·
                        rfl

theorem cell23_422402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_422402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422402 prefixEnd_422402 := by exact prefixLift 422402
  have htrace : WordTrace (prefixWord ++ tailWord_422402) baseStart_422402 baseEnd_422402 := by
    simpa [prefixWord, tailWord_422402, baseEnd_422402] using wordTrace_append hprefix tailTrace_422402
  have hstable : (prefixWord ++ tailWord_422402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422402).length < 2 ^ (prefixWord ++ tailWord_422402).sum := by decide
  have hdescent : baseEnd_422402 < baseStart_422402 := by decide
  rcases family_descends (prefixWord ++ tailWord_422402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422421 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 2, 2, 4]
def baseStart_422421 : Nat := 118140960795 + 422421 * 2 ^ 59
def prefixEnd_422421 : Nat := 4983230072969 + 3 ^ 40 * 422421 * 2
def baseEnd_422421 : Nat := 216905011552997009594827

theorem tailTrace_422421 : CollatzResearch.WordTrace tailWord_422421 prefixEnd_422421 216905011552997009594827 := by
  unfold tailWord_422421
  simp only [CollatzResearch.WordTrace]
  refine ⟨15406959602648335608251117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10271306401765557072167411 15406959602648335608251117)
  ·
    refine ⟨5777609850993125853094169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15406959602648335608251117 5777609850993125853094169)
    ·
      refine ⟨4333207388244844389820627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5777609850993125853094169 4333207388244844389820627)
      ·
        refine ⟨6499811082367266584730941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4333207388244844389820627 6499811082367266584730941)
        ·
          refine ⟨2437429155887724969274103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6499811082367266584730941 2437429155887724969274103)
          ·
            refine ⟨3656143733831587453911155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2437429155887724969274103 3656143733831587453911155)
            ·
              refine ⟨5484215600747381180866733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3656143733831587453911155 5484215600747381180866733)
              ·
                refine ⟨2056580850280267942825025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5484215600747381180866733 2056580850280267942825025)
                ·
                  refine ⟨1542435637710200957118769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2056580850280267942825025 1542435637710200957118769)
                  ·
                    refine ⟨1156826728282650717839077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1542435637710200957118769 1156826728282650717839077)
                    ·
                      refine ⟨216905011552997009594827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1156826728282650717839077 216905011552997009594827)
                      ·
                        rfl

theorem cell23_422421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_422421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422421 prefixEnd_422421 := by exact prefixLift 422421
  have htrace : WordTrace (prefixWord ++ tailWord_422421) baseStart_422421 baseEnd_422421 := by
    simpa [prefixWord, tailWord_422421, baseEnd_422421] using wordTrace_append hprefix tailTrace_422421
  have hstable : (prefixWord ++ tailWord_422421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422421).length < 2 ^ (prefixWord ++ tailWord_422421).sum := by decide
  have hdescent : baseEnd_422421 < baseStart_422421 := by decide
  rcases family_descends (prefixWord ++ tailWord_422421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422448 : List Nat := [2, 1, 1, 1, 2, 3, 5, 3, 5]
def baseStart_422448 : Nat := 118140960795 + 422448 * 2 ^ 59
def prefixEnd_422448 : Nat := 4983230072969 + 3 ^ 40 * 422448 * 2
def baseEnd_422448 : Nat := 24102097281185378217467

theorem tailTrace_422448 : CollatzResearch.WordTrace tailWord_422448 prefixEnd_422448 24102097281185378217467 := by
  unfold tailWord_422448
  simp only [CollatzResearch.WordTrace]
  refine ⟨7703972186775259609741999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10271962915700346146322665 7703972186775259609741999)
  ·
    refine ⟨11555958280162889414612999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7703972186775259609741999 11555958280162889414612999)
    ·
      refine ⟨17333937420244334121919499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11555958280162889414612999 17333937420244334121919499)
      ·
        refine ⟨26000906130366501182879249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17333937420244334121919499 26000906130366501182879249)
        ·
          refine ⟨19500679597774875887159437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26000906130366501182879249 19500679597774875887159437)
          ·
            refine ⟨7312754849165578457684789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19500679597774875887159437 7312754849165578457684789)
            ·
              refine ⟨685570767109272980407949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7312754849165578457684789 685570767109272980407949)
              ·
                refine ⟨257089037665977367652981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 685570767109272980407949 257089037665977367652981)
                ·
                  refine ⟨24102097281185378217467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 257089037665977367652981 24102097281185378217467)
                  ·
                    rfl

theorem cell23_422448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 5].length) (baseStart_422448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422448 prefixEnd_422448 := by exact prefixLift 422448
  have htrace : WordTrace (prefixWord ++ tailWord_422448) baseStart_422448 baseEnd_422448 := by
    simpa [prefixWord, tailWord_422448, baseEnd_422448] using wordTrace_append hprefix tailTrace_422448
  have hstable : (prefixWord ++ tailWord_422448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422448).length < 2 ^ (prefixWord ++ tailWord_422448).sum := by decide
  have hdescent : baseEnd_422448 < baseStart_422448 := by decide
  rcases family_descends (prefixWord ++ tailWord_422448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422471 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 7]
def baseStart_422471 : Nat := 118140960795 + 422471 * 2 ^ 59
def prefixEnd_422471 : Nat := 4983230072969 + 3 ^ 40 * 422471 * 2
def baseEnd_422471 : Nat := 216930685585721813969597

theorem tailTrace_422471 : CollatzResearch.WordTrace tailWord_422471 prefixEnd_422471 216930685585721813969597 := by
  unfold tailWord_422471
  simp only [CollatzResearch.WordTrace]
  refine ⟨15408783252467194147571267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10272522168311462765047511 15408783252467194147571267)
  ·
    refine ⟨23113174878700791221356901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15408783252467194147571267 23113174878700791221356901)
    ·
      refine ⟨4333720289756398354004419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23113174878700791221356901 4333720289756398354004419)
      ·
        refine ⟨6500580434634597531006629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4333720289756398354004419 6500580434634597531006629)
        ·
          refine ⟨1218858831493987037063743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6500580434634597531006629 1218858831493987037063743)
          ·
            refine ⟨1828288247240980555595615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1218858831493987037063743 1828288247240980555595615)
            ·
              refine ⟨2742432370861470833393423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1828288247240980555595615 2742432370861470833393423)
              ·
                refine ⟨4113648556292206250090135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2742432370861470833393423 4113648556292206250090135)
                ·
                  refine ⟨6170472834438309375135203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4113648556292206250090135 6170472834438309375135203)
                  ·
                    refine ⟨9255709251657464062702805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6170472834438309375135203 9255709251657464062702805)
                    ·
                      refine ⟨216930685585721813969597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9255709251657464062702805 216930685585721813969597)
                      ·
                        rfl

theorem cell23_422471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_422471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422471 prefixEnd_422471 := by exact prefixLift 422471
  have htrace : WordTrace (prefixWord ++ tailWord_422471) baseStart_422471 baseEnd_422471 := by
    simpa [prefixWord, tailWord_422471, baseEnd_422471] using wordTrace_append hprefix tailTrace_422471
  have hstable : (prefixWord ++ tailWord_422471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422471).length < 2 ^ (prefixWord ++ tailWord_422471).sum := by decide
  have hdescent : baseEnd_422471 < baseStart_422471 := by decide
  rcases family_descends (prefixWord ++ tailWord_422471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422608 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 3]
def baseStart_422608 : Nat := 118140960795 + 422608 * 2 ^ 59
def prefixEnd_422608 : Nat := 4983230072969 + 3 ^ 40 * 422608 * 2
def baseEnd_422608 : Nat := 217001032435387777956467

theorem tailTrace_422608 : CollatzResearch.WordTrace tailWord_422608 prefixEnd_422608 217001032435387777956467 := by
  unfold tailWord_422608
  simp only [CollatzResearch.WordTrace]
  refine ⟨7706890026485433272654239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10275853368647244363538985 7706890026485433272654239)
  ·
    refine ⟨11560335039728149908981359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7706890026485433272654239 11560335039728149908981359)
    ·
      refine ⟨17340502559592224863472039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11560335039728149908981359 17340502559592224863472039)
      ·
        refine ⟨26010753839388337295208059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17340502559592224863472039 26010753839388337295208059)
        ·
          refine ⟨39016130759082505942812089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26010753839388337295208059 39016130759082505942812089)
          ·
            refine ⟨29262098069311879457109067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39016130759082505942812089 29262098069311879457109067)
            ·
              refine ⟨43893147103967819185663601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29262098069311879457109067 43893147103967819185663601)
              ·
                refine ⟨32919860327975864389247701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43893147103967819185663601 32919860327975864389247701)
                ·
                  refine ⟨771559226436934321622993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 32919860327975864389247701 771559226436934321622993)
                  ·
                    refine ⟨578669419827700741217245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 771559226436934321622993 578669419827700741217245)
                    ·
                      refine ⟨217001032435387777956467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 578669419827700741217245 217001032435387777956467)
                      ·
                        rfl

theorem cell23_422608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 3].length) (baseStart_422608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422608 prefixEnd_422608 := by exact prefixLift 422608
  have htrace : WordTrace (prefixWord ++ tailWord_422608) baseStart_422608 baseEnd_422608 := by
    simpa [prefixWord, tailWord_422608, baseEnd_422608] using wordTrace_append hprefix tailTrace_422608
  have hstable : (prefixWord ++ tailWord_422608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422608).length < 2 ^ (prefixWord ++ tailWord_422608).sum := by decide
  have hdescent : baseEnd_422608 < baseStart_422608 := by decide
  rcases family_descends (prefixWord ++ tailWord_422608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422618 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4]
def baseStart_422618 : Nat := 118140960795 + 422618 * 2 ^ 59
def prefixEnd_422618 : Nat := 4983230072969 + 3 ^ 40 * 422618 * 2
def baseEnd_422618 : Nat := 217006167241932738831421

theorem tailTrace_422618 : CollatzResearch.WordTrace tailWord_422618 prefixEnd_422618 217006167241932738831421 := by
  unfold tailWord_422618
  simp only [CollatzResearch.WordTrace]
  refine ⟨3853536195733659563293127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10276096521956425502115005 3853536195733659563293127)
  ·
    refine ⟨5780304293600489344939691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3853536195733659563293127 5780304293600489344939691)
    ·
      refine ⟨8670456440400734017409537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5780304293600489344939691 8670456440400734017409537)
      ·
        refine ⟨6502842330300550513057153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8670456440400734017409537 6502842330300550513057153)
        ·
          refine ⟨4877131747725412884792865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6502842330300550513057153 4877131747725412884792865)
          ·
            refine ⟨3657848810794059663594649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4877131747725412884792865 3657848810794059663594649)
            ·
              refine ⟨2743386608095544747695987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3657848810794059663594649 2743386608095544747695987)
              ·
                refine ⟨4115079912143317121543981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2743386608095544747695987 4115079912143317121543981)
                ·
                  refine ⟨1543154967053743920578993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4115079912143317121543981 1543154967053743920578993)
                  ·
                    refine ⟨1157366225290307940434245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1543154967053743920578993 1157366225290307940434245)
                    ·
                      refine ⟨217006167241932738831421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1157366225290307940434245 217006167241932738831421)
                      ·
                        rfl

theorem cell23_422618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_422618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422618 prefixEnd_422618 := by exact prefixLift 422618
  have htrace : WordTrace (prefixWord ++ tailWord_422618) baseStart_422618 baseEnd_422618 := by
    simpa [prefixWord, tailWord_422618, baseEnd_422618] using wordTrace_append hprefix tailTrace_422618
  have hstable : (prefixWord ++ tailWord_422618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422618).length < 2 ^ (prefixWord ++ tailWord_422618).sum := by decide
  have hdescent : baseEnd_422618 < baseStart_422618 := by decide
  rcases family_descends (prefixWord ++ tailWord_422618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422625 : List Nat := [1, 2, 3, 1, 4, 2, 2, 1, 1, 1, 5]
def baseStart_422625 : Nat := 118140960795 + 422625 * 2 ^ 59
def prefixEnd_422625 : Nat := 4983230072969 + 3 ^ 40 * 422625 * 2
def baseEnd_422625 : Nat := 217009761606514211443889

theorem tailTrace_422625 : CollatzResearch.WordTrace tailWord_422625 prefixEnd_422625 217009761606514211443889 := by
  unfold tailWord_422625
  simp only [CollatzResearch.WordTrace]
  refine ⟨15414400093909278448677329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10276266729272852299118219 15414400093909278448677329)
  ·
    refine ⟨11560800070431958836507997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15414400093909278448677329 11560800070431958836507997)
    ·
      refine ⟨4335300026411984563690499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11560800070431958836507997 4335300026411984563690499)
      ·
        refine ⟨6502950039617976845535749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4335300026411984563690499 6502950039617976845535749)
        ·
          refine ⟨1219303132428370658537953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6502950039617976845535749 1219303132428370658537953)
          ·
            refine ⟨914477349321277993903465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1219303132428370658537953 914477349321277993903465)
            ·
              refine ⟨685858011990958495427599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 914477349321277993903465 685858011990958495427599)
              ·
                refine ⟨1028787017986437743141399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 685858011990958495427599 1028787017986437743141399)
                ·
                  refine ⟨1543180526979656614712099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1028787017986437743141399 1543180526979656614712099)
                  ·
                    refine ⟨2314770790469484922068149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1543180526979656614712099 2314770790469484922068149)
                    ·
                      refine ⟨217009761606514211443889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2314770790469484922068149 217009761606514211443889)
                      ·
                        rfl

theorem cell23_422625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_422625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422625 prefixEnd_422625 := by exact prefixLift 422625
  have htrace : WordTrace (prefixWord ++ tailWord_422625) baseStart_422625 baseEnd_422625 := by
    simpa [prefixWord, tailWord_422625, baseEnd_422625] using wordTrace_append hprefix tailTrace_422625
  have hstable : (prefixWord ++ tailWord_422625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422625).length < 2 ^ (prefixWord ++ tailWord_422625).sum := by decide
  have hdescent : baseEnd_422625 < baseStart_422625 := by decide
  rcases family_descends (prefixWord ++ tailWord_422625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422628 : List Nat := [2, 3, 1, 1, 1, 6, 9]
def baseStart_422628 : Nat := 118140960795 + 422628 * 2 ^ 59
def prefixEnd_422628 : Nat := 4983230072969 + 3 ^ 40 * 422628 * 2
def baseEnd_422628 : Nat := 2679151877141699996375

theorem tailTrace_422628 : CollatzResearch.WordTrace tailWord_422628 prefixEnd_422628 2679151877141699996375 := by
  unfold tailWord_422628
  simp only [CollatzResearch.WordTrace]
  refine ⟨7707254756449204980518269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10276339675265606640691025 7707254756449204980518269)
  ·
    refine ⟨2890220533668451867694351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7707254756449204980518269 2890220533668451867694351)
    ·
      refine ⟨4335330800502677801541527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2890220533668451867694351 4335330800502677801541527)
      ·
        refine ⟨6502996200754016702312291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4335330800502677801541527 6502996200754016702312291)
        ·
          refine ⟨9754494301131025053468437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6502996200754016702312291 9754494301131025053468437)
          ·
            refine ⟨457241920365516799381333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9754494301131025053468437 457241920365516799381333)
            ·
              refine ⟨2679151877141699996375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 457241920365516799381333 2679151877141699996375)
              ·
                rfl

theorem cell23_422628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 9].length) (baseStart_422628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422628 prefixEnd_422628 := by exact prefixLift 422628
  have htrace : WordTrace (prefixWord ++ tailWord_422628) baseStart_422628 baseEnd_422628 := by
    simpa [prefixWord, tailWord_422628, baseEnd_422628] using wordTrace_append hprefix tailTrace_422628
  have hstable : (prefixWord ++ tailWord_422628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422628).length < 2 ^ (prefixWord ++ tailWord_422628).sum := by decide
  have hdescent : baseEnd_422628 < baseStart_422628 := by decide
  rcases family_descends (prefixWord ++ tailWord_422628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422639 : List Nat := [1, 1, 2, 1, 5, 4, 1, 1, 3, 2, 2]
def baseStart_422639 : Nat := 118140960795 + 422639 * 2 ^ 59
def prefixEnd_422639 : Nat := 4983230072969 + 3 ^ 40 * 422639 * 2
def baseEnd_422639 : Nat := 217016950335677156668825

theorem tailTrace_422639 : CollatzResearch.WordTrace tailWord_422639 prefixEnd_422639 217016950335677156668825 := by
  unfold tailWord_422639
  simp only [CollatzResearch.WordTrace]
  refine ⟨15414910715858558839686971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10276607143905705893124647 15414910715858558839686971)
  ·
    refine ⟨23122366073787838259530457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15414910715858558839686971 23122366073787838259530457)
    ·
      refine ⟨17341774555340878694647843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23122366073787838259530457 17341774555340878694647843)
      ·
        refine ⟨26012661833011318041971765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17341774555340878694647843 26012661833011318041971765)
        ·
          refine ⟨2438687046844811066434853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26012661833011318041971765 2438687046844811066434853)
          ·
            refine ⟨457253821283402074956535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2438687046844811066434853 457253821283402074956535)
            ·
              refine ⟨685880731925103112434803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457253821283402074956535 685880731925103112434803)
              ·
                refine ⟨1028821097887654668652205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 685880731925103112434803 1028821097887654668652205)
                ·
                  refine ⟨385807911707870500744577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1028821097887654668652205 385807911707870500744577)
                  ·
                    refine ⟨289355933780902875558433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 385807911707870500744577 289355933780902875558433)
                    ·
                      refine ⟨217016950335677156668825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 289355933780902875558433 217016950335677156668825)
                      ·
                        rfl

theorem cell23_422639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 2, 2].length) (baseStart_422639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422639 prefixEnd_422639 := by exact prefixLift 422639
  have htrace : WordTrace (prefixWord ++ tailWord_422639) baseStart_422639 baseEnd_422639 := by
    simpa [prefixWord, tailWord_422639, baseEnd_422639] using wordTrace_append hprefix tailTrace_422639
  have hstable : (prefixWord ++ tailWord_422639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422639).length < 2 ^ (prefixWord ++ tailWord_422639).sum := by decide
  have hdescent : baseEnd_422639 < baseStart_422639 := by decide
  rcases family_descends (prefixWord ++ tailWord_422639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422712 : List Nat := [2, 1, 2, 1, 3, 2, 4, 1, 1, 4, 2]
def baseStart_422712 : Nat := 118140960795 + 422712 * 2 ^ 59
def prefixEnd_422712 : Nat := 4983230072969 + 3 ^ 40 * 422712 * 2
def baseEnd_422712 : Nat := 217054434423455371055989

theorem tailTrace_422712 : CollatzResearch.WordTrace tailWord_422712 prefixEnd_422712 217054434423455371055989 := by
  unfold tailWord_422712
  simp only [CollatzResearch.WordTrace]
  refine ⟨7708786622297046153547195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10278382163062728204729593 7708786622297046153547195)
  ·
    refine ⟨11563179933445569230320793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7708786622297046153547195 11563179933445569230320793)
    ·
      refine ⟨8672384950084176922740595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11563179933445569230320793 8672384950084176922740595)
      ·
        refine ⟨13008577425126265384110893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8672384950084176922740595 13008577425126265384110893)
        ·
          refine ⟨4878216534422349519041585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13008577425126265384110893 4878216534422349519041585)
          ·
            refine ⟨3658662400816762139281189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4878216534422349519041585 3658662400816762139281189)
            ·
              refine ⟨685999200153142901115223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3658662400816762139281189 685999200153142901115223)
              ·
                refine ⟨1028998800229714351672835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 685999200153142901115223 1028998800229714351672835)
                ·
                  refine ⟨1543498200344571527509253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1028998800229714351672835 1543498200344571527509253)
                  ·
                    refine ⟨289405912564607161407985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1543498200344571527509253 289405912564607161407985)
                    ·
                      refine ⟨217054434423455371055989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 289405912564607161407985 217054434423455371055989)
                      ·
                        rfl

theorem cell23_422712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 1, 4, 2].length) (baseStart_422712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422712 prefixEnd_422712 := by exact prefixLift 422712
  have htrace : WordTrace (prefixWord ++ tailWord_422712) baseStart_422712 baseEnd_422712 := by
    simpa [prefixWord, tailWord_422712, baseEnd_422712] using wordTrace_append hprefix tailTrace_422712
  have hstable : (prefixWord ++ tailWord_422712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422712).length < 2 ^ (prefixWord ++ tailWord_422712).sum := by decide
  have hdescent : baseEnd_422712 < baseStart_422712 := by decide
  rcases family_descends (prefixWord ++ tailWord_422712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422745 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 2, 3, 3]
def baseStart_422745 : Nat := 118140960795 + 422745 * 2 ^ 59
def prefixEnd_422745 : Nat := 4983230072969 + 3 ^ 40 * 422745 * 2
def baseEnd_422745 : Nat := 217071379285053741943337

theorem tailTrace_422745 : CollatzResearch.WordTrace tailWord_422745 prefixEnd_422745 217071379285053741943337 := by
  unfold tailWord_422745
  simp only [CollatzResearch.WordTrace]
  refine ⟨15418776853474538943045689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10279184568983025962030459 15418776853474538943045689)
  ·
    refine ⟨11564082640105904207284267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15418776853474538943045689 11564082640105904207284267)
    ·
      refine ⟨17346123960158856310926401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11564082640105904207284267 17346123960158856310926401)
      ·
        refine ⟨13009592970119142233194801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17346123960158856310926401 13009592970119142233194801)
        ·
          refine ⟨9757194727589356674896101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13009592970119142233194801 9757194727589356674896101)
          ·
            refine ⟨1829474011423004376543019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9757194727589356674896101 1829474011423004376543019)
            ·
              refine ⟨2744211017134506564814529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1829474011423004376543019 2744211017134506564814529)
              ·
                refine ⟨2058158262850879923610897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2744211017134506564814529 2058158262850879923610897)
                ·
                  refine ⟨1543618697138159942708173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2058158262850879923610897 1543618697138159942708173)
                  ·
                    refine ⟨578857011426809978515565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1543618697138159942708173 578857011426809978515565)
                    ·
                      refine ⟨217071379285053741943337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 578857011426809978515565 217071379285053741943337)
                      ·
                        rfl

theorem cell23_422745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 3, 3].length) (baseStart_422745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422745 prefixEnd_422745 := by exact prefixLift 422745
  have htrace : WordTrace (prefixWord ++ tailWord_422745) baseStart_422745 baseEnd_422745 := by
    simpa [prefixWord, tailWord_422745, baseEnd_422745] using wordTrace_append hprefix tailTrace_422745
  have hstable : (prefixWord ++ tailWord_422745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422745).length < 2 ^ (prefixWord ++ tailWord_422745).sum := by decide
  have hdescent : baseEnd_422745 < baseStart_422745 := by decide
  rcases family_descends (prefixWord ++ tailWord_422745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422746 : List Nat := [3, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2]
def baseStart_422746 : Nat := 118140960795 + 422746 * 2 ^ 59
def prefixEnd_422746 : Nat := 4983230072969 + 3 ^ 40 * 422746 * 2
def baseEnd_422746 : Nat := 217071892765708238030833

theorem tailTrace_422746 : CollatzResearch.WordTrace tailWord_422746 prefixEnd_422746 217071892765708238030833 := by
  unfold tailWord_422746
  simp only [CollatzResearch.WordTrace]
  refine ⟨3854703331617729028458023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10279208884313944075888061 3854703331617729028458023)
  ·
    refine ⟨5782054997426593542687035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3854703331617729028458023 5782054997426593542687035)
    ·
      refine ⟨8673082496139890314030553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5782054997426593542687035 8673082496139890314030553)
      ·
        refine ⟨6504811872104917735522915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8673082496139890314030553 6504811872104917735522915)
        ·
          refine ⟨9757217808157376603284373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6504811872104917735522915 9757217808157376603284373)
          ·
            refine ⟨457369584757377028278955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9757217808157376603284373 457369584757377028278955)
            ·
              refine ⟨686054377136065542418433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457369584757377028278955 686054377136065542418433)
              ·
                refine ⟨514540782852049156813825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 686054377136065542418433 514540782852049156813825)
                ·
                  refine ⟨385905587139036867610369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 514540782852049156813825 385905587139036867610369)
                  ·
                    refine ⟨289429190354277650707777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 385905587139036867610369 289429190354277650707777)
                    ·
                      refine ⟨217071892765708238030833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 289429190354277650707777 217071892765708238030833)
                      ·
                        rfl

theorem cell23_422746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2].length) (baseStart_422746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422746 prefixEnd_422746 := by exact prefixLift 422746
  have htrace : WordTrace (prefixWord ++ tailWord_422746) baseStart_422746 baseEnd_422746 := by
    simpa [prefixWord, tailWord_422746, baseEnd_422746] using wordTrace_append hprefix tailTrace_422746
  have hstable : (prefixWord ++ tailWord_422746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422746).length < 2 ^ (prefixWord ++ tailWord_422746).sum := by decide
  have hdescent : baseEnd_422746 < baseStart_422746 := by decide
  rcases family_descends (prefixWord ++ tailWord_422746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422778 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 1, 10]
def baseStart_422778 : Nat := 118140960795 + 422778 * 2 ^ 59
def prefixEnd_422778 : Nat := 4983230072969 + 3 ^ 40 * 422778 * 2
def baseEnd_422778 : Nat := 72362774715550704276895

theorem tailTrace_422778 : CollatzResearch.WordTrace tailWord_422778 prefixEnd_422778 72362774715550704276895 := by
  unfold tailWord_422778
  simp only [CollatzResearch.WordTrace]
  refine ⟨3854995115588746394749247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10279986974903323719331325 3854995115588746394749247)
  ·
    refine ⟨5782492673383119592123871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3854995115588746394749247 5782492673383119592123871)
    ·
      refine ⟨8673739010074679388185807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5782492673383119592123871 8673739010074679388185807)
      ·
        refine ⟨13010608515112019082278711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8673739010074679388185807 13010608515112019082278711)
        ·
          refine ⟨19515912772668028623418067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13010608515112019082278711 19515912772668028623418067)
          ·
            refine ⟨29273869159002042935127101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19515912772668028623418067 29273869159002042935127101)
            ·
              refine ⟨10977700934625766100672663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29273869159002042935127101 10977700934625766100672663)
              ·
                refine ⟨16466551401938649151008995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10977700934625766100672663 16466551401938649151008995)
                ·
                  refine ⟨24699827102907973726513493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16466551401938649151008995 24699827102907973726513493)
                  ·
                    refine ⟨72362774715550704276895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 24699827102907973726513493 72362774715550704276895)
                    ·
                      rfl

theorem cell23_422778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_422778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422778 prefixEnd_422778 := by exact prefixLift 422778
  have htrace : WordTrace (prefixWord ++ tailWord_422778) baseStart_422778 baseEnd_422778 := by
    simpa [prefixWord, tailWord_422778, baseEnd_422778] using wordTrace_append hprefix tailTrace_422778
  have hstable : (prefixWord ++ tailWord_422778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422778).length < 2 ^ (prefixWord ++ tailWord_422778).sum := by decide
  have hdescent : baseEnd_422778 < baseStart_422778 := by decide
  rcases family_descends (prefixWord ++ tailWord_422778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422795 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 5, 4]
def baseStart_422795 : Nat := 118140960795 + 422795 * 2 ^ 59
def prefixEnd_422795 : Nat := 4983230072969 + 3 ^ 40 * 422795 * 2
def baseEnd_422795 : Nat := 72365684439259515439369

theorem tailTrace_422795 : CollatzResearch.WordTrace tailWord_422795 prefixEnd_422795 72365684439259515439369 := by
  unfold tailWord_422795
  simp only [CollatzResearch.WordTrace]
  refine ⟨15420600503293397482365839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10280400335528931654910559 15420600503293397482365839)
  ·
    refine ⟨23130900754940096223548759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15420600503293397482365839 23130900754940096223548759)
    ·
      refine ⟨34696351132410144335323139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23130900754940096223548759 34696351132410144335323139)
      ·
        refine ⟨52044526698615216502984709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34696351132410144335323139 52044526698615216502984709)
        ·
          refine ⟨9758348755990353094309633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52044526698615216502984709 9758348755990353094309633)
          ·
            refine ⟨7318761566992764820732225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9758348755990353094309633 7318761566992764820732225)
            ·
              refine ⟨5489071175244573615549169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7318761566992764820732225 5489071175244573615549169)
              ·
                refine ⟨4116803381433430211661877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5489071175244573615549169 4116803381433430211661877)
                ·
                  refine ⟨385950317009384082343301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4116803381433430211661877 385950317009384082343301)
                  ·
                    refine ⟨72365684439259515439369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 385950317009384082343301 72365684439259515439369)
                    ·
                      rfl

theorem cell23_422795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 4].length) (baseStart_422795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422795 prefixEnd_422795 := by exact prefixLift 422795
  have htrace : WordTrace (prefixWord ++ tailWord_422795) baseStart_422795 baseEnd_422795 := by
    simpa [prefixWord, tailWord_422795, baseEnd_422795] using wordTrace_append hprefix tailTrace_422795
  have hstable : (prefixWord ++ tailWord_422795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422795).length < 2 ^ (prefixWord ++ tailWord_422795).sum := by decide
  have hdescent : baseEnd_422795 < baseStart_422795 := by decide
  rcases family_descends (prefixWord ++ tailWord_422795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422825 : List Nat := [1, 2, 1, 1, 1, 1, 7, 3, 6]
def baseStart_422825 : Nat := 118140960795 + 422825 * 2 ^ 59
def prefixEnd_422825 : Nat := 4983230072969 + 3 ^ 40 * 422825 * 2
def baseEnd_422825 : Nat := 24123606415268158771441

theorem tailTrace_422825 : CollatzResearch.WordTrace tailWord_422825 prefixEnd_422825 24123606415268158771441 := by
  unfold tailWord_422825
  simp only [CollatzResearch.WordTrace]
  refine ⟨15421694693184712605957929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10281129795456475070638619 15421694693184712605957929)
  ·
    refine ⟨11566271019888534454468447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15421694693184712605957929 11566271019888534454468447)
    ·
      refine ⟨17349406529832801681702671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11566271019888534454468447 17349406529832801681702671)
      ·
        refine ⟨26024109794749202522554007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17349406529832801681702671 26024109794749202522554007)
        ·
          refine ⟨39036164692123803783831011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26024109794749202522554007 39036164692123803783831011)
          ·
            refine ⟨58554247038185705675746517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39036164692123803783831011 58554247038185705675746517)
            ·
              refine ⟨1372365164957477476775309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 58554247038185705675746517 1372365164957477476775309)
              ·
                refine ⟨514636936859054053790741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1372365164957477476775309 514636936859054053790741)
                ·
                  refine ⟨24123606415268158771441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 514636936859054053790741 24123606415268158771441)
                  ·
                    rfl

theorem cell23_422825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 6].length) (baseStart_422825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422825 prefixEnd_422825 := by exact prefixLift 422825
  have htrace : WordTrace (prefixWord ++ tailWord_422825) baseStart_422825 baseEnd_422825 := by
    simpa [prefixWord, tailWord_422825, baseEnd_422825] using wordTrace_append hprefix tailTrace_422825
  have hstable : (prefixWord ++ tailWord_422825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422825).length < 2 ^ (prefixWord ++ tailWord_422825).sum := by decide
  have hdescent : baseEnd_422825 < baseStart_422825 := by decide
  rcases family_descends (prefixWord ++ tailWord_422825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422836 : List Nat := [2, 5, 2, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_422836 : Nat := 118140960795 + 422836 * 2 ^ 59
def prefixEnd_422836 : Nat := 4983230072969 + 3 ^ 40 * 422836 * 2
def baseEnd_422836 : Nat := 217118106024612885905419

theorem tailTrace_422836 : CollatzResearch.WordTrace tailWord_422836 prefixEnd_422836 217118106024612885905419 := by
  unfold tailWord_422836
  simp only [CollatzResearch.WordTrace]
  refine ⟨7711047948072430742304181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10281397264096574323072241 7711047948072430742304181)
  ·
    refine ⟨722910745131790382091017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7711047948072430742304181 722910745131790382091017)
    ·
      refine ⟨542183058848842786568263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 722910745131790382091017 542183058848842786568263)
      ·
        refine ⟨813274588273264179852395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542183058848842786568263 813274588273264179852395)
        ·
          refine ⟨1219911882409896269778593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813274588273264179852395 1219911882409896269778593)
          ·
            refine ⟨914933911807422202333945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1219911882409896269778593 914933911807422202333945)
            ·
              refine ⟨686200433855566651750459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 914933911807422202333945 686200433855566651750459)
              ·
                refine ⟨1029300650783349977625689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 686200433855566651750459 1029300650783349977625689)
                ·
                  refine ⟨771975488087512483219267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1029300650783349977625689 771975488087512483219267)
                  ·
                    refine ⟨1157963232131268724828901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 771975488087512483219267 1157963232131268724828901)
                    ·
                      refine ⟨217118106024612885905419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1157963232131268724828901 217118106024612885905419)
                      ·
                        rfl

theorem cell23_422836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_422836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422836 prefixEnd_422836 := by exact prefixLift 422836
  have htrace : WordTrace (prefixWord ++ tailWord_422836) baseStart_422836 baseEnd_422836 := by
    simpa [prefixWord, tailWord_422836, baseEnd_422836] using wordTrace_append hprefix tailTrace_422836
  have hstable : (prefixWord ++ tailWord_422836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422836).length < 2 ^ (prefixWord ++ tailWord_422836).sum := by decide
  have hdescent : baseEnd_422836 < baseStart_422836 := by decide
  rcases family_descends (prefixWord ++ tailWord_422836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422854 : List Nat := [6, 1, 3, 1, 2, 1, 2, 2, 5]
def baseStart_422854 : Nat := 118140960795 + 422854 * 2 ^ 59
def prefixEnd_422854 : Nat := 4983230072969 + 3 ^ 40 * 422854 * 2
def baseEnd_422854 : Nat := 24125260964043757275593

theorem tailTrace_422854 : CollatzResearch.WordTrace tailWord_422854 prefixEnd_422854 24125260964043757275593 := by
  unfold tailWord_422854
  simp only [CollatzResearch.WordTrace]
  refine ⟨481961012814989079961363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10281834940053100372509077 481961012814989079961363)
  ·
    refine ⟨722941519222483619942045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 481961012814989079961363 722941519222483619942045)
    ·
      refine ⟨271103069708431357478267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 722941519222483619942045 271103069708431357478267)
      ·
        refine ⟨406654604562647036217401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271103069708431357478267 406654604562647036217401)
        ·
          refine ⟨304990953421985277163051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406654604562647036217401 304990953421985277163051)
          ·
            refine ⟨457486430132977915744577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304990953421985277163051 457486430132977915744577)
            ·
              refine ⟨343114822599733436808433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457486430132977915744577 343114822599733436808433)
              ·
                refine ⟨257336116949800077606325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 343114822599733436808433 257336116949800077606325)
                ·
                  refine ⟨24125260964043757275593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 257336116949800077606325 24125260964043757275593)
                  ·
                    rfl

theorem cell23_422854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_422854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422854 prefixEnd_422854 := by exact prefixLift 422854
  have htrace : WordTrace (prefixWord ++ tailWord_422854) baseStart_422854 baseEnd_422854 := by
    simpa [prefixWord, tailWord_422854, baseEnd_422854] using wordTrace_append hprefix tailTrace_422854
  have hstable : (prefixWord ++ tailWord_422854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422854).length < 2 ^ (prefixWord ++ tailWord_422854).sum := by decide
  have hdescent : baseEnd_422854 < baseStart_422854 := by decide
  rcases family_descends (prefixWord ++ tailWord_422854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422909 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 7, 2, 2]
def baseStart_422909 : Nat := 118140960795 + 422909 * 2 ^ 59
def prefixEnd_422909 : Nat := 4983230072969 + 3 ^ 40 * 422909 * 2
def baseEnd_422909 : Nat := 217155590112391100292583

theorem tailTrace_422909 : CollatzResearch.WordTrace tailWord_422909 prefixEnd_422909 217155590112391100292583 := by
  unfold tailWord_422909
  simp only [CollatzResearch.WordTrace]
  refine ⟨15424758424880394952015781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10283172283253596634677187 15424758424880394952015781)
  ·
    refine ⟨2892142204665074053502959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15424758424880394952015781 2892142204665074053502959)
    ·
      refine ⟨4338213306997611080254439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2892142204665074053502959 4338213306997611080254439)
      ·
        refine ⟨6507319960496416620381659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4338213306997611080254439 6507319960496416620381659)
        ·
          refine ⟨9760979940744624930572489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6507319960496416620381659 9760979940744624930572489)
          ·
            refine ⟨7320734955558468697929367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9760979940744624930572489 7320734955558468697929367)
            ·
              refine ⟨10981102433337703046894051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7320734955558468697929367 10981102433337703046894051)
              ·
                refine ⟨16471653650006554570341077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10981102433337703046894051 16471653650006554570341077)
                ·
                  refine ⟨386054382422028622742369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16471653650006554570341077 386054382422028622742369)
                  ·
                    refine ⟨289540786816521467056777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 386054382422028622742369 289540786816521467056777)
                    ·
                      refine ⟨217155590112391100292583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 289540786816521467056777 217155590112391100292583)
                      ·
                        rfl

theorem cell23_422909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 2, 2].length) (baseStart_422909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422909 prefixEnd_422909 := by exact prefixLift 422909
  have htrace : WordTrace (prefixWord ++ tailWord_422909) baseStart_422909 baseEnd_422909 := by
    simpa [prefixWord, tailWord_422909, baseEnd_422909] using wordTrace_append hprefix tailTrace_422909
  have hstable : (prefixWord ++ tailWord_422909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422909).length < 2 ^ (prefixWord ++ tailWord_422909).sum := by decide
  have hdescent : baseEnd_422909 < baseStart_422909 := by decide
  rcases family_descends (prefixWord ++ tailWord_422909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422926 : List Nat := [4, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2]
def baseStart_422926 : Nat := 118140960795 + 422926 * 2 ^ 59
def prefixEnd_422926 : Nat := 4983230072969 + 3 ^ 40 * 422926 * 2
def baseEnd_422926 : Nat := 217164319283517533780005

theorem tailTrace_422926 : CollatzResearch.WordTrace tailWord_422926 prefixEnd_422926 217164319283517533780005 := by
  unfold tailWord_422926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1928172308227350856923079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10283585643879204570256421 1928172308227350856923079)
  ·
    refine ⟨2892258462341026285384619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1928172308227350856923079 2892258462341026285384619)
    ·
      refine ⟨4338387693511539428076929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2892258462341026285384619 4338387693511539428076929)
      ·
        refine ⟨3253790770133654571057697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4338387693511539428076929 3253790770133654571057697)
        ·
          refine ⟨2440343077600240928293273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3253790770133654571057697 2440343077600240928293273)
          ·
            refine ⟨1830257308200180696219955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2440343077600240928293273 1830257308200180696219955)
            ·
              refine ⟨2745385962300271044329933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1830257308200180696219955 2745385962300271044329933)
              ·
                refine ⟨1029519735862601641623725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2745385962300271044329933 1029519735862601641623725)
                ·
                  refine ⟨386069900948475615608897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1029519735862601641623725 386069900948475615608897)
                  ·
                    refine ⟨289552425711356711706673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 386069900948475615608897 289552425711356711706673)
                    ·
                      refine ⟨217164319283517533780005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 289552425711356711706673 217164319283517533780005)
                      ·
                        rfl

theorem cell23_422926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_422926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422926 prefixEnd_422926 := by exact prefixLift 422926
  have htrace : WordTrace (prefixWord ++ tailWord_422926) baseStart_422926 baseEnd_422926 := by
    simpa [prefixWord, tailWord_422926, baseEnd_422926] using wordTrace_append hprefix tailTrace_422926
  have hstable : (prefixWord ++ tailWord_422926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422926).length < 2 ^ (prefixWord ++ tailWord_422926).sum := by decide
  have hdescent : baseEnd_422926 < baseStart_422926 := by decide
  rcases family_descends (prefixWord ++ tailWord_422926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422936 : List Nat := [2, 1, 2, 3, 2, 3, 3, 1, 2, 4]
def baseStart_422936 : Nat := 118140960795 + 422936 * 2 ^ 59
def prefixEnd_422936 : Nat := 4983230072969 + 3 ^ 40 * 422936 * 2
def baseEnd_422936 : Nat := 72389818030020831551653

theorem tailTrace_422936 : CollatzResearch.WordTrace tailWord_422936 prefixEnd_422936 72389818030020831551653 := by
  unfold tailWord_422936
  simp only [CollatzResearch.WordTrace]
  refine ⟨7712871597891289281624331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10283828797188385708832441 7712871597891289281624331)
  ·
    refine ⟨11569307396836933922436497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7712871597891289281624331 11569307396836933922436497)
    ·
      refine ⟨8676980547627700441827373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11569307396836933922436497 8676980547627700441827373)
      ·
        refine ⟨3253867705360387665685265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8676980547627700441827373 3253867705360387665685265)
        ·
          refine ⟨2440400779020290749263949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3253867705360387665685265 2440400779020290749263949)
          ·
            refine ⟨915150292132609030973981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2440400779020290749263949 915150292132609030973981)
            ·
              refine ⟨343181359549728386615243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 915150292132609030973981 343181359549728386615243)
              ·
                refine ⟨514772039324592579922865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343181359549728386615243 514772039324592579922865)
                ·
                  refine ⟨386079029493444434942149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 514772039324592579922865 386079029493444434942149)
                  ·
                    refine ⟨72389818030020831551653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 386079029493444434942149 72389818030020831551653)
                    ·
                      rfl

theorem cell23_422936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 2, 4].length) (baseStart_422936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422936 prefixEnd_422936 := by exact prefixLift 422936
  have htrace : WordTrace (prefixWord ++ tailWord_422936) baseStart_422936 baseEnd_422936 := by
    simpa [prefixWord, tailWord_422936, baseEnd_422936] using wordTrace_append hprefix tailTrace_422936
  have hstable : (prefixWord ++ tailWord_422936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422936).length < 2 ^ (prefixWord ++ tailWord_422936).sum := by decide
  have hdescent : baseEnd_422936 < baseStart_422936 := by decide
  rcases family_descends (prefixWord ++ tailWord_422936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422946 : List Nat := [3, 3, 1, 1, 1, 4, 2, 2, 1, 2, 3]
def baseStart_422946 : Nat := 118140960795 + 422946 * 2 ^ 59
def prefixEnd_422946 : Nat := 4983230072969 + 3 ^ 40 * 422946 * 2
def baseEnd_422946 : Nat := 217174588896607455529913

theorem tailTrace_422946 : CollatzResearch.WordTrace tailWord_422946 prefixEnd_422946 217174588896607455529913 := by
  unfold tailWord_422946
  simp only [CollatzResearch.WordTrace]
  refine ⟨3856526981436587567778173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10284071950497566847408461 3856526981436587567778173)
  ·
    refine ⟨1446197618038720337916815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3856526981436587567778173 1446197618038720337916815)
    ·
      refine ⟨2169296427058080506875223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1446197618038720337916815 2169296427058080506875223)
      ·
        refine ⟨3253944640587120760312835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2169296427058080506875223 3253944640587120760312835)
        ·
          refine ⟨4880916960880681140469253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3253944640587120760312835 4880916960880681140469253)
          ·
            refine ⟨915171930165127713837985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4880916960880681140469253 915171930165127713837985)
            ·
              refine ⟨686378947623845785378489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 915171930165127713837985 686378947623845785378489)
              ·
                refine ⟨514784210717884339033867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 686378947623845785378489 514784210717884339033867)
                ·
                  refine ⟨772176316076826508550801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 514784210717884339033867 772176316076826508550801)
                  ·
                    refine ⟨579132237057619881413101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 772176316076826508550801 579132237057619881413101)
                    ·
                      refine ⟨217174588896607455529913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 579132237057619881413101 217174588896607455529913)
                      ·
                        rfl

theorem cell23_422946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_422946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422946 prefixEnd_422946 := by exact prefixLift 422946
  have htrace : WordTrace (prefixWord ++ tailWord_422946) baseStart_422946 baseEnd_422946 := by
    simpa [prefixWord, tailWord_422946, baseEnd_422946] using wordTrace_append hprefix tailTrace_422946
  have hstable : (prefixWord ++ tailWord_422946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422946).length < 2 ^ (prefixWord ++ tailWord_422946).sum := by decide
  have hdescent : baseEnd_422946 < baseStart_422946 := by decide
  rcases family_descends (prefixWord ++ tailWord_422946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422955 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 5]
def baseStart_422955 : Nat := 118140960795 + 422955 * 2 ^ 59
def prefixEnd_422955 : Nat := 4983230072969 + 3 ^ 40 * 422955 * 2
def baseEnd_422955 : Nat := 217179210222497920317371

theorem tailTrace_422955 : CollatzResearch.WordTrace tailWord_422955 prefixEnd_422955 217179210222497920317371 := by
  unfold tailWord_422955
  simp only [CollatzResearch.WordTrace]
  refine ⟨15426436182713744808190319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10284290788475829872126879 15426436182713744808190319)
  ·
    refine ⟨23139654274070617212285479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15426436182713744808190319 23139654274070617212285479)
    ·
      refine ⟨34709481411105925818428219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23139654274070617212285479 34709481411105925818428219)
      ·
        refine ⟨52064222116658888727642329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34709481411105925818428219 52064222116658888727642329)
        ·
          refine ⟨39048166587494166545731747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52064222116658888727642329 39048166587494166545731747)
          ·
            refine ⟨58572249881241249818597621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39048166587494166545731747 58572249881241249818597621)
            ·
              refine ⟨5491148426366367170493527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58572249881241249818597621 5491148426366367170493527)
              ·
                refine ⟨8236722639549550755740291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5491148426366367170493527 8236722639549550755740291)
                ·
                  refine ⟨12355083959324326133610437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8236722639549550755740291 12355083959324326133610437)
                  ·
                    refine ⟨2316578242373311150051957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12355083959324326133610437 2316578242373311150051957)
                    ·
                      refine ⟨217179210222497920317371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2316578242373311150051957 217179210222497920317371)
                      ·
                        rfl

theorem cell23_422955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 5].length) (baseStart_422955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422955 prefixEnd_422955 := by exact prefixLift 422955
  have htrace : WordTrace (prefixWord ++ tailWord_422955) baseStart_422955 baseEnd_422955 := by
    simpa [prefixWord, tailWord_422955, baseEnd_422955] using wordTrace_append hprefix tailTrace_422955
  have hstable : (prefixWord ++ tailWord_422955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422955).length < 2 ^ (prefixWord ++ tailWord_422955).sum := by decide
  have hdescent : baseEnd_422955 < baseStart_422955 := by decide
  rcases family_descends (prefixWord ++ tailWord_422955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422977 : List Nat := [1, 2, 5, 1, 3, 1, 3, 2, 1, 2, 2]
def baseStart_422977 : Nat := 118140960795 + 422977 * 2 ^ 59
def prefixEnd_422977 : Nat := 4983230072969 + 3 ^ 40 * 422977 * 2
def baseEnd_422977 : Nat := 217190506796896834242271

theorem tailTrace_422977 : CollatzResearch.WordTrace tailWord_422977 prefixEnd_422977 217190506796896834242271 := by
  unfold tailWord_422977
  simp only [CollatzResearch.WordTrace]
  refine ⟨15427238588634042565491185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10284825725756028376994123 15427238588634042565491185)
  ·
    refine ⟨11570428941475531924118389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15427238588634042565491185 11570428941475531924118389)
    ·
      refine ⟨1084727713263331117886099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11570428941475531924118389 1084727713263331117886099)
      ·
        refine ⟨1627091569894996676829149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1084727713263331117886099 1627091569894996676829149)
        ·
          refine ⟨610159338710623753810931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1627091569894996676829149 610159338710623753810931)
          ·
            refine ⟨915239008065935630716397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610159338710623753810931 915239008065935630716397)
            ·
              refine ⟨343214628024725861518649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 915239008065935630716397 343214628024725861518649)
              ·
                refine ⟨257410971018544396138987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 343214628024725861518649 257410971018544396138987)
                ·
                  refine ⟨386116456527816594208481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257410971018544396138987 386116456527816594208481)
                  ·
                    refine ⟨289587342395862445656361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 386116456527816594208481 289587342395862445656361)
                    ·
                      refine ⟨217190506796896834242271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 289587342395862445656361 217190506796896834242271)
                      ·
                        rfl

theorem cell23_422977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_422977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422977 prefixEnd_422977 := by exact prefixLift 422977
  have htrace : WordTrace (prefixWord ++ tailWord_422977) baseStart_422977 baseEnd_422977 := by
    simpa [prefixWord, tailWord_422977, baseEnd_422977] using wordTrace_append hprefix tailTrace_422977
  have hstable : (prefixWord ++ tailWord_422977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422977).length < 2 ^ (prefixWord ++ tailWord_422977).sum := by decide
  have hdescent : baseEnd_422977 < baseStart_422977 := by decide
  rcases family_descends (prefixWord ++ tailWord_422977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422999 : List Nat := [1, 1, 3, 2, 2, 1, 1, 5, 1, 4, 2]
def baseStart_422999 : Nat := 118140960795 + 422999 * 2 ^ 59
def prefixEnd_422999 : Nat := 4983230072969 + 3 ^ 40 * 422999 * 2
def baseEnd_422999 : Nat := 217201803371295748167169

theorem tailTrace_422999 : CollatzResearch.WordTrace tailWord_422999 prefixEnd_422999 217201803371295748167169 := by
  unfold tailWord_422999
  simp only [CollatzResearch.WordTrace]
  refine ⟨15428040994554340322792051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10285360663036226881861367 15428040994554340322792051)
  ·
    refine ⟨23142061491831510484188077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15428040994554340322792051 23142061491831510484188077)
    ·
      refine ⟨8678273059436816431570529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23142061491831510484188077 8678273059436816431570529)
      ·
        refine ⟨6508704794577612323677897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8678273059436816431570529 6508704794577612323677897)
        ·
          refine ⟨4881528595933209242758423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6508704794577612323677897 4881528595933209242758423)
          ·
            refine ⟨7322292893899813864137635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4881528595933209242758423 7322292893899813864137635)
            ·
              refine ⟨10983439340849720796206453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7322292893899813864137635 10983439340849720796206453)
              ·
                refine ⟨1029697438204661324644355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10983439340849720796206453 1029697438204661324644355)
                ·
                  refine ⟨1544546157306991986966533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029697438204661324644355 1544546157306991986966533)
                  ·
                    refine ⟨289602404495060997556225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1544546157306991986966533 289602404495060997556225)
                    ·
                      refine ⟨217201803371295748167169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 289602404495060997556225 217201803371295748167169)
                      ·
                        rfl

theorem cell23_422999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 4, 2].length) (baseStart_422999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422999 prefixEnd_422999 := by exact prefixLift 422999
  have htrace : WordTrace (prefixWord ++ tailWord_422999) baseStart_422999 baseEnd_422999 := by
    simpa [prefixWord, tailWord_422999, baseEnd_422999] using wordTrace_append hprefix tailTrace_422999
  have hstable : (prefixWord ++ tailWord_422999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422999).length < 2 ^ (prefixWord ++ tailWord_422999).sum := by decide
  have hdescent : baseEnd_422999 < baseStart_422999 := by decide
  rcases family_descends (prefixWord ++ tailWord_422999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423002 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3]
def baseStart_423002 : Nat := 118140960795 + 423002 * 2 ^ 59
def prefixEnd_423002 : Nat := 4983230072969 + 3 ^ 40 * 423002 * 2
def baseEnd_423002 : Nat := 217203343813259236429655

theorem tailTrace_423002 : CollatzResearch.WordTrace tailWord_423002 prefixEnd_423002 217203343813259236429655 := by
  unfold tailWord_423002
  simp only [CollatzResearch.WordTrace]
  refine ⟨3857037603385867958787815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10285433609028981223434173 3857037603385867958787815)
  ·
    refine ⟨5785556405078801938181723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3857037603385867958787815 5785556405078801938181723)
    ·
      refine ⟨8678334607618202907272585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5785556405078801938181723 8678334607618202907272585)
      ·
        refine ⟨6508750955713652180454439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8678334607618202907272585 6508750955713652180454439)
        ·
          refine ⟨9763126433570478270681659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6508750955713652180454439 9763126433570478270681659)
          ·
            refine ⟨14644689650355717406022489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9763126433570478270681659 14644689650355717406022489)
            ·
              refine ⟨10983517237766788054516867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14644689650355717406022489 10983517237766788054516867)
              ·
                refine ⟨16475275856650182081775301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10983517237766788054516867 16475275856650182081775301)
                ·
                  refine ⟨3089114223121909140332869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16475275856650182081775301 3089114223121909140332869)
                  ·
                    refine ⟨579208916835357963812413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3089114223121909140332869 579208916835357963812413)
                    ·
                      refine ⟨217203343813259236429655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 579208916835357963812413 217203343813259236429655)
                      ·
                        rfl

theorem cell23_423002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_423002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423002 prefixEnd_423002 := by exact prefixLift 423002
  have htrace : WordTrace (prefixWord ++ tailWord_423002) baseStart_423002 baseEnd_423002 := by
    simpa [prefixWord, tailWord_423002, baseEnd_423002] using wordTrace_append hprefix tailTrace_423002
  have hstable : (prefixWord ++ tailWord_423002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423002).length < 2 ^ (prefixWord ++ tailWord_423002).sum := by decide
  have hdescent : baseEnd_423002 < baseStart_423002 := by decide
  rcases family_descends (prefixWord ++ tailWord_423002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423012 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 4, 2, 4]
def baseStart_423012 : Nat := 118140960795 + 423012 * 2 ^ 59
def prefixEnd_423012 : Nat := 4983230072969 + 3 ^ 40 * 423012 * 2
def baseEnd_423012 : Nat := 217208478619804197304609

theorem tailTrace_423012 : CollatzResearch.WordTrace tailWord_423012 prefixEnd_423012 217208478619804197304609 := by
  unfold tailWord_423012
  simp only [CollatzResearch.WordTrace]
  refine ⟨7714257571753621771507645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10285676762338162362010193 7714257571753621771507645)
  ·
    refine ⟨2892846589407608164315367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7714257571753621771507645 2892846589407608164315367)
    ·
      refine ⟨4339269884111412246473051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2892846589407608164315367 4339269884111412246473051)
      ·
        refine ⟨6508904826167118369709577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4339269884111412246473051 6508904826167118369709577)
        ·
          refine ⟨4881678619625338777282183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6508904826167118369709577 4881678619625338777282183)
          ·
            refine ⟨7322517929438008165923275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4881678619625338777282183 7322517929438008165923275)
            ·
              refine ⟨10983776894157012248884913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7322517929438008165923275 10983776894157012248884913)
              ·
                refine ⟨8237832670617759186663685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10983776894157012248884913 8237832670617759186663685)
                ·
                  refine ⟨1544593625740829847499441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8237832670617759186663685 1544593625740829847499441)
                  ·
                    refine ⟨1158445219305622385624581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1544593625740829847499441 1158445219305622385624581)
                    ·
                      refine ⟨217208478619804197304609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1158445219305622385624581 217208478619804197304609)
                      ·
                        rfl

theorem cell23_423012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_423012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423012 prefixEnd_423012 := by exact prefixLift 423012
  have htrace : WordTrace (prefixWord ++ tailWord_423012) baseStart_423012 baseEnd_423012 := by
    simpa [prefixWord, tailWord_423012, baseEnd_423012] using wordTrace_append hprefix tailTrace_423012
  have hstable : (prefixWord ++ tailWord_423012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423012).length < 2 ^ (prefixWord ++ tailWord_423012).sum := by decide
  have hdescent : baseEnd_423012 < baseStart_423012 := by decide
  rcases family_descends (prefixWord ++ tailWord_423012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423049 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 2, 3, 3]
def baseStart_423049 : Nat := 118140960795 + 423049 * 2 ^ 59
def prefixEnd_423049 : Nat := 4983230072969 + 3 ^ 40 * 423049 * 2
def baseEnd_423049 : Nat := 217227477404020552541939

theorem tailTrace_423049 : CollatzResearch.WordTrace tailWord_423049 prefixEnd_423049 217227477404020552541939 := by
  unfold tailWord_423049
  simp only [CollatzResearch.WordTrace]
  refine ⟨15429864644373198862112201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10286576429582132574741467 15429864644373198862112201)
  ·
    refine ⟨11572398483279899146584151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15429864644373198862112201 11572398483279899146584151)
    ·
      refine ⟨17358597724919848719876227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11572398483279899146584151 17358597724919848719876227)
      ·
        refine ⟨26037896587379773079814341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17358597724919848719876227 26037896587379773079814341)
        ·
          refine ⟨4882105610133707452465189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26037896587379773079814341 4882105610133707452465189)
          ·
            refine ⟨915394801900070147337223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4882105610133707452465189 915394801900070147337223)
            ·
              refine ⟨1373092202850105221005835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915394801900070147337223 1373092202850105221005835)
              ·
                refine ⟨2059638304275157831508753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373092202850105221005835 2059638304275157831508753)
                ·
                  refine ⟨1544728728206368373631565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2059638304275157831508753 1544728728206368373631565)
                  ·
                    refine ⟨579273273077388140111837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1544728728206368373631565 579273273077388140111837)
                    ·
                      refine ⟨217227477404020552541939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 579273273077388140111837 217227477404020552541939)
                      ·
                        rfl

theorem cell23_423049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 3, 3].length) (baseStart_423049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423049 prefixEnd_423049 := by exact prefixLift 423049
  have htrace : WordTrace (prefixWord ++ tailWord_423049) baseStart_423049 baseEnd_423049 := by
    simpa [prefixWord, tailWord_423049, baseEnd_423049] using wordTrace_append hprefix tailTrace_423049
  have hstable : (prefixWord ++ tailWord_423049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423049).length < 2 ^ (prefixWord ++ tailWord_423049).sum := by decide
  have hdescent : baseEnd_423049 < baseStart_423049 := by decide
  rcases family_descends (prefixWord ++ tailWord_423049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423052 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 4, 5]
def baseStart_423052 : Nat := 118140960795 + 423052 * 2 ^ 59
def prefixEnd_423052 : Nat := 4983230072969 + 3 ^ 40 * 423052 * 2
def baseEnd_423052 : Nat := 72409672615328013601475

theorem tailTrace_423052 : CollatzResearch.WordTrace tailWord_423052 prefixEnd_423052 72409672615328013601475 := by
  unfold tailWord_423052
  simp only [CollatzResearch.WordTrace]
  refine ⟨7714987031681165187235705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10286649375574886916314273 7714987031681165187235705)
  ·
    refine ⟨5786240273760873890426779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7714987031681165187235705 5786240273760873890426779)
    ·
      refine ⟨8679360410641310835640169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5786240273760873890426779 8679360410641310835640169)
      ·
        refine ⟨6509520307980983126730127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8679360410641310835640169 6509520307980983126730127)
        ·
          refine ⟨9764280461971474690095191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6509520307980983126730127 9764280461971474690095191)
          ·
            refine ⟨14646420692957212035142787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9764280461971474690095191 14646420692957212035142787)
            ·
              refine ⟨21969631039435818052714181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14646420692957212035142787 21969631039435818052714181)
              ·
                refine ⟨4119305819894215884883909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21969631039435818052714181 4119305819894215884883909)
                ·
                  refine ⟨772369841230165478415733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4119305819894215884883909 772369841230165478415733)
                  ·
                    refine ⟨72409672615328013601475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 772369841230165478415733 72409672615328013601475)
                    ·
                      rfl

theorem cell23_423052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_423052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423052 prefixEnd_423052 := by exact prefixLift 423052
  have htrace : WordTrace (prefixWord ++ tailWord_423052) baseStart_423052 baseEnd_423052 := by
    simpa [prefixWord, tailWord_423052, baseEnd_423052] using wordTrace_append hprefix tailTrace_423052
  have hstable : (prefixWord ++ tailWord_423052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423052).length < 2 ^ (prefixWord ++ tailWord_423052).sum := by decide
  have hdescent : baseEnd_423052 < baseStart_423052 := by decide
  rcases family_descends (prefixWord ++ tailWord_423052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423143 : List Nat := [1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 3]
def baseStart_423143 : Nat := 118140960795 + 423143 * 2 ^ 59
def prefixEnd_423143 : Nat := 4983230072969 + 3 ^ 40 * 423143 * 2
def baseEnd_423143 : Nat := 217275744585543184766507

theorem tailTrace_423143 : CollatzResearch.WordTrace tailWord_423143 prefixEnd_423143 217275744585543184766507 := by
  unfold tailWord_423143
  simp only [CollatzResearch.WordTrace]
  refine ⟨15433293106032652916034083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10288862070688435277356055 15433293106032652916034083)
  ·
    refine ⟨23149939659048979374051125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15433293106032652916034083 23149939659048979374051125)
    ·
      refine ⟨2170306843035841816317293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23149939659048979374051125 2170306843035841816317293)
      ·
        refine ⟨813865066138440681118985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2170306843035841816317293 813865066138440681118985)
        ·
          refine ⟨610398799603830510839239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 813865066138440681118985 610398799603830510839239)
          ·
            refine ⟨915598199405745766258859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610398799603830510839239 915598199405745766258859)
            ·
              refine ⟨1373397299108618649388289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915598199405745766258859 1373397299108618649388289)
              ·
                refine ⟨1030047974331463987041217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1373397299108618649388289 1030047974331463987041217)
                ·
                  refine ⟨772535980748597990280913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1030047974331463987041217 772535980748597990280913)
                  ·
                    refine ⟨579401985561448492710685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 772535980748597990280913 579401985561448492710685)
                    ·
                      refine ⟨217275744585543184766507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 579401985561448492710685 217275744585543184766507)
                      ·
                        rfl

theorem cell23_423143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_423143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423143 prefixEnd_423143 := by exact prefixLift 423143
  have htrace : WordTrace (prefixWord ++ tailWord_423143) baseStart_423143 baseEnd_423143 := by
    simpa [prefixWord, tailWord_423143, baseEnd_423143] using wordTrace_append hprefix tailTrace_423143
  have hstable : (prefixWord ++ tailWord_423143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423143).length < 2 ^ (prefixWord ++ tailWord_423143).sum := by decide
  have hdescent : baseEnd_423143 < baseStart_423143 := by decide
  rcases family_descends (prefixWord ++ tailWord_423143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423152 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 7]
def baseStart_423152 : Nat := 118140960795 + 423152 * 2 ^ 59
def prefixEnd_423152 : Nat := 4983230072969 + 3 ^ 40 * 423152 * 2
def baseEnd_423152 : Nat := 217280365911433649553965

theorem tailTrace_423152 : CollatzResearch.WordTrace tailWord_423152 prefixEnd_423152 217280365911433649553965 := by
  unfold tailWord_423152
  simp only [CollatzResearch.WordTrace]
  refine ⟨7716810681500023726555855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10289080908666698302074473 7716810681500023726555855)
  ·
    refine ⟨11575216022250035589833783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7716810681500023726555855 11575216022250035589833783)
    ·
      refine ⟨17362824033375053384750675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11575216022250035589833783 17362824033375053384750675)
      ·
        refine ⟨26044236050062580077126013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17362824033375053384750675 26044236050062580077126013)
        ·
          refine ⟨9766588518773467528922255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26044236050062580077126013 9766588518773467528922255)
          ·
            refine ⟨14649882778160201293383383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9766588518773467528922255 14649882778160201293383383)
            ·
              refine ⟨21974824167240301940075075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14649882778160201293383383 21974824167240301940075075)
              ·
                refine ⟨32962236250860452910112613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21974824167240301940075075 32962236250860452910112613)
                ·
                  refine ⟨6180419297036334920646115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32962236250860452910112613 6180419297036334920646115)
                  ·
                    refine ⟨9270628945554502380969173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6180419297036334920646115 9270628945554502380969173)
                    ·
                      refine ⟨217280365911433649553965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9270628945554502380969173 217280365911433649553965)
                      ·
                        rfl

theorem cell23_423152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_423152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423152 prefixEnd_423152 := by exact prefixLift 423152
  have htrace : WordTrace (prefixWord ++ tailWord_423152) baseStart_423152 baseEnd_423152 := by
    simpa [prefixWord, tailWord_423152, baseEnd_423152] using wordTrace_append hprefix tailTrace_423152
  have hstable : (prefixWord ++ tailWord_423152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423152).length < 2 ^ (prefixWord ++ tailWord_423152).sum := by decide
  have hdescent : baseEnd_423152 < baseStart_423152 := by decide
  rcases family_descends (prefixWord ++ tailWord_423152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423176 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 3, 5]
def baseStart_423176 : Nat := 118140960795 + 423176 * 2 ^ 59
def prefixEnd_423176 : Nat := 4983230072969 + 3 ^ 40 * 423176 * 2
def baseEnd_423176 : Nat := 72430896482380518551285

theorem tailTrace_423176 : CollatzResearch.WordTrace tailWord_423176 prefixEnd_423176 72430896482380518551285 := by
  unfold tailWord_423176
  simp only [CollatzResearch.WordTrace]
  refine ⟨7717248357456549775992691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10289664476608733034656921 7717248357456549775992691)
  ·
    refine ⟨11575872536184824663989037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7717248357456549775992691 11575872536184824663989037)
    ·
      refine ⟨4340952201069309248995889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11575872536184824663989037 4340952201069309248995889)
      ·
        refine ⟨3255714150801981936746917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4340952201069309248995889 3255714150801981936746917)
        ·
          refine ⟨610446403275371613140047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3255714150801981936746917 610446403275371613140047)
          ·
            refine ⟨915669604913057419710071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610446403275371613140047 915669604913057419710071)
            ·
              refine ⟨1373504407369586129565107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915669604913057419710071 1373504407369586129565107)
              ·
                refine ⟨2060256611054379194347661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373504407369586129565107 2060256611054379194347661)
                ·
                  refine ⟨772596229145392197880373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2060256611054379194347661 772596229145392197880373)
                  ·
                    refine ⟨72430896482380518551285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 772596229145392197880373 72430896482380518551285)
                    ·
                      rfl

theorem cell23_423176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_423176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423176 prefixEnd_423176 := by exact prefixLift 423176
  have htrace : WordTrace (prefixWord ++ tailWord_423176) baseStart_423176 baseEnd_423176 := by
    simpa [prefixWord, tailWord_423176, baseEnd_423176] using wordTrace_append hprefix tailTrace_423176
  have hstable : (prefixWord ++ tailWord_423176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423176).length < 2 ^ (prefixWord ++ tailWord_423176).sum := by decide
  have hdescent : baseEnd_423176 < baseStart_423176 := by decide
  rcases family_descends (prefixWord ++ tailWord_423176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423196 : List Nat := [2, 2, 3, 1, 1, 1, 2, 5, 1, 1, 4]
def baseStart_423196 : Nat := 118140960795 + 423196 * 2 ^ 59
def prefixEnd_423196 : Nat := 4983230072969 + 3 ^ 40 * 423196 * 2
def baseEnd_423196 : Nat := 217302959060231477403763

theorem tailTrace_423196 : CollatzResearch.WordTrace tailWord_423196 prefixEnd_423196 217302959060231477403763 := by
  unfold tailWord_423196
  simp only [CollatzResearch.WordTrace]
  refine ⟨7717613087420321483856721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10290150783227095311808961 7717613087420321483856721)
  ·
    refine ⟨5788209815565241112892541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7717613087420321483856721 5788209815565241112892541)
    ·
      refine ⟨2170578680836965417334703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5788209815565241112892541 2170578680836965417334703)
      ·
        refine ⟨3255868021255448126002055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2170578680836965417334703 3255868021255448126002055)
        ·
          refine ⟨4883802031883172189003083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3255868021255448126002055 4883802031883172189003083)
          ·
            refine ⟨7325703047824758283504625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4883802031883172189003083 7325703047824758283504625)
            ·
              refine ⟨5494277285868568712628469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7325703047824758283504625 5494277285868568712628469)
              ·
                refine ⟨515088495550178316808919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5494277285868568712628469 515088495550178316808919)
                ·
                  refine ⟨772632743325267475213379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 515088495550178316808919 772632743325267475213379)
                  ·
                    refine ⟨1158949114987901212820069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 772632743325267475213379 1158949114987901212820069)
                    ·
                      refine ⟨217302959060231477403763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1158949114987901212820069 217302959060231477403763)
                      ·
                        rfl

theorem cell23_423196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_423196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423196 prefixEnd_423196 := by exact prefixLift 423196
  have htrace : WordTrace (prefixWord ++ tailWord_423196) baseStart_423196 baseEnd_423196 := by
    simpa [prefixWord, tailWord_423196, baseEnd_423196] using wordTrace_append hprefix tailTrace_423196
  have hstable : (prefixWord ++ tailWord_423196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423196).length < 2 ^ (prefixWord ++ tailWord_423196).sum := by decide
  have hdescent : baseEnd_423196 < baseStart_423196 := by decide
  rcases family_descends (prefixWord ++ tailWord_423196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423213 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_423213 : Nat := 118140960795 + 423213 * 2 ^ 59
def prefixEnd_423213 : Nat := 4983230072969 + 3 ^ 40 * 423213 * 2
def baseEnd_423213 : Nat := 217311688231357910891185

theorem tailTrace_423213 : CollatzResearch.WordTrace tailWord_423213 prefixEnd_423213 217311688231357910891185 := by
  unfold tailWord_423213
  simp only [CollatzResearch.WordTrace]
  refine ⟨15435846215779054871082293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10290564143852703247388195 15435846215779054871082293)
  ·
    refine ⟨1447110582729286394163965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15435846215779054871082293 1447110582729286394163965)
    ·
      refine ⟨542666468523482397811487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1447110582729286394163965 542666468523482397811487)
      ·
        refine ⟨813999702785223596717231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542666468523482397811487 813999702785223596717231)
        ·
          refine ⟨1220999554177835395075847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813999702785223596717231 1220999554177835395075847)
          ·
            refine ⟨1831499331266753092613771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1220999554177835395075847 1831499331266753092613771)
            ·
              refine ⟨2747248996900129638920657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1831499331266753092613771 2747248996900129638920657)
              ·
                refine ⟨2060436747675097229190493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2747248996900129638920657 2060436747675097229190493)
                ·
                  refine ⟨772663780378161460946435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2060436747675097229190493 772663780378161460946435)
                  ·
                    refine ⟨1158995670567242191419653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 772663780378161460946435 1158995670567242191419653)
                    ·
                      refine ⟨217311688231357910891185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1158995670567242191419653 217311688231357910891185)
                      ·
                        rfl

theorem cell23_423213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_423213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423213 prefixEnd_423213 := by exact prefixLift 423213
  have htrace : WordTrace (prefixWord ++ tailWord_423213) baseStart_423213 baseEnd_423213 := by
    simpa [prefixWord, tailWord_423213, baseEnd_423213] using wordTrace_append hprefix tailTrace_423213
  have hstable : (prefixWord ++ tailWord_423213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423213).length < 2 ^ (prefixWord ++ tailWord_423213).sum := by decide
  have hdescent : baseEnd_423213 < baseStart_423213 := by decide
  rcases family_descends (prefixWord ++ tailWord_423213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423219 : List Nat := [1, 1, 1, 2, 5, 2, 3, 8]
def baseStart_423219 : Nat := 118140960795 + 423219 * 2 ^ 59
def prefixEnd_423219 : Nat := 4983230072969 + 3 ^ 40 * 423219 * 2
def baseEnd_423219 : Nat := 8048695152417958793191

theorem tailTrace_423219 : CollatzResearch.WordTrace tailWord_423219 prefixEnd_423219 8048695152417958793191 := by
  unfold tailWord_423219
  simp only [CollatzResearch.WordTrace]
  refine ⟨15436065053757317895800711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10290710035838211930533807 15436065053757317895800711)
  ·
    refine ⟨23154097580635976843701067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15436065053757317895800711 23154097580635976843701067)
    ·
      refine ⟨34731146370953965265551601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23154097580635976843701067 34731146370953965265551601)
      ·
        refine ⟨26048359778215473949163701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34731146370953965265551601 26048359778215473949163701)
        ·
          refine ⟨2442033729207700682734097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26048359778215473949163701 2442033729207700682734097)
          ·
            refine ⟨1831525296905775512050573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2442033729207700682734097 1831525296905775512050573)
            ·
              refine ⟨686821986339665817018965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1831525296905775512050573 686821986339665817018965)
              ·
                refine ⟨8048695152417958793191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 686821986339665817018965 8048695152417958793191)
                ·
                  rfl

theorem cell23_423219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 8].length) (baseStart_423219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423219 prefixEnd_423219 := by exact prefixLift 423219
  have htrace : WordTrace (prefixWord ++ tailWord_423219) baseStart_423219 baseEnd_423219 := by
    simpa [prefixWord, tailWord_423219, baseEnd_423219] using wordTrace_append hprefix tailTrace_423219
  have hstable : (prefixWord ++ tailWord_423219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423219).length < 2 ^ (prefixWord ++ tailWord_423219).sum := by decide
  have hdescent : baseEnd_423219 < baseStart_423219 := by decide
  rcases family_descends (prefixWord ++ tailWord_423219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423226 : List Nat := [3, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4]
def baseStart_423226 : Nat := 118140960795 + 423226 * 2 ^ 59
def prefixEnd_423226 : Nat := 4983230072969 + 3 ^ 40 * 423226 * 2
def baseEnd_423226 : Nat := 217318363479866360028625

theorem tailTrace_423226 : CollatzResearch.WordTrace tailWord_423226 prefixEnd_423226 217318363479866360028625 := by
  unfold tailWord_423226
  simp only [CollatzResearch.WordTrace]
  refine ⟨3859080091182989522826383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10290880243154638727537021 3859080091182989522826383)
  ·
    refine ⟨5788620136774484284239575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3859080091182989522826383 5788620136774484284239575)
    ·
      refine ⟨8682930205161726426359363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5788620136774484284239575 8682930205161726426359363)
      ·
        refine ⟨13024395307742589639539045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8682930205161726426359363 13024395307742589639539045)
        ·
          refine ⟨2442074120201735557413571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13024395307742589639539045 2442074120201735557413571)
          ·
            refine ⟨3663111180302603336120357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2442074120201735557413571 3663111180302603336120357)
            ·
              refine ⟨686833346306738125522567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3663111180302603336120357 686833346306738125522567)
              ·
                refine ⟨1030250019460107188283851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 686833346306738125522567 1030250019460107188283851)
                ·
                  refine ⟨1545375029190160782425777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1030250019460107188283851 1545375029190160782425777)
                  ·
                    refine ⟨1159031271892620586819333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1545375029190160782425777 1159031271892620586819333)
                    ·
                      refine ⟨217318363479866360028625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1159031271892620586819333 217318363479866360028625)
                      ·
                        rfl

theorem cell23_423226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4].length) (baseStart_423226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423226 prefixEnd_423226 := by exact prefixLift 423226
  have htrace : WordTrace (prefixWord ++ tailWord_423226) baseStart_423226 baseEnd_423226 := by
    simpa [prefixWord, tailWord_423226, baseEnd_423226] using wordTrace_append hprefix tailTrace_423226
  have hstable : (prefixWord ++ tailWord_423226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423226).length < 2 ^ (prefixWord ++ tailWord_423226).sum := by decide
  have hdescent : baseEnd_423226 < baseStart_423226 := by decide
  rcases family_descends (prefixWord ++ tailWord_423226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423230 : List Nat := [4, 2, 1, 2, 1, 1, 3, 2, 3, 2, 2]
def baseStart_423230 : Nat := 118140960795 + 423230 * 2 ^ 59
def prefixEnd_423230 : Nat := 4983230072969 + 3 ^ 40 * 423230 * 2
def baseEnd_423230 : Nat := 217320417402484344378607

theorem tailTrace_423230 : CollatzResearch.WordTrace tailWord_423230 prefixEnd_423230 217320417402484344378607 := by
  unfold tailWord_423230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1929558282089683346806393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10290977504478311182967429 1929558282089683346806393)
  ·
    refine ⟨1447168711567262510104795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1929558282089683346806393 1447168711567262510104795)
    ·
      refine ⟨2170753067350893765157193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1447168711567262510104795 2170753067350893765157193)
      ·
        refine ⟨1628064800513170323867895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2170753067350893765157193 1628064800513170323867895)
        ·
          refine ⟨2442097200769755485801843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1628064800513170323867895 2442097200769755485801843)
          ·
            refine ⟨3663145801154633228702765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2442097200769755485801843 3663145801154633228702765)
            ·
              refine ⟨1373679675432987460763537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3663145801154633228702765 1373679675432987460763537)
              ·
                refine ⟨1030259756574740595572653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1373679675432987460763537 1030259756574740595572653)
                ·
                  refine ⟨386347408715527723339745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1030259756574740595572653 386347408715527723339745)
                  ·
                    refine ⟨289760556536645792504809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 386347408715527723339745 289760556536645792504809)
                    ·
                      refine ⟨217320417402484344378607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 289760556536645792504809 217320417402484344378607)
                      ·
                        rfl

theorem cell23_423230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_423230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423230 prefixEnd_423230 := by exact prefixLift 423230
  have htrace : WordTrace (prefixWord ++ tailWord_423230) baseStart_423230 baseEnd_423230 := by
    simpa [prefixWord, tailWord_423230, baseEnd_423230] using wordTrace_append hprefix tailTrace_423230
  have hstable : (prefixWord ++ tailWord_423230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423230).length < 2 ^ (prefixWord ++ tailWord_423230).sum := by decide
  have hdescent : baseEnd_423230 < baseStart_423230 := by decide
  rcases family_descends (prefixWord ++ tailWord_423230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423233 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_423233 : Nat := 118140960795 + 423233 * 2 ^ 59
def prefixEnd_423233 : Nat := 4983230072969 + 3 ^ 40 * 423233 * 2
def baseEnd_423233 : Nat := 217321957844447832641093

theorem tailTrace_423233 : CollatzResearch.WordTrace tailWord_423233 prefixEnd_423233 217321957844447832641093 := by
  unfold tailWord_423233
  simp only [CollatzResearch.WordTrace]
  refine ⟨15436575675706598286810353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10291050450471065524540235 15436575675706598286810353)
  ·
    refine ⟨11577431756779948715107765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15436575675706598286810353 11577431756779948715107765)
    ·
      refine ⟨1085384227198120192041353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11577431756779948715107765 1085384227198120192041353)
      ·
        refine ⟨814038170398590144031015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1085384227198120192041353 814038170398590144031015)
        ·
          refine ⟨1221057255597885216046523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814038170398590144031015 1221057255597885216046523)
          ·
            refine ⟨1831585883396827824069785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1221057255597885216046523 1831585883396827824069785)
            ·
              refine ⟨1373689412547620868052339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1831585883396827824069785 1373689412547620868052339)
              ·
                refine ⟨2060534118821431302078509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373689412547620868052339 2060534118821431302078509)
                ·
                  refine ⟨772700294558036738279441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2060534118821431302078509 772700294558036738279441)
                  ·
                    refine ⟨579525220918527553709581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 772700294558036738279441 579525220918527553709581)
                    ·
                      refine ⟨217321957844447832641093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 579525220918527553709581 217321957844447832641093)
                      ·
                        rfl

theorem cell23_423233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_423233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423233 prefixEnd_423233 := by exact prefixLift 423233
  have htrace : WordTrace (prefixWord ++ tailWord_423233) baseStart_423233 baseEnd_423233 := by
    simpa [prefixWord, tailWord_423233, baseEnd_423233] using wordTrace_append hprefix tailTrace_423233
  have hstable : (prefixWord ++ tailWord_423233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423233).length < 2 ^ (prefixWord ++ tailWord_423233).sum := by decide
  have hdescent : baseEnd_423233 < baseStart_423233 := by decide
  rcases family_descends (prefixWord ++ tailWord_423233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423246 : List Nat := [4, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3]
def baseStart_423246 : Nat := 118140960795 + 423246 * 2 ^ 59
def prefixEnd_423246 : Nat := 4983230072969 + 3 ^ 40 * 423246 * 2
def baseEnd_423246 : Nat := 217328633092956281778533

theorem tailTrace_423246 : CollatzResearch.WordTrace tailWord_423246 prefixEnd_423246 217328633092956281778533 := by
  unfold tailWord_423246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1929631228082437688379199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10291366549773001004689061 1929631228082437688379199)
  ·
    refine ⟨2894446842123656532568799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1929631228082437688379199 2894446842123656532568799)
    ·
      refine ⟨4341670263185484798853199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2894446842123656532568799 4341670263185484798853199)
      ·
        refine ⟨6512505394778227198279799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4341670263185484798853199 6512505394778227198279799)
        ·
          refine ⟨9768758092167340797419699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6512505394778227198279799 9768758092167340797419699)
          ·
            refine ⟨14653137138251011196129549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9768758092167340797419699 14653137138251011196129549)
            ·
              refine ⟨5494926426844129198548581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14653137138251011196129549 5494926426844129198548581)
              ·
                refine ⟨1030298705033274224727859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5494926426844129198548581 1030298705033274224727859)
                ·
                  refine ⟨1545448057549911337091789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1030298705033274224727859 1545448057549911337091789)
                  ·
                    refine ⟨579543021581216751409421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1545448057549911337091789 579543021581216751409421)
                    ·
                      refine ⟨217328633092956281778533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 579543021581216751409421 217328633092956281778533)
                      ·
                        rfl

theorem cell23_423246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_423246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423246 prefixEnd_423246 := by exact prefixLift 423246
  have htrace : WordTrace (prefixWord ++ tailWord_423246) baseStart_423246 baseEnd_423246 := by
    simpa [prefixWord, tailWord_423246, baseEnd_423246] using wordTrace_append hprefix tailTrace_423246
  have hstable : (prefixWord ++ tailWord_423246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423246).length < 2 ^ (prefixWord ++ tailWord_423246).sum := by decide
  have hdescent : baseEnd_423246 < baseStart_423246 := by decide
  rcases family_descends (prefixWord ++ tailWord_423246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423279 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 2, 6]
def baseStart_423279 : Nat := 118140960795 + 423279 * 2 ^ 59
def prefixEnd_423279 : Nat := 4983230072969 + 3 ^ 40 * 423279 * 2
def baseEnd_423279 : Nat := 72448525984851550888627

theorem tailTrace_423279 : CollatzResearch.WordTrace tailWord_423279 prefixEnd_423279 72448525984851550888627 := by
  unfold tailWord_423279
  simp only [CollatzResearch.WordTrace]
  refine ⟨15438253433539948142984891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10292168955693298761989927 15438253433539948142984891)
  ·
    refine ⟨23157380150309922214477337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15438253433539948142984891 23157380150309922214477337)
    ·
      refine ⟨17368035112732441660858003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23157380150309922214477337 17368035112732441660858003)
      ·
        refine ⟨26052052669098662491287005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17368035112732441660858003 26052052669098662491287005)
        ·
          refine ⟨9769519750911998434232627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26052052669098662491287005 9769519750911998434232627)
          ·
            refine ⟨14654279626367997651348941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9769519750911998434232627 14654279626367997651348941)
            ·
              refine ⟨5495354859887999119255853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14654279626367997651348941 5495354859887999119255853)
              ·
                refine ⟨2060758072457999669720945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5495354859887999119255853 2060758072457999669720945)
                ·
                  refine ⟨1545568554343499752290709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2060758072457999669720945 1545568554343499752290709)
                  ·
                    refine ⟨72448525984851550888627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1545568554343499752290709 72448525984851550888627)
                    ·
                      rfl

theorem cell23_423279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 6].length) (baseStart_423279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423279 prefixEnd_423279 := by exact prefixLift 423279
  have htrace : WordTrace (prefixWord ++ tailWord_423279) baseStart_423279 baseEnd_423279 := by
    simpa [prefixWord, tailWord_423279, baseEnd_423279] using wordTrace_append hprefix tailTrace_423279
  have hstable : (prefixWord ++ tailWord_423279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423279).length < 2 ^ (prefixWord ++ tailWord_423279).sum := by decide
  have hdescent : baseEnd_423279 < baseStart_423279 := by decide
  rcases family_descends (prefixWord ++ tailWord_423279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423280 : List Nat := [2, 1, 1, 1, 4, 2, 5, 1, 2, 1, 3]
def baseStart_423280 : Nat := 118140960795 + 423280 * 2 ^ 59
def prefixEnd_423280 : Nat := 4983230072969 + 3 ^ 40 * 423280 * 2
def baseEnd_423280 : Nat := 217346091435209148753377

theorem tailTrace_423280 : CollatzResearch.WordTrace tailWord_423280 prefixEnd_423280 217346091435209148753377 := by
  unfold tailWord_423280
  simp only [CollatzResearch.WordTrace]
  refine ⟨7719144953268162656885647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10292193271024216875847529 7719144953268162656885647)
  ·
    refine ⟨11578717429902243985328471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7719144953268162656885647 11578717429902243985328471)
    ·
      refine ⟨17368076144853365977992707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11578717429902243985328471 17368076144853365977992707)
      ·
        refine ⟨26052114217280048966989061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17368076144853365977992707 26052114217280048966989061)
        ·
          refine ⟨4884771415740009181310449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26052114217280048966989061 4884771415740009181310449)
          ·
            refine ⟨3663578561805006885982837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4884771415740009181310449 3663578561805006885982837)
            ·
              refine ⟨343460490169219395560891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3663578561805006885982837 343460490169219395560891)
              ·
                refine ⟨515190735253829093341337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343460490169219395560891 515190735253829093341337)
                ·
                  refine ⟨386393051440371820006003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515190735253829093341337 386393051440371820006003)
                  ·
                    refine ⟨579589577160557730009005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 386393051440371820006003 579589577160557730009005)
                    ·
                      refine ⟨217346091435209148753377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 579589577160557730009005 217346091435209148753377)
                      ·
                        rfl

theorem cell23_423280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 2, 1, 3].length) (baseStart_423280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423280 prefixEnd_423280 := by exact prefixLift 423280
  have htrace : WordTrace (prefixWord ++ tailWord_423280) baseStart_423280 baseEnd_423280 := by
    simpa [prefixWord, tailWord_423280, baseEnd_423280] using wordTrace_append hprefix tailTrace_423280
  have hstable : (prefixWord ++ tailWord_423280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423280).length < 2 ^ (prefixWord ++ tailWord_423280).sum := by decide
  have hdescent : baseEnd_423280 < baseStart_423280 := by decide
  rcases family_descends (prefixWord ++ tailWord_423280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423319 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 9]
def baseStart_423319 : Nat := 118140960795 + 423319 * 2 ^ 59
def prefixEnd_423319 : Nat := 4983230072969 + 3 ^ 40 * 423319 * 2
def baseEnd_423319 : Nat := 217366117180734496165697

theorem tailTrace_423319 : CollatzResearch.WordTrace tailWord_423319 prefixEnd_423319 217366117180734496165697 := by
  unfold tailWord_423319
  simp only [CollatzResearch.WordTrace]
  refine ⟨15439712353395034974441011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10293141568930023316294007 15439712353395034974441011)
  ·
    refine ⟨23159568530092552461661517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15439712353395034974441011 23159568530092552461661517)
    ·
      refine ⟨8684838198784707173123069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23159568530092552461661517 8684838198784707173123069)
      ·
        refine ⟨3256814324544265189921151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8684838198784707173123069 3256814324544265189921151)
        ·
          refine ⟨4885221486816397784881727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3256814324544265189921151 4885221486816397784881727)
          ·
            refine ⟨7327832230224596677322591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4885221486816397784881727 7327832230224596677322591)
            ·
              refine ⟨10991748345336895015983887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7327832230224596677322591 10991748345336895015983887)
              ·
                refine ⟨16487622518005342523975831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10991748345336895015983887 16487622518005342523975831)
                ·
                  refine ⟨24731433777008013785963747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16487622518005342523975831 24731433777008013785963747)
                  ·
                    refine ⟨37097150665512020678945621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24731433777008013785963747 37097150665512020678945621)
                    ·
                      refine ⟨217366117180734496165697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 37097150665512020678945621 217366117180734496165697)
                      ·
                        rfl

theorem cell23_423319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_423319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423319 prefixEnd_423319 := by exact prefixLift 423319
  have htrace : WordTrace (prefixWord ++ tailWord_423319) baseStart_423319 baseEnd_423319 := by
    simpa [prefixWord, tailWord_423319, baseEnd_423319] using wordTrace_append hprefix tailTrace_423319
  have hstable : (prefixWord ++ tailWord_423319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423319).length < 2 ^ (prefixWord ++ tailWord_423319).sum := by decide
  have hdescent : baseEnd_423319 < baseStart_423319 := by decide
  rcases family_descends (prefixWord ++ tailWord_423319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423393 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 1, 6, 2]
def baseStart_423393 : Nat := 118140960795 + 423393 * 2 ^ 59
def prefixEnd_423393 : Nat := 4983230072969 + 3 ^ 40 * 423393 * 2
def baseEnd_423393 : Nat := 217404114749167206640357

theorem tailTrace_423393 : CollatzResearch.WordTrace tailWord_423393 prefixEnd_423393 217404114749167206640357 := by
  unfold tailWord_423393
  simp only [CollatzResearch.WordTrace]
  refine ⟨15442411355126945612634833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10294940903417963741756555 15442411355126945612634833)
  ·
    refine ⟨11581808516345209209476125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15442411355126945612634833 11581808516345209209476125)
    ·
      refine ⟨4343178193629453453553547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11581808516345209209476125 4343178193629453453553547)
      ·
        refine ⟨6514767290444180180330321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4343178193629453453553547 6514767290444180180330321)
        ·
          refine ⟨4886075467833135135247741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6514767290444180180330321 4886075467833135135247741)
          ·
            refine ⟨1832278300437425675717903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4886075467833135135247741 1832278300437425675717903)
            ·
              refine ⟨2748417450656138513576855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1832278300437425675717903 2748417450656138513576855)
              ·
                refine ⟨4122626175984207770365283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2748417450656138513576855 4122626175984207770365283)
                ·
                  refine ⟨6183939263976311655547925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4122626175984207770365283 6183939263976311655547925)
                  ·
                    refine ⟨289872152998889608853809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6183939263976311655547925 289872152998889608853809)
                    ·
                      refine ⟨217404114749167206640357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 289872152998889608853809 217404114749167206640357)
                      ·
                        rfl

theorem cell23_423393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 6, 2].length) (baseStart_423393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423393 prefixEnd_423393 := by exact prefixLift 423393
  have htrace : WordTrace (prefixWord ++ tailWord_423393) baseStart_423393 baseEnd_423393 := by
    simpa [prefixWord, tailWord_423393, baseEnd_423393] using wordTrace_append hprefix tailTrace_423393
  have hstable : (prefixWord ++ tailWord_423393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423393).length < 2 ^ (prefixWord ++ tailWord_423393).sum := by decide
  have hdescent : baseEnd_423393 < baseStart_423393 := by decide
  rcases family_descends (prefixWord ++ tailWord_423393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423410 : List Nat := [3, 2, 1, 4, 1, 1, 3, 1, 2, 1, 4]
def baseStart_423410 : Nat := 118140960795 + 423410 * 2 ^ 59
def prefixEnd_423410 : Nat := 4983230072969 + 3 ^ 40 * 423410 * 2
def baseEnd_423410 : Nat := 217412843920293640127779

theorem tailTrace_423410 : CollatzResearch.WordTrace tailWord_423410 prefixEnd_423410 217412843920293640127779 := by
  unfold tailWord_423410
  simp only [CollatzResearch.WordTrace]
  refine ⟨3860757849016339379000921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10295354264043571677335789 3860757849016339379000921)
  ·
    refine ⟨2895568386762254534250691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3860757849016339379000921 2895568386762254534250691)
    ·
      refine ⟨4343352580143381801376037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2895568386762254534250691 4343352580143381801376037)
      ·
        refine ⟨814378608776884087758007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4343352580143381801376037 814378608776884087758007)
        ·
          refine ⟨1221567913165326131637011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814378608776884087758007 1221567913165326131637011)
          ·
            refine ⟨1832351869747989197455517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1221567913165326131637011 1832351869747989197455517)
            ·
              refine ⟨687131951155495949045819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1832351869747989197455517 687131951155495949045819)
              ·
                refine ⟨1030697926733243923568729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 687131951155495949045819 1030697926733243923568729)
                ·
                  refine ⟨773023445049932942676547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1030697926733243923568729 773023445049932942676547)
                  ·
                    refine ⟨1159535167574899414014821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 773023445049932942676547 1159535167574899414014821)
                    ·
                      refine ⟨217412843920293640127779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1159535167574899414014821 217412843920293640127779)
                      ·
                        rfl

theorem cell23_423410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_423410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423410 prefixEnd_423410 := by exact prefixLift 423410
  have htrace : WordTrace (prefixWord ++ tailWord_423410) baseStart_423410 baseEnd_423410 := by
    simpa [prefixWord, tailWord_423410, baseEnd_423410] using wordTrace_append hprefix tailTrace_423410
  have hstable : (prefixWord ++ tailWord_423410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423410).length < 2 ^ (prefixWord ++ tailWord_423410).sum := by decide
  have hdescent : baseEnd_423410 < baseStart_423410 := by decide
  rcases family_descends (prefixWord ++ tailWord_423410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423420 : List Nat := [2, 2, 2, 1, 2, 1, 3, 5, 1, 4]
def baseStart_423420 : Nat := 118140960795 + 423420 * 2 ^ 59
def prefixEnd_423420 : Nat := 4983230072969 + 3 ^ 40 * 423420 * 2
def baseEnd_423420 : Nat := 72472659575612867000911

theorem tailTrace_423420 : CollatzResearch.WordTrace tailWord_423420 prefixEnd_423420 72472659575612867000911 := by
  unfold tailWord_423420
  simp only [CollatzResearch.WordTrace]
  refine ⟨7721698063014564611933857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10295597417352752815911809 7721698063014564611933857)
  ·
    refine ⟨5791273547260923458950393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7721698063014564611933857 5791273547260923458950393)
    ·
      refine ⟨4343455160445692594212795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5791273547260923458950393 4343455160445692594212795)
      ·
        refine ⟨6515182740668538891319193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4343455160445692594212795 6515182740668538891319193)
        ·
          refine ⟨4886387055501404168489395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6515182740668538891319193 4886387055501404168489395)
          ·
            refine ⟨7329580583252106252734093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4886387055501404168489395 7329580583252106252734093)
            ·
              refine ⟨2748592718719539844775285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7329580583252106252734093 2748592718719539844775285)
              ·
                refine ⟨257680567379956860447683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2748592718719539844775285 257680567379956860447683)
                ·
                  refine ⟨386520851069935290671525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257680567379956860447683 386520851069935290671525)
                  ·
                    refine ⟨72472659575612867000911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 386520851069935290671525 72472659575612867000911)
                    ·
                      rfl

theorem cell23_423420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_423420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423420 prefixEnd_423420 := by exact prefixLift 423420
  have htrace : WordTrace (prefixWord ++ tailWord_423420) baseStart_423420 baseEnd_423420 := by
    simpa [prefixWord, tailWord_423420, baseEnd_423420] using wordTrace_append hprefix tailTrace_423420
  have hstable : (prefixWord ++ tailWord_423420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423420).length < 2 ^ (prefixWord ++ tailWord_423420).sum := by decide
  have hdescent : baseEnd_423420 < baseStart_423420 := by decide
  rcases family_descends (prefixWord ++ tailWord_423420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423493 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 4, 4]
def baseStart_423493 : Nat := 118140960795 + 423493 * 2 ^ 59
def prefixEnd_423493 : Nat := 4983230072969 + 3 ^ 40 * 423493 * 2
def baseEnd_423493 : Nat := 72485154271538938463299

theorem tailTrace_423493 : CollatzResearch.WordTrace tailWord_423493 prefixEnd_423493 72485154271538938463299 := by
  unfold tailWord_423493
  simp only [CollatzResearch.WordTrace]
  refine ⟨15446058654764662691275133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10297372436509775127516755 15446058654764662691275133)
  ·
    refine ⟨5792271995536748509228175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15446058654764662691275133 5792271995536748509228175)
    ·
      refine ⟨8688407993305122763842263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5792271995536748509228175 8688407993305122763842263)
      ·
        refine ⟨13032611989957684145763395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8688407993305122763842263 13032611989957684145763395)
        ·
          refine ⟨19548917984936526218645093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13032611989957684145763395 19548917984936526218645093)
          ·
            refine ⟨3665422122175598665995955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19548917984936526218645093 3665422122175598665995955)
            ·
              refine ⟨5498133183263397998993933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3665422122175598665995955 5498133183263397998993933)
              ·
                refine ⟨2061799943723774249622725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5498133183263397998993933 2061799943723774249622725)
                ·
                  refine ⟨386587489448207671804261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2061799943723774249622725 386587489448207671804261)
                  ·
                    refine ⟨72485154271538938463299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 386587489448207671804261 72485154271538938463299)
                    ·
                      rfl

theorem cell23_423493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 4].length) (baseStart_423493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423493 prefixEnd_423493 := by exact prefixLift 423493
  have htrace : WordTrace (prefixWord ++ tailWord_423493) baseStart_423493 baseEnd_423493 := by
    simpa [prefixWord, tailWord_423493, baseEnd_423493] using wordTrace_append hprefix tailTrace_423493
  have hstable : (prefixWord ++ tailWord_423493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423493).length < 2 ^ (prefixWord ++ tailWord_423493).sum := by decide
  have hdescent : baseEnd_423493 < baseStart_423493 := by decide
  rcases family_descends (prefixWord ++ tailWord_423493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423503 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 3]
def baseStart_423503 : Nat := 118140960795 + 423503 * 2 ^ 59
def prefixEnd_423503 : Nat := 4983230072969 + 3 ^ 40 * 423503 * 2
def baseEnd_423503 : Nat := 217460597621161776264851

theorem tailTrace_423503 : CollatzResearch.WordTrace tailWord_423503 prefixEnd_423503 217460597621161776264851 := by
  unfold tailWord_423503
  simp only [CollatzResearch.WordTrace]
  refine ⟨15446423384728434399139163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10297615589818956266092775 15446423384728434399139163)
  ·
    refine ⟨23169635077092651598708745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15446423384728434399139163 23169635077092651598708745)
    ·
      refine ⟨17377226307819488699031559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23169635077092651598708745 17377226307819488699031559)
      ·
        refine ⟨26065839461729233048547339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17377226307819488699031559 26065839461729233048547339)
        ·
          refine ⟨39098759192593849572821009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26065839461729233048547339 39098759192593849572821009)
          ·
            refine ⟨29324069394445387179615757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39098759192593849572821009 29324069394445387179615757)
            ·
              refine ⟨10996526022917020192355909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29324069394445387179615757 10996526022917020192355909)
              ·
                refine ⟨2061848629296941286066733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10996526022917020192355909 2061848629296941286066733)
                ·
                  refine ⟨773193235986352982275025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2061848629296941286066733 773193235986352982275025)
                  ·
                    refine ⟨579894926989764736706269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 773193235986352982275025 579894926989764736706269)
                    ·
                      refine ⟨217460597621161776264851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 579894926989764736706269 217460597621161776264851)
                      ·
                        rfl

theorem cell23_423503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 3].length) (baseStart_423503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423503 prefixEnd_423503 := by exact prefixLift 423503
  have htrace : WordTrace (prefixWord ++ tailWord_423503) baseStart_423503 baseEnd_423503 := by
    simpa [prefixWord, tailWord_423503, baseEnd_423503] using wordTrace_append hprefix tailTrace_423503
  have hstable : (prefixWord ++ tailWord_423503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423503).length < 2 ^ (prefixWord ++ tailWord_423503).sum := by decide
  have hdescent : baseEnd_423503 < baseStart_423503 := by decide
  rcases family_descends (prefixWord ++ tailWord_423503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423530 : List Nat := [3, 1, 3, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_423530 : Nat := 118140960795 + 423530 * 2 ^ 59
def prefixEnd_423530 : Nat := 4983230072969 + 3 ^ 40 * 423530 * 2
def baseEnd_423530 : Nat := 217474461598833170627227

theorem tailTrace_423530 : CollatzResearch.WordTrace tailWord_423530 prefixEnd_423530 217474461598833170627227 := by
  unfold tailWord_423530
  simp only [CollatzResearch.WordTrace]
  refine ⟨3861852038907654502593011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10298272103753745340248029 3861852038907654502593011)
  ·
    refine ⟨5792778058361481753889517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3861852038907654502593011 5792778058361481753889517)
    ·
      refine ⟨2172291771885555657708569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5792778058361481753889517 2172291771885555657708569)
      ·
        refine ⟨1629218828914166743281427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2172291771885555657708569 1629218828914166743281427)
        ·
          refine ⟨2443828243371250114922141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1629218828914166743281427 2443828243371250114922141)
          ·
            refine ⟨916435591264218793095803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2443828243371250114922141 916435591264218793095803)
            ·
              refine ⟨1374653386896328189643705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 916435591264218793095803 1374653386896328189643705)
              ·
                refine ⟨1030990040172246142232779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1374653386896328189643705 1030990040172246142232779)
                ·
                  refine ⟨1546485060258369213349169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1030990040172246142232779 1546485060258369213349169)
                  ·
                    refine ⟨1159863795193776910011877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1546485060258369213349169 1159863795193776910011877)
                    ·
                      refine ⟨217474461598833170627227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1159863795193776910011877 217474461598833170627227)
                      ·
                        rfl

theorem cell23_423530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_423530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423530 prefixEnd_423530 := by exact prefixLift 423530
  have htrace : WordTrace (prefixWord ++ tailWord_423530) baseStart_423530 baseEnd_423530 := by
    simpa [prefixWord, tailWord_423530, baseEnd_423530] using wordTrace_append hprefix tailTrace_423530
  have hstable : (prefixWord ++ tailWord_423530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423530).length < 2 ^ (prefixWord ++ tailWord_423530).sum := by decide
  have hdescent : baseEnd_423530 < baseStart_423530 := by decide
  rcases family_descends (prefixWord ++ tailWord_423530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423534 : List Nat := [4, 1, 2, 2, 3, 1, 3, 1, 1, 1, 4]
def baseStart_423534 : Nat := 118140960795 + 423534 * 2 ^ 59
def prefixEnd_423534 : Nat := 4983230072969 + 3 ^ 40 * 423534 * 2
def baseEnd_423534 : Nat := 217476515521451154977209

theorem tailTrace_423534 : CollatzResearch.WordTrace tailWord_423534 prefixEnd_423534 217476515521451154977209 := by
  unfold tailWord_423534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1930944255952015836689707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10298369365077417795678437 1930944255952015836689707)
  ·
    refine ⟨2896416383928023755034561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1930944255952015836689707 2896416383928023755034561)
    ·
      refine ⟨2172312287946017816275921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2896416383928023755034561 2172312287946017816275921)
      ·
        refine ⟨1629234215959513362206941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2172312287946017816275921 1629234215959513362206941)
        ·
          refine ⟨610962830984817510827603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1629234215959513362206941 610962830984817510827603)
          ·
            refine ⟨916444246477226266241405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610962830984817510827603 916444246477226266241405)
            ·
              refine ⟨343666592428959849840527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 916444246477226266241405 343666592428959849840527)
              ·
                refine ⟨515499888643439774760791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343666592428959849840527 515499888643439774760791)
                ·
                  refine ⟨773249832965159662141187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 515499888643439774760791 773249832965159662141187)
                  ·
                    refine ⟨1159874749447739493211781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 773249832965159662141187 1159874749447739493211781)
                    ·
                      refine ⟨217476515521451154977209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1159874749447739493211781 217476515521451154977209)
                      ·
                        rfl

theorem cell23_423534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_423534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423534 prefixEnd_423534 := by exact prefixLift 423534
  have htrace : WordTrace (prefixWord ++ tailWord_423534) baseStart_423534 baseEnd_423534 := by
    simpa [prefixWord, tailWord_423534, baseEnd_423534] using wordTrace_append hprefix tailTrace_423534
  have hstable : (prefixWord ++ tailWord_423534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423534).length < 2 ^ (prefixWord ++ tailWord_423534).sum := by decide
  have hdescent : baseEnd_423534 < baseStart_423534 := by decide
  rcases family_descends (prefixWord ++ tailWord_423534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423553 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 2, 7]
def baseStart_423553 : Nat := 118140960795 + 423553 * 2 ^ 59
def prefixEnd_423553 : Nat := 4983230072969 + 3 ^ 40 * 423553 * 2
def baseEnd_423553 : Nat := 72495423884628860213207

theorem tailTrace_423553 : CollatzResearch.WordTrace tailWord_423553 prefixEnd_423553 72495423884628860213207 := by
  unfold tailWord_423553
  simp only [CollatzResearch.WordTrace]
  refine ⟨15448247034547292938459313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10298831356364861958972875 15448247034547292938459313)
  ·
    refine ⟨11586185275910469703844485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15448247034547292938459313 11586185275910469703844485)
    ·
      refine ⟨2172409739233213069470841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11586185275910469703844485 2172409739233213069470841)
      ·
        refine ⟨1629307304424909802103131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2172409739233213069470841 1629307304424909802103131)
        ·
          refine ⟨2443960956637364703154697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1629307304424909802103131 2443960956637364703154697)
          ·
            refine ⟨1832970717478023527366023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2443960956637364703154697 1832970717478023527366023)
            ·
              refine ⟨2749456076217035291049035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1832970717478023527366023 2749456076217035291049035)
              ·
                refine ⟨4124184114325552936573553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2749456076217035291049035 4124184114325552936573553)
                ·
                  refine ⟨3093138085744164702430165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4124184114325552936573553 3093138085744164702430165)
                  ·
                    refine ⟨72495423884628860213207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3093138085744164702430165 72495423884628860213207)
                    ·
                      rfl

theorem cell23_423553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_423553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423553 prefixEnd_423553 := by exact prefixLift 423553
  have htrace : WordTrace (prefixWord ++ tailWord_423553) baseStart_423553 baseEnd_423553 := by
    simpa [prefixWord, tailWord_423553, baseEnd_423553] using wordTrace_append hprefix tailTrace_423553
  have hstable : (prefixWord ++ tailWord_423553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423553).length < 2 ^ (prefixWord ++ tailWord_423553).sum := by decide
  have hdescent : baseEnd_423553 < baseStart_423553 := by decide
  rcases family_descends (prefixWord ++ tailWord_423553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423603 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 4]
def baseStart_423603 : Nat := 118140960795 + 423603 * 2 ^ 59
def prefixEnd_423603 : Nat := 4983230072969 + 3 ^ 40 * 423603 * 2
def baseEnd_423603 : Nat := 217511945686611385014391

theorem tailTrace_423603 : CollatzResearch.WordTrace tailWord_423603 prefixEnd_423603 217511945686611385014391 := by
  unfold tailWord_423603
  simp only [CollatzResearch.WordTrace]
  refine ⟨15450070684366151477779463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10300047122910767651852975 15450070684366151477779463)
  ·
    refine ⟨23175106026549227216669195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15450070684366151477779463 23175106026549227216669195)
    ·
      refine ⟨34762659039823840825003793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23175106026549227216669195 34762659039823840825003793)
      ·
        refine ⟨26071994279867880618752845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34762659039823840825003793 26071994279867880618752845)
        ·
          refine ⟨9776997854950455232032317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26071994279867880618752845 9776997854950455232032317)
          ·
            refine ⟨3666374195606420712012119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9776997854950455232032317 3666374195606420712012119)
            ·
              refine ⟨5499561293409631068018179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3666374195606420712012119 5499561293409631068018179)
              ·
                refine ⟨8249341940114446602027269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5499561293409631068018179 8249341940114446602027269)
                ·
                  refine ⟨1546751613771458737880113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8249341940114446602027269 1546751613771458737880113)
                  ·
                    refine ⟨1160063710328594053410085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1546751613771458737880113 1160063710328594053410085)
                    ·
                      refine ⟨217511945686611385014391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1160063710328594053410085 217511945686611385014391)
                      ·
                        rfl

theorem cell23_423603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 4].length) (baseStart_423603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423603 prefixEnd_423603 := by exact prefixLift 423603
  have htrace : WordTrace (prefixWord ++ tailWord_423603) baseStart_423603 baseEnd_423603 := by
    simpa [prefixWord, tailWord_423603, baseEnd_423603] using wordTrace_append hprefix tailTrace_423603
  have hstable : (prefixWord ++ tailWord_423603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423603).length < 2 ^ (prefixWord ++ tailWord_423603).sum := by decide
  have hdescent : baseEnd_423603 < baseStart_423603 := by decide
  rcases family_descends (prefixWord ++ tailWord_423603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423618 : List Nat := [3, 5, 1, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_423618 : Nat := 118140960795 + 423618 * 2 ^ 59
def prefixEnd_423618 : Nat := 4983230072969 + 3 ^ 40 * 423618 * 2
def baseEnd_423618 : Nat := 217519647896428826326823

theorem tailTrace_423618 : CollatzResearch.WordTrace tailWord_423618 prefixEnd_423618 217519647896428826326823 := by
  unfold tailWord_423618
  simp only [CollatzResearch.WordTrace]
  refine ⟨3862654444827952259893877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10300411852874539359717005 3862654444827952259893877)
  ·
    refine ⟨362123854202620524365051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3862654444827952259893877 362123854202620524365051)
    ·
      refine ⟨543185781303930786547577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362123854202620524365051 543185781303930786547577)
      ·
        refine ⟨407389335977948089910683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543185781303930786547577 407389335977948089910683)
        ·
          refine ⟨611084003966922134866025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407389335977948089910683 611084003966922134866025)
          ·
            refine ⟨458313002975191601149519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 611084003966922134866025 458313002975191601149519)
            ·
              refine ⟨687469504462787401724279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458313002975191601149519 687469504462787401724279)
              ·
                refine ⟨1031204256694181102586419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 687469504462787401724279 1031204256694181102586419)
                ·
                  refine ⟨1546806385041271653879629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1031204256694181102586419 1546806385041271653879629)
                  ·
                    refine ⟨580052394390476870204861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1546806385041271653879629 580052394390476870204861)
                    ·
                      refine ⟨217519647896428826326823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 580052394390476870204861 217519647896428826326823)
                      ·
                        rfl

theorem cell23_423618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_423618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423618 prefixEnd_423618 := by exact prefixLift 423618
  have htrace : WordTrace (prefixWord ++ tailWord_423618) baseStart_423618 baseEnd_423618 := by
    simpa [prefixWord, tailWord_423618, baseEnd_423618] using wordTrace_append hprefix tailTrace_423618
  have hstable : (prefixWord ++ tailWord_423618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423618).length < 2 ^ (prefixWord ++ tailWord_423618).sum := by decide
  have hdescent : baseEnd_423618 < baseStart_423618 := by decide
  rcases family_descends (prefixWord ++ tailWord_423618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423620 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_423620 : Nat := 118140960795 + 423620 * 2 ^ 59
def prefixEnd_423620 : Nat := 4983230072969 + 3 ^ 40 * 423620 * 2
def baseEnd_423620 : Nat := 217520674857737818501813

theorem tailTrace_423620 : CollatzResearch.WordTrace tailWord_423620 prefixEnd_423620 217520674857737818501813 := by
  unfold tailWord_423620
  simp only [CollatzResearch.WordTrace]
  refine ⟨7725345362652281690574157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10300460483536375587432209 7725345362652281690574157)
  ·
    refine ⟨2897004510994605633965309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7725345362652281690574157 2897004510994605633965309)
    ·
      refine ⟨1086376691622977112736991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2897004510994605633965309 1086376691622977112736991)
      ·
        refine ⟨1629565037434465669105487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1086376691622977112736991 1629565037434465669105487)
        ·
          refine ⟨2444347556151698503658231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1629565037434465669105487 2444347556151698503658231)
          ·
            refine ⟨3666521334227547755487347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2444347556151698503658231 3666521334227547755487347)
            ·
              refine ⟨5499782001341321633231021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3666521334227547755487347 5499782001341321633231021)
              ·
                refine ⟨2062418250502995612461633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5499782001341321633231021 2062418250502995612461633)
                ·
                  refine ⟨1546813687877246709346225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2062418250502995612461633 1546813687877246709346225)
                  ·
                    refine ⟨1160110265907935032009669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1546813687877246709346225 1160110265907935032009669)
                    ·
                      refine ⟨217520674857737818501813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1160110265907935032009669 217520674857737818501813)
                      ·
                        rfl

theorem cell23_423620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_423620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423620 prefixEnd_423620 := by exact prefixLift 423620
  have htrace : WordTrace (prefixWord ++ tailWord_423620) baseStart_423620 baseEnd_423620 := by
    simpa [prefixWord, tailWord_423620, baseEnd_423620] using wordTrace_append hprefix tailTrace_423620
  have hstable : (prefixWord ++ tailWord_423620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423620).length < 2 ^ (prefixWord ++ tailWord_423620).sum := by decide
  have hdescent : baseEnd_423620 < baseStart_423620 := by decide
  rcases family_descends (prefixWord ++ tailWord_423620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423670 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_423670 : Nat := 118140960795 + 423670 * 2 ^ 59
def prefixEnd_423670 : Nat := 4983230072969 + 3 ^ 40 * 423670 * 2
def baseEnd_423670 : Nat := 217546348890462622876583

theorem tailTrace_423670 : CollatzResearch.WordTrace tailWord_423670 prefixEnd_423670 217546348890462622876583 := by
  unfold tailWord_423670
  simp only [CollatzResearch.WordTrace]
  refine ⟨965782148445213870029279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10301676250082281280312309 965782148445213870029279)
  ·
    refine ⟨1448673222667820805043919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 965782148445213870029279 1448673222667820805043919)
    ·
      refine ⟨2173009834001731207565879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1448673222667820805043919 2173009834001731207565879)
      ·
        refine ⟨3259514751002596811348819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2173009834001731207565879 3259514751002596811348819)
        ·
          refine ⟨4889272126503895217023229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3259514751002596811348819 4889272126503895217023229)
          ·
            refine ⟨1833477047438960706383711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4889272126503895217023229 1833477047438960706383711)
            ·
              refine ⟨2750215571158441059575567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1833477047438960706383711 2750215571158441059575567)
              ·
                refine ⟨4125323356737661589363351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2750215571158441059575567 4125323356737661589363351)
                ·
                  refine ⟨6187985035106492384045027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4125323356737661589363351 6187985035106492384045027)
                  ·
                    refine ⟨9281977552659738576067541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6187985035106492384045027 9281977552659738576067541)
                    ·
                      refine ⟨217546348890462622876583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9281977552659738576067541 217546348890462622876583)
                      ·
                        rfl

theorem cell23_423670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_423670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423670 prefixEnd_423670 := by exact prefixLift 423670
  have htrace : WordTrace (prefixWord ++ tailWord_423670) baseStart_423670 baseEnd_423670 := by
    simpa [prefixWord, tailWord_423670, baseEnd_423670] using wordTrace_append hprefix tailTrace_423670
  have hstable : (prefixWord ++ tailWord_423670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423670).length < 2 ^ (prefixWord ++ tailWord_423670).sum := by decide
  have hdescent : baseEnd_423670 < baseStart_423670 := by decide
  rcases family_descends (prefixWord ++ tailWord_423670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423717 : List Nat := [1, 3, 1, 2, 3, 2, 2, 2, 2, 2, 3]
def baseStart_423717 : Nat := 118140960795 + 423717 * 2 ^ 59
def prefixEnd_423717 : Nat := 4983230072969 + 3 ^ 40 * 423717 * 2
def baseEnd_423717 : Nat := 217570482481223938988867

theorem tailTrace_423717 : CollatzResearch.WordTrace tailWord_423717 prefixEnd_423717 217570482481223938988867 := by
  unfold tailWord_423717
  simp only [CollatzResearch.WordTrace]
  refine ⟨15454228605953148947429405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10302819070635432631619603 15454228605953148947429405)
  ·
    refine ⟨5795335727232430855286027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15454228605953148947429405 5795335727232430855286027)
    ·
      refine ⟨8693003590848646282929041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5795335727232430855286027 8693003590848646282929041)
      ·
        refine ⟨6519752693136484712196781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8693003590848646282929041 6519752693136484712196781)
        ·
          refine ⟨2444907259926181767073793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6519752693136484712196781 2444907259926181767073793)
          ·
            refine ⟨1833680444944636325305345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2444907259926181767073793 1833680444944636325305345)
            ·
              refine ⟨1375260333708477243979009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1833680444944636325305345 1375260333708477243979009)
              ·
                refine ⟨1031445250281357932984257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1375260333708477243979009 1031445250281357932984257)
                ·
                  refine ⟨773583937711018449738193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1031445250281357932984257 773583937711018449738193)
                  ·
                    refine ⟨580187953283263837303645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 773583937711018449738193 580187953283263837303645)
                    ·
                      refine ⟨217570482481223938988867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 580187953283263837303645 217570482481223938988867)
                      ·
                        rfl

theorem cell23_423717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_423717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423717 prefixEnd_423717 := by exact prefixLift 423717
  have htrace : WordTrace (prefixWord ++ tailWord_423717) baseStart_423717 baseEnd_423717 := by
    simpa [prefixWord, tailWord_423717, baseEnd_423717] using wordTrace_append hprefix tailTrace_423717
  have hstable : (prefixWord ++ tailWord_423717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423717).length < 2 ^ (prefixWord ++ tailWord_423717).sum := by decide
  have hdescent : baseEnd_423717 < baseStart_423717 := by decide
  rcases family_descends (prefixWord ++ tailWord_423717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423724 : List Nat := [2, 2, 1, 1, 1, 6, 1, 4, 1, 4]
def baseStart_423724 : Nat := 118140960795 + 423724 * 2 ^ 59
def prefixEnd_423724 : Nat := 4983230072969 + 3 ^ 40 * 423724 * 2
def baseEnd_423724 : Nat := 72524692281935137200445

theorem tailTrace_423724 : CollatzResearch.WordTrace tailWord_423724 prefixEnd_423724 72524692281935137200445 := by
  unfold tailWord_423724
  simp only [CollatzResearch.WordTrace]
  refine ⟨7727241958463894571467113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10302989277951859428622817 7727241958463894571467113)
  ·
    refine ⟨5795431468847920928600335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7727241958463894571467113 5795431468847920928600335)
    ·
      refine ⟨8693147203271881392900503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5795431468847920928600335 8693147203271881392900503)
      ·
        refine ⟨13039720804907822089350755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8693147203271881392900503 13039720804907822089350755)
        ·
          refine ⟨19559581207361733134026133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13039720804907822089350755 19559581207361733134026133)
          ·
            refine ⟨916855369095081240657475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19559581207361733134026133 916855369095081240657475)
            ·
              refine ⟨1375283053642621860986213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 916855369095081240657475 1375283053642621860986213)
              ·
                refine ⟨257865572557991598934915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1375283053642621860986213 257865572557991598934915)
                ·
                  refine ⟨386798358836987398402373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257865572557991598934915 386798358836987398402373)
                  ·
                    refine ⟨72524692281935137200445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 386798358836987398402373 72524692281935137200445)
                    ·
                      rfl

theorem cell23_423724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 1, 4].length) (baseStart_423724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423724 prefixEnd_423724 := by exact prefixLift 423724
  have htrace : WordTrace (prefixWord ++ tailWord_423724) baseStart_423724 baseEnd_423724 := by
    simpa [prefixWord, tailWord_423724, baseEnd_423724] using wordTrace_append hprefix tailTrace_423724
  have hstable : (prefixWord ++ tailWord_423724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423724).length < 2 ^ (prefixWord ++ tailWord_423724).sum := by decide
  have hdescent : baseEnd_423724 < baseStart_423724 := by decide
  rcases family_descends (prefixWord ++ tailWord_423724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423747 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 5, 1, 3]
def baseStart_423747 : Nat := 118140960795 + 423747 * 2 ^ 59
def prefixEnd_423747 : Nat := 4983230072969 + 3 ^ 40 * 423747 * 2
def baseEnd_423747 : Nat := 217585886900858821613729

theorem tailTrace_423747 : CollatzResearch.WordTrace tailWord_423747 prefixEnd_423747 217585886900858821613729 := by
  unfold tailWord_423747
  simp only [CollatzResearch.WordTrace]
  refine ⟨15455322795844464071021495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10303548530562976047347663 15455322795844464071021495)
  ·
    refine ⟨23182984193766696106532243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15455322795844464071021495 23182984193766696106532243)
    ·
      refine ⟨34774476290650044159798365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23182984193766696106532243 34774476290650044159798365)
      ·
        refine ⟨13040428608993766559924387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34774476290650044159798365 13040428608993766559924387)
        ·
          refine ⟨19560642913490649839886581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13040428608993766559924387 19560642913490649839886581)
          ·
            refine ⟨1833810273139748422489367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19560642913490649839886581 1833810273139748422489367)
            ·
              refine ⟨2750715409709622633734051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1833810273139748422489367 2750715409709622633734051)
              ·
                refine ⟨4126073114564433950601077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2750715409709622633734051 4126073114564433950601077)
                ·
                  refine ⟨386819354490415682868851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4126073114564433950601077 386819354490415682868851)
                  ·
                    refine ⟨580229031735623524303277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 386819354490415682868851 580229031735623524303277)
                    ·
                      refine ⟨217585886900858821613729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 580229031735623524303277 217585886900858821613729)
                      ·
                        rfl

theorem cell23_423747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 1, 3].length) (baseStart_423747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423747 prefixEnd_423747 := by exact prefixLift 423747
  have htrace : WordTrace (prefixWord ++ tailWord_423747) baseStart_423747 baseEnd_423747 := by
    simpa [prefixWord, tailWord_423747, baseEnd_423747] using wordTrace_append hprefix tailTrace_423747
  have hstable : (prefixWord ++ tailWord_423747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423747).length < 2 ^ (prefixWord ++ tailWord_423747).sum := by decide
  have hdescent : baseEnd_423747 < baseStart_423747 := by decide
  rcases family_descends (prefixWord ++ tailWord_423747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423815 : List Nat := [1, 1, 4, 2, 5, 1, 1, 3, 1, 1, 3]
def baseStart_423815 : Nat := 118140960795 + 423815 * 2 ^ 59
def prefixEnd_423815 : Nat := 4983230072969 + 3 ^ 40 * 423815 * 2
def baseEnd_423815 : Nat := 217620803585364555563417

theorem tailTrace_423815 : CollatzResearch.WordTrace tailWord_423815 prefixEnd_423815 217620803585364555563417 := by
  unfold tailWord_423815
  simp only [CollatzResearch.WordTrace]
  refine ⟨15457802959598111684496899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10305201973065407789664599 15457802959598111684496899)
  ·
    refine ⟨23186704439397167526745349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15457802959598111684496899 23186704439397167526745349)
    ·
      refine ⟨4347507082386968911264753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23186704439397167526745349 4347507082386968911264753)
      ·
        refine ⟨3260630311790226683448565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4347507082386968911264753 3260630311790226683448565)
        ·
          refine ⟨305684091730333751573303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3260630311790226683448565 305684091730333751573303)
          ·
            refine ⟨458526137595500627359955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305684091730333751573303 458526137595500627359955)
            ·
              refine ⟨687789206393250941039933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458526137595500627359955 687789206393250941039933)
              ·
                refine ⟨257920952397469102889975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 687789206393250941039933 257920952397469102889975)
                ·
                  refine ⟨386881428596203654334963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257920952397469102889975 386881428596203654334963)
                  ·
                    refine ⟨580322142894305481502445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 386881428596203654334963 580322142894305481502445)
                    ·
                      refine ⟨217620803585364555563417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 580322142894305481502445 217620803585364555563417)
                      ·
                        rfl

theorem cell23_423815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_423815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423815 prefixEnd_423815 := by exact prefixLift 423815
  have htrace : WordTrace (prefixWord ++ tailWord_423815) baseStart_423815 baseEnd_423815 := by
    simpa [prefixWord, tailWord_423815, baseEnd_423815] using wordTrace_append hprefix tailTrace_423815
  have hstable : (prefixWord ++ tailWord_423815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423815).length < 2 ^ (prefixWord ++ tailWord_423815).sum := by decide
  have hdescent : baseEnd_423815 < baseStart_423815 := by decide
  rcases family_descends (prefixWord ++ tailWord_423815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423840 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 2, 7]
def baseStart_423840 : Nat := 118140960795 + 423840 * 2 ^ 59
def prefixEnd_423840 : Nat := 4983230072969 + 3 ^ 40 * 423840 * 2
def baseEnd_423840 : Nat := 72544546867242319250267

theorem tailTrace_423840 : CollatzResearch.WordTrace tailWord_423840 prefixEnd_423840 72544546867242319250267 := by
  unfold tailWord_423840
  simp only [CollatzResearch.WordTrace]
  refine ⟨7729357392253770477078487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10305809856338360636104649 7729357392253770477078487)
  ·
    refine ⟨11594036088380655715617731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7729357392253770477078487 11594036088380655715617731)
    ·
      refine ⟨17391054132570983573426597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11594036088380655715617731 17391054132570983573426597)
      ·
        refine ⟨3260822649857059420017487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17391054132570983573426597 3260822649857059420017487)
        ·
          refine ⟨4891233974785589130026231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3260822649857059420017487 4891233974785589130026231)
          ·
            refine ⟨7336850962178383695039347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4891233974785589130026231 7336850962178383695039347)
            ·
              refine ⟨11005276443267575542559021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7336850962178383695039347 11005276443267575542559021)
              ·
                refine ⟨4126978666225340828459633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11005276443267575542559021 4126978666225340828459633)
                ·
                  refine ⟨3095233999669005621344725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4126978666225340828459633 3095233999669005621344725)
                  ·
                    refine ⟨72544546867242319250267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3095233999669005621344725 72544546867242319250267)
                    ·
                      rfl

theorem cell23_423840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 2, 7].length) (baseStart_423840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423840 prefixEnd_423840 := by exact prefixLift 423840
  have htrace : WordTrace (prefixWord ++ tailWord_423840) baseStart_423840 baseEnd_423840 := by
    simpa [prefixWord, tailWord_423840, baseEnd_423840] using wordTrace_append hprefix tailTrace_423840
  have hstable : (prefixWord ++ tailWord_423840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423840).length < 2 ^ (prefixWord ++ tailWord_423840).sum := by decide
  have hdescent : baseEnd_423840 < baseStart_423840 := by decide
  rcases family_descends (prefixWord ++ tailWord_423840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423848 : List Nat := [2, 1, 6, 2, 1, 1, 1, 3, 2, 4]
def baseStart_423848 : Nat := 118140960795 + 423848 * 2 ^ 59
def prefixEnd_423848 : Nat := 4983230072969 + 3 ^ 40 * 423848 * 2
def baseEnd_423848 : Nat := 72545916148987642150255

theorem tailTrace_423848 : CollatzResearch.WordTrace tailWord_423848 prefixEnd_423848 72545916148987642150255 := by
  unfold tailWord_423848
  simp only [CollatzResearch.WordTrace]
  refine ⟨7729503284239279160224099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10306004378985705546965465 7729503284239279160224099)
  ·
    refine ⟨11594254926358918740336149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7729503284239279160224099 11594254926358918740336149)
    ·
      refine ⟨543480699673074315953257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11594254926358918740336149 543480699673074315953257)
      ·
        refine ⟨407610524754805736964943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543480699673074315953257 407610524754805736964943)
        ·
          refine ⟨611415787132208605447415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407610524754805736964943 611415787132208605447415)
          ·
            refine ⟨917123680698312908171123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611415787132208605447415 917123680698312908171123)
            ·
              refine ⟨1375685521047469362256685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917123680698312908171123 1375685521047469362256685)
              ·
                refine ⟨515882070392801010846257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1375685521047469362256685 515882070392801010846257)
                ·
                  refine ⟨386911552794600758134693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515882070392801010846257 386911552794600758134693)
                  ·
                    refine ⟨72545916148987642150255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 386911552794600758134693 72545916148987642150255)
                    ·
                      rfl

theorem cell23_423848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_423848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423848 prefixEnd_423848 := by exact prefixLift 423848
  have htrace : WordTrace (prefixWord ++ tailWord_423848) baseStart_423848 baseEnd_423848 := by
    simpa [prefixWord, tailWord_423848, baseEnd_423848] using wordTrace_append hprefix tailTrace_423848
  have hstable : (prefixWord ++ tailWord_423848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423848).length < 2 ^ (prefixWord ++ tailWord_423848).sum := by decide
  have hdescent : baseEnd_423848 < baseStart_423848 := by decide
  rcases family_descends (prefixWord ++ tailWord_423848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423864 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 3, 3, 2]
def baseStart_423864 : Nat := 118140960795 + 423864 * 2 ^ 59
def prefixEnd_423864 : Nat := 4983230072969 + 3 ^ 40 * 423864 * 2
def baseEnd_423864 : Nat := 217645964137434863850691

theorem tailTrace_423864 : CollatzResearch.WordTrace tailWord_423864 prefixEnd_423864 217645964137434863850691 := by
  unfold tailWord_423864
  simp only [CollatzResearch.WordTrace]
  refine ⟨7729795068210296526515323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10306393424280395368687097 7729795068210296526515323)
  ·
    refine ⟨11594692602315444789772985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7729795068210296526515323 11594692602315444789772985)
    ·
      refine ⟨8696019451736583592329739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11594692602315444789772985 8696019451736583592329739)
      ·
        refine ⟨13044029177604875388494609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8696019451736583592329739 13044029177604875388494609)
        ·
          refine ⟨9783021883203656541370957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13044029177604875388494609 9783021883203656541370957)
          ·
            refine ⟨3668633206201371203014109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9783021883203656541370957 3668633206201371203014109)
            ·
              refine ⟨1375737452325514201130291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3668633206201371203014109 1375737452325514201130291)
              ·
                refine ⟨2063606178488271301695437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1375737452325514201130291 2063606178488271301695437)
                ·
                  refine ⟨773852316933101738135789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2063606178488271301695437 773852316933101738135789)
                  ·
                    refine ⟨290194618849913151800921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 773852316933101738135789 290194618849913151800921)
                    ·
                      refine ⟨217645964137434863850691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 290194618849913151800921 217645964137434863850691)
                      ·
                        rfl

theorem cell23_423864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 3, 3, 2].length) (baseStart_423864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423864 prefixEnd_423864 := by exact prefixLift 423864
  have htrace : WordTrace (prefixWord ++ tailWord_423864) baseStart_423864 baseEnd_423864 := by
    simpa [prefixWord, tailWord_423864, baseEnd_423864] using wordTrace_append hprefix tailTrace_423864
  have hstable : (prefixWord ++ tailWord_423864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423864).length < 2 ^ (prefixWord ++ tailWord_423864).sum := by decide
  have hdescent : baseEnd_423864 < baseStart_423864 := by decide
  rcases family_descends (prefixWord ++ tailWord_423864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423907 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 4]
def baseStart_423907 : Nat := 118140960795 + 423907 * 2 ^ 59
def prefixEnd_423907 : Nat := 4983230072969 + 3 ^ 40 * 423907 * 2
def baseEnd_423907 : Nat := 217668043805578195612993

theorem tailTrace_423907 : CollatzResearch.WordTrace tailWord_423907 prefixEnd_423907 217668043805578195612993 := by
  unfold tailWord_423907
  simp only [CollatzResearch.WordTrace]
  refine ⟨15461158475264811396845975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10307438983509874264563983 15461158475264811396845975)
  ·
    refine ⟨23191737712897217095268963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15461158475264811396845975 23191737712897217095268963)
    ·
      refine ⟨34787606569345825642903445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23191737712897217095268963 34787606569345825642903445)
      ·
        refine ⟨1630669057938085577011099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34787606569345825642903445 1630669057938085577011099)
        ·
          refine ⟨2446003586907128365516649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1630669057938085577011099 2446003586907128365516649)
          ·
            refine ⟨1834502690180346274137487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2446003586907128365516649 1834502690180346274137487)
            ·
              refine ⟨2751754035270519411206231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1834502690180346274137487 2751754035270519411206231)
              ·
                refine ⟨4127631052905779116809347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2751754035270519411206231 4127631052905779116809347)
                ·
                  refine ⟨6191446579358668675214021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4127631052905779116809347 6191446579358668675214021)
                  ·
                    refine ⟨1160896233629750376602629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6191446579358668675214021 1160896233629750376602629)
                    ·
                      refine ⟨217668043805578195612993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1160896233629750376602629 217668043805578195612993)
                      ·
                        rfl

theorem cell23_423907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_423907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423907 prefixEnd_423907 := by exact prefixLift 423907
  have htrace : WordTrace (prefixWord ++ tailWord_423907) baseStart_423907 baseEnd_423907 := by
    simpa [prefixWord, tailWord_423907, baseEnd_423907] using wordTrace_append hprefix tailTrace_423907
  have hstable : (prefixWord ++ tailWord_423907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423907).length < 2 ^ (prefixWord ++ tailWord_423907).sum := by decide
  have hdescent : baseEnd_423907 < baseStart_423907 := by decide
  rcases family_descends (prefixWord ++ tailWord_423907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423947 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 4, 5]
def baseStart_423947 : Nat := 118140960795 + 423947 * 2 ^ 59
def prefixEnd_423947 : Nat := 4983230072969 + 3 ^ 40 * 423947 * 2
def baseEnd_423947 : Nat := 72562861010586013037603

theorem tailTrace_423947 : CollatzResearch.WordTrace tailWord_423947 prefixEnd_423947 72562861010586013037603 := by
  unfold tailWord_423947
  simp only [CollatzResearch.WordTrace]
  refine ⟨15462617395119898228302095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10308411596746598818868063 15462617395119898228302095)
  ·
    refine ⟨23193926092679847342453143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15462617395119898228302095 23193926092679847342453143)
    ·
      refine ⟨34790889139019771013679715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23193926092679847342453143 34790889139019771013679715)
      ·
        refine ⟨52186333708529656520519573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34790889139019771013679715 52186333708529656520519573)
        ·
          refine ⟨2446234392587327649399355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52186333708529656520519573 2446234392587327649399355)
          ·
            refine ⟨3669351588880991474099033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2446234392587327649399355 3669351588880991474099033)
            ·
              refine ⟨2752013691660743605574275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3669351588880991474099033 2752013691660743605574275)
              ·
                refine ⟨4128020537491115408361413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2752013691660743605574275 4128020537491115408361413)
                ·
                  refine ⟨774003850779584139067765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4128020537491115408361413 774003850779584139067765)
                  ·
                    refine ⟨72562861010586013037603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 774003850779584139067765 72562861010586013037603)
                    ·
                      rfl

theorem cell23_423947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 5].length) (baseStart_423947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423947 prefixEnd_423947 := by exact prefixLift 423947
  have htrace : WordTrace (prefixWord ++ tailWord_423947) baseStart_423947 baseEnd_423947 := by
    simpa [prefixWord, tailWord_423947, baseEnd_423947] using wordTrace_append hprefix tailTrace_423947
  have hstable : (prefixWord ++ tailWord_423947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423947).length < 2 ^ (prefixWord ++ tailWord_423947).sum := by decide
  have hdescent : baseEnd_423947 < baseStart_423947 := by decide
  rcases family_descends (prefixWord ++ tailWord_423947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423967 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 4]
def baseStart_423967 : Nat := 118140960795 + 423967 * 2 ^ 59
def prefixEnd_423967 : Nat := 4983230072969 + 3 ^ 40 * 423967 * 2
def baseEnd_423967 : Nat := 217698852644847960862717

theorem tailTrace_423967 : CollatzResearch.WordTrace tailWord_423967 prefixEnd_423967 217698852644847960862717 := by
  unfold tailWord_423967
  simp only [CollatzResearch.WordTrace]
  refine ⟨15463346855047441644030155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10308897903364961096020103 15463346855047441644030155)
  ·
    refine ⟨23195020282571162466045233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15463346855047441644030155 23195020282571162466045233)
    ·
      refine ⟨17396265211928371849533925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23195020282571162466045233 17396265211928371849533925)
      ·
        refine ⟨3261799727236569721787611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17396265211928371849533925 3261799727236569721787611)
        ·
          refine ⟨4892699590854854582681417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3261799727236569721787611 4892699590854854582681417)
          ·
            refine ⟨3669524693141140937011063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4892699590854854582681417 3669524693141140937011063)
            ·
              refine ⟨5504287039711711405516595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3669524693141140937011063 5504287039711711405516595)
              ·
                refine ⟨8256430559567567108274893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5504287039711711405516595 8256430559567567108274893)
                ·
                  refine ⟨3096161459837837665603085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8256430559567567108274893 3096161459837837665603085)
                  ·
                    refine ⟨1161060547439189124601157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3096161459837837665603085 1161060547439189124601157)
                    ·
                      refine ⟨217698852644847960862717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1161060547439189124601157 217698852644847960862717)
                      ·
                        rfl

theorem cell23_423967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_423967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_423967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_423967 prefixEnd_423967 := by exact prefixLift 423967
  have htrace : WordTrace (prefixWord ++ tailWord_423967) baseStart_423967 baseEnd_423967 := by
    simpa [prefixWord, tailWord_423967, baseEnd_423967] using wordTrace_append hprefix tailTrace_423967
  have hstable : (prefixWord ++ tailWord_423967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423967).length < 2 ^ (prefixWord ++ tailWord_423967).sum := by decide
  have hdescent : baseEnd_423967 < baseStart_423967 := by decide
  rcases family_descends (prefixWord ++ tailWord_423967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424001 : List Nat := [1, 2, 5, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_424001 : Nat := 118140960795 + 424001 * 2 ^ 59
def prefixEnd_424001 : Nat := 4983230072969 + 3 ^ 40 * 424001 * 2
def baseEnd_424001 : Nat := 217716310987100827837561

theorem tailTrace_424001 : CollatzResearch.WordTrace tailWord_424001 prefixEnd_424001 217716310987100827837561 := by
  unfold tailWord_424001
  simp only [CollatzResearch.WordTrace]
  refine ⟨15464586936924265450767857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10309724624616176967178571 15464586936924265450767857)
  ·
    refine ⟨11598440202693199088075893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15464586936924265450767857 11598440202693199088075893)
    ·
      refine ⟨1087353769002487414507115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11598440202693199088075893 1087353769002487414507115)
      ·
        refine ⟨1631030653503731121760673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1087353769002487414507115 1631030653503731121760673)
        ·
          refine ⟨1223272990127798341320505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1631030653503731121760673 1223272990127798341320505)
          ·
            refine ⟨917454742595848755990379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1223272990127798341320505 917454742595848755990379)
            ·
              refine ⟨1376182113893773133985569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917454742595848755990379 1376182113893773133985569)
              ·
                refine ⟨1032136585420329850489177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1376182113893773133985569 1032136585420329850489177)
                ·
                  refine ⟨774102439065247387866883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1032136585420329850489177 774102439065247387866883)
                  ·
                    refine ⟨1161153658597871081800325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 774102439065247387866883 1161153658597871081800325)
                    ·
                      refine ⟨217716310987100827837561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1161153658597871081800325 217716310987100827837561)
                      ·
                        rfl

theorem cell23_424001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_424001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424001 prefixEnd_424001 := by exact prefixLift 424001
  have htrace : WordTrace (prefixWord ++ tailWord_424001) baseStart_424001 baseEnd_424001 := by
    simpa [prefixWord, tailWord_424001, baseEnd_424001] using wordTrace_append hprefix tailTrace_424001
  have hstable : (prefixWord ++ tailWord_424001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424001).length < 2 ^ (prefixWord ++ tailWord_424001).sum := by decide
  have hdescent : baseEnd_424001 < baseStart_424001 := by decide
  rcases family_descends (prefixWord ++ tailWord_424001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424007 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 8]
def baseStart_424007 : Nat := 118140960795 + 424007 * 2 ^ 59
def prefixEnd_424007 : Nat := 4983230072969 + 3 ^ 40 * 424007 * 2
def baseEnd_424007 : Nat := 24191043541225311595837

theorem tailTrace_424007 : CollatzResearch.WordTrace tailWord_424007 prefixEnd_424007 24191043541225311595837 := by
  unfold tailWord_424007
  simp only [CollatzResearch.WordTrace]
  refine ⟨15464805774902528475486275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10309870516601685650324183 15464805774902528475486275)
  ·
    refine ⟨23197208662353792713229413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15464805774902528475486275 23197208662353792713229413)
    ·
      refine ⟨4349476624191336133730515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23197208662353792713229413 4349476624191336133730515)
      ·
        refine ⟨6524214936287004200595773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4349476624191336133730515 6524214936287004200595773)
        ·
          refine ⟨2446580601107626575223415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6524214936287004200595773 2446580601107626575223415)
          ·
            refine ⟨3669870901661439862835123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2446580601107626575223415 3669870901661439862835123)
            ·
              refine ⟨5504806352492159794252685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3669870901661439862835123 5504806352492159794252685)
              ·
                refine ⟨2064302382184559922844757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5504806352492159794252685 2064302382184559922844757)
                ·
                  refine ⟨24191043541225311595837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2064302382184559922844757 24191043541225311595837)
                  ·
                    rfl

theorem cell23_424007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 8].length) (baseStart_424007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424007 prefixEnd_424007 := by exact prefixLift 424007
  have htrace : WordTrace (prefixWord ++ tailWord_424007) baseStart_424007 baseEnd_424007 := by
    simpa [prefixWord, tailWord_424007, baseEnd_424007] using wordTrace_append hprefix tailTrace_424007
  have hstable : (prefixWord ++ tailWord_424007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424007).length < 2 ^ (prefixWord ++ tailWord_424007).sum := by decide
  have hdescent : baseEnd_424007 < baseStart_424007 := by decide
  rcases family_descends (prefixWord ++ tailWord_424007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424024 : List Nat := [2, 1, 2, 2, 1, 5, 1, 3, 6]
def baseStart_424024 : Nat := 118140960795 + 424024 * 2 ^ 59
def prefixEnd_424024 : Nat := 4983230072969 + 3 ^ 40 * 424024 * 2
def baseEnd_424024 : Nat := 24192013449128248649995

theorem tailTrace_424024 : CollatzResearch.WordTrace tailWord_424024 prefixEnd_424024 24192013449128248649995 := by
  unfold tailWord_424024
  simp only [CollatzResearch.WordTrace]
  refine ⟨7732712907920470189427563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10310283877227293585903417 7732712907920470189427563)
  ·
    refine ⟨11599069361880705284141345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7732712907920470189427563 11599069361880705284141345)
    ·
      refine ⟨8699302021410528963106009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11599069361880705284141345 8699302021410528963106009)
      ·
        refine ⟨6524476516057896722329507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8699302021410528963106009 6524476516057896722329507)
        ·
          refine ⟨9786714774086845083494261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6524476516057896722329507 9786714774086845083494261)
          ·
            refine ⟨917504510070641726577587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9786714774086845083494261 917504510070641726577587)
            ·
              refine ⟨1376256765105962589866381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917504510070641726577587 1376256765105962589866381)
              ·
                refine ⟨516096286914735971199893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1376256765105962589866381 516096286914735971199893)
                ·
                  refine ⟨24192013449128248649995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 516096286914735971199893 24192013449128248649995)
                  ·
                    rfl

theorem cell23_424024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 6].length) (baseStart_424024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424024 prefixEnd_424024 := by exact prefixLift 424024
  have htrace : WordTrace (prefixWord ++ tailWord_424024) baseStart_424024 baseEnd_424024 := by
    simpa [prefixWord, tailWord_424024, baseEnd_424024] using wordTrace_append hprefix tailTrace_424024
  have hstable : (prefixWord ++ tailWord_424024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424024).length < 2 ^ (prefixWord ++ tailWord_424024).sum := by decide
  have hdescent : baseEnd_424024 < baseStart_424024 := by decide
  rcases family_descends (prefixWord ++ tailWord_424024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424086 : List Nat := [5, 3, 2, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_424086 : Nat := 118140960795 + 424086 * 2 ^ 59
def prefixEnd_424086 : Nat := 4983230072969 + 3 ^ 40 * 424086 * 2
def baseEnd_424086 : Nat := 217759956842732995274671

theorem tailTrace_424086 : CollatzResearch.WordTrace tailWord_424086 prefixEnd_424086 217759956842732995274671 := by
  unfold tailWord_424086
  simp only [CollatzResearch.WordTrace]
  refine ⟨966730446351020310475757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10311791427744216645074741 966730446351020310475757)
  ·
    refine ⟨362523917381632616428409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 966730446351020310475757 362523917381632616428409)
    ·
      refine ⟨271892938036224462321307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362523917381632616428409 271892938036224462321307)
      ·
        refine ⟨407839407054336693481961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271892938036224462321307 407839407054336693481961)
        ·
          refine ⟨305879555290752520111471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407839407054336693481961 305879555290752520111471)
          ·
            refine ⟨458819332936128780167207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305879555290752520111471 458819332936128780167207)
            ·
              refine ⟨688228999404193170250811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458819332936128780167207 688228999404193170250811)
              ·
                refine ⟨1032343499106289755376217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 688228999404193170250811 1032343499106289755376217)
                ·
                  refine ⟨774257624329717316532163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1032343499106289755376217 774257624329717316532163)
                  ·
                    refine ⟨1161386436494575974798245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 774257624329717316532163 1161386436494575974798245)
                    ·
                      refine ⟨217759956842732995274671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1161386436494575974798245 217759956842732995274671)
                      ·
                        rfl

theorem cell23_424086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_424086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424086 prefixEnd_424086 := by exact prefixLift 424086
  have htrace : WordTrace (prefixWord ++ tailWord_424086) baseStart_424086 baseEnd_424086 := by
    simpa [prefixWord, tailWord_424086, baseEnd_424086] using wordTrace_append hprefix tailTrace_424086
  have hstable : (prefixWord ++ tailWord_424086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424086).length < 2 ^ (prefixWord ++ tailWord_424086).sum := by decide
  have hdescent : baseEnd_424086 < baseStart_424086 := by decide
  rcases family_descends (prefixWord ++ tailWord_424086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424095 : List Nat := [1, 1, 2, 6, 1, 3, 1, 1, 2, 3, 2]
def baseStart_424095 : Nat := 118140960795 + 424095 * 2 ^ 59
def prefixEnd_424095 : Nat := 4983230072969 + 3 ^ 40 * 424095 * 2
def baseEnd_424095 : Nat := 217764578168623460062129

theorem tailTrace_424095 : CollatzResearch.WordTrace tailWord_424095 prefixEnd_424095 217764578168623460062129 := by
  unfold tailWord_424095
  simp only [CollatzResearch.WordTrace]
  refine ⟨15468015398583719504689739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10312010265722479669793159 15468015398583719504689739)
  ·
    refine ⟨23202023097875579257034609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15468015398583719504689739 23202023097875579257034609)
    ·
      refine ⟨17401517323406684442775957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23202023097875579257034609 17401517323406684442775957)
      ·
        refine ⟨815696124534688333255123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17401517323406684442775957 815696124534688333255123)
        ·
          refine ⟨1223544186802032499882685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 815696124534688333255123 1223544186802032499882685)
          ·
            refine ⟨458829070050762187456007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1223544186802032499882685 458829070050762187456007)
            ·
              refine ⟨688243605076143281184011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458829070050762187456007 688243605076143281184011)
              ·
                refine ⟨1032365407614214921776017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 688243605076143281184011 1032365407614214921776017)
                ·
                  refine ⟨774274055710661191332013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1032365407614214921776017 774274055710661191332013)
                  ·
                    refine ⟨290352770891497946749505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 774274055710661191332013 290352770891497946749505)
                    ·
                      refine ⟨217764578168623460062129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 290352770891497946749505 217764578168623460062129)
                      ·
                        rfl

theorem cell23_424095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_424095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424095 prefixEnd_424095 := by exact prefixLift 424095
  have htrace : WordTrace (prefixWord ++ tailWord_424095) baseStart_424095 baseEnd_424095 := by
    simpa [prefixWord, tailWord_424095, baseEnd_424095] using wordTrace_append hprefix tailTrace_424095
  have hstable : (prefixWord ++ tailWord_424095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424095).length < 2 ^ (prefixWord ++ tailWord_424095).sum := by decide
  have hdescent : baseEnd_424095 < baseStart_424095 := by decide
  rcases family_descends (prefixWord ++ tailWord_424095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424107 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 7]
def baseStart_424107 : Nat := 118140960795 + 424107 * 2 ^ 59
def prefixEnd_424107 : Nat := 4983230072969 + 3 ^ 40 * 424107 * 2
def baseEnd_424107 : Nat := 217770739936477413112073

theorem tailTrace_424107 : CollatzResearch.WordTrace tailWord_424107 prefixEnd_424107 217770739936477413112073 := by
  unfold tailWord_424107
  simp only [CollatzResearch.WordTrace]
  refine ⟨15468453074540245554126575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10312302049693497036084383 15468453074540245554126575)
  ·
    refine ⟨23202679611810368331189863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15468453074540245554126575 23202679611810368331189863)
    ·
      refine ⟨34804019417715552496784795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23202679611810368331189863 34804019417715552496784795)
      ·
        refine ⟨52206029126573328745177193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34804019417715552496784795 52206029126573328745177193)
        ·
          refine ⟨39154521844929996558882895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52206029126573328745177193 39154521844929996558882895)
          ·
            refine ⟨58731782767394994838324343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39154521844929996558882895 58731782767394994838324343)
            ·
              refine ⟨88097674151092492257486515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58731782767394994838324343 88097674151092492257486515)
              ·
                refine ⟨132146511226638738386229773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88097674151092492257486515 132146511226638738386229773)
                ·
                  refine ⟨49554941709989526894836165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132146511226638738386229773 49554941709989526894836165)
                  ·
                    refine ⟨9291551570623036292781781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49554941709989526894836165 9291551570623036292781781)
                    ·
                      refine ⟨217770739936477413112073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9291551570623036292781781 217770739936477413112073)
                      ·
                        rfl

theorem cell23_424107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 7].length) (baseStart_424107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424107 prefixEnd_424107 := by exact prefixLift 424107
  have htrace : WordTrace (prefixWord ++ tailWord_424107) baseStart_424107 baseEnd_424107 := by
    simpa [prefixWord, tailWord_424107, baseEnd_424107] using wordTrace_append hprefix tailTrace_424107
  have hstable : (prefixWord ++ tailWord_424107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424107).length < 2 ^ (prefixWord ++ tailWord_424107).sum := by decide
  have hdescent : baseEnd_424107 < baseStart_424107 := by decide
  rcases family_descends (prefixWord ++ tailWord_424107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424154 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5]
def baseStart_424154 : Nat := 118140960795 + 424154 * 2 ^ 59
def prefixEnd_424154 : Nat := 4983230072969 + 3 ^ 40 * 424154 * 2
def baseEnd_424154 : Nat := 217794873527238729224357

theorem tailTrace_424154 : CollatzResearch.WordTrace tailWord_424154 prefixEnd_424154 217794873527238729224357 := by
  unfold tailWord_424154
  simp only [CollatzResearch.WordTrace]
  refine ⟨3867541826342493145271879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10313444870246648387391677 3867541826342493145271879)
  ·
    refine ⟨5801312739513739717907819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3867541826342493145271879 5801312739513739717907819)
    ·
      refine ⟨8701969109270609576861729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5801312739513739717907819 8701969109270609576861729)
      ·
        refine ⟨6526476831952957182646297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8701969109270609576861729 6526476831952957182646297)
        ·
          refine ⟨4894857623964717886984723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6526476831952957182646297 4894857623964717886984723)
          ·
            refine ⟨7342286435947076830477085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4894857623964717886984723 7342286435947076830477085)
            ·
              refine ⟨2753357413480153811428907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7342286435947076830477085 2753357413480153811428907)
              ·
                refine ⟨4130036120220230717143361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753357413480153811428907 4130036120220230717143361)
                ·
                  refine ⟨3097527090165173037857521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4130036120220230717143361 3097527090165173037857521)
                  ·
                    refine ⟨2323145317623879778393141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3097527090165173037857521 2323145317623879778393141)
                    ·
                      refine ⟨217794873527238729224357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2323145317623879778393141 217794873527238729224357)
                      ·
                        rfl

theorem cell23_424154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_424154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424154 prefixEnd_424154 := by exact prefixLift 424154
  have htrace : WordTrace (prefixWord ++ tailWord_424154) baseStart_424154 baseEnd_424154 := by
    simpa [prefixWord, tailWord_424154, baseEnd_424154] using wordTrace_append hprefix tailTrace_424154
  have hstable : (prefixWord ++ tailWord_424154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424154).length < 2 ^ (prefixWord ++ tailWord_424154).sum := by decide
  have hdescent : baseEnd_424154 < baseStart_424154 := by decide
  rcases family_descends (prefixWord ++ tailWord_424154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424162 : List Nat := [3, 3, 4, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_424162 : Nat := 118140960795 + 424162 * 2 ^ 59
def prefixEnd_424162 : Nat := 4983230072969 + 3 ^ 40 * 424162 * 2
def baseEnd_424162 : Nat := 217798981372474697924321

theorem tailTrace_424162 : CollatzResearch.WordTrace tailWord_424162 prefixEnd_424162 217798981372474697924321 := by
  unfold tailWord_424162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3867614772335247486844685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10313639392893993298252493 3867614772335247486844685)
  ·
    refine ⟨1450355539625717807566757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3867614772335247486844685 1450355539625717807566757)
    ·
      refine ⟨271941663679822088918767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1450355539625717807566757 271941663679822088918767)
      ·
        refine ⟨407912495519733133378151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271941663679822088918767 407912495519733133378151)
        ·
          refine ⟨611868743279599700067227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407912495519733133378151 611868743279599700067227)
          ·
            refine ⟨917803114919399550100841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611868743279599700067227 917803114919399550100841)
            ·
              refine ⟨688352336189549662575631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 917803114919399550100841 688352336189549662575631)
              ·
                refine ⟨1032528504284324493863447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 688352336189549662575631 1032528504284324493863447)
                ·
                  refine ⟨1548792756426486740795171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1032528504284324493863447 1548792756426486740795171)
                  ·
                    refine ⟨2323189134639730111192757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1548792756426486740795171 2323189134639730111192757)
                    ·
                      refine ⟨217798981372474697924321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2323189134639730111192757 217798981372474697924321)
                      ·
                        rfl

theorem cell23_424162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_424162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424162 prefixEnd_424162 := by exact prefixLift 424162
  have htrace : WordTrace (prefixWord ++ tailWord_424162) baseStart_424162 baseEnd_424162 := by
    simpa [prefixWord, tailWord_424162, baseEnd_424162] using wordTrace_append hprefix tailTrace_424162
  have hstable : (prefixWord ++ tailWord_424162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424162).length < 2 ^ (prefixWord ++ tailWord_424162).sum := by decide
  have hdescent : baseEnd_424162 < baseStart_424162 := by decide
  rcases family_descends (prefixWord ++ tailWord_424162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424164 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 1, 5, 4]
def baseStart_424164 : Nat := 118140960795 + 424164 * 2 ^ 59
def prefixEnd_424164 : Nat := 4983230072969 + 3 ^ 40 * 424164 * 2
def baseEnd_424164 : Nat := 217800008333783690099311

theorem tailTrace_424164 : CollatzResearch.WordTrace tailWord_424164 prefixEnd_424164 217800008333783690099311 := by
  unfold tailWord_424164
  simp only [CollatzResearch.WordTrace]
  refine ⟨7735266017666872144475773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10313688023555829525967697 7735266017666872144475773)
  ·
    refine ⟨2900724756625077054178415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7735266017666872144475773 2900724756625077054178415)
    ·
      refine ⟨4351087134937615581267623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2900724756625077054178415 4351087134937615581267623)
      ·
        refine ⟨6526630702406423371901435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4351087134937615581267623 6526630702406423371901435)
        ·
          refine ⟨9789946053609635057852153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6526630702406423371901435 9789946053609635057852153)
          ·
            refine ⟨7342459540207226293389115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9789946053609635057852153 7342459540207226293389115)
            ·
              refine ⟨11013689310310839440083673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7342459540207226293389115 11013689310310839440083673)
              ·
                refine ⟨8260266982733129580062755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11013689310310839440083673 8260266982733129580062755)
                ·
                  refine ⟨12390400474099694370094133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8260266982733129580062755 12390400474099694370094133)
                  ·
                    refine ⟨1161600044446846347196325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12390400474099694370094133 1161600044446846347196325)
                    ·
                      refine ⟨217800008333783690099311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1161600044446846347196325 217800008333783690099311)
                      ·
                        rfl

theorem cell23_424164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_424164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424164 prefixEnd_424164 := by exact prefixLift 424164
  have htrace : WordTrace (prefixWord ++ tailWord_424164) baseStart_424164 baseEnd_424164 := by
    simpa [prefixWord, tailWord_424164, baseEnd_424164] using wordTrace_append hprefix tailTrace_424164
  have hstable : (prefixWord ++ tailWord_424164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424164).length < 2 ^ (prefixWord ++ tailWord_424164).sum := by decide
  have hdescent : baseEnd_424164 < baseStart_424164 := by decide
  rcases family_descends (prefixWord ++ tailWord_424164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424204 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 9]
def baseStart_424204 : Nat := 118140960795 + 424204 * 2 ^ 59
def prefixEnd_424204 : Nat := 4983230072969 + 3 ^ 40 * 424204 * 2
def baseEnd_424204 : Nat := 24202283062218170399903

theorem tailTrace_424204 : CollatzResearch.WordTrace tailWord_424204 prefixEnd_424204 24202283062218170399903 := by
  unfold tailWord_424204
  simp only [CollatzResearch.WordTrace]
  refine ⟨7735995477594415560203833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10314660636792554080271777 7735995477594415560203833)
  ·
    refine ⟨5801996608195811670152875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7735995477594415560203833 5801996608195811670152875)
    ·
      refine ⟨8702994912293717505229313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5801996608195811670152875 8702994912293717505229313)
      ·
        refine ⟨6527246184220288128921985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8702994912293717505229313 6527246184220288128921985)
        ·
          refine ⟨4895434638165216096691489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6527246184220288128921985 4895434638165216096691489)
          ·
            refine ⟨3671575978623912072518617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4895434638165216096691489 3671575978623912072518617)
            ·
              refine ⟨2753681983967934054388963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3671575978623912072518617 2753681983967934054388963)
              ·
                refine ⟨4130522975951901081583445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753681983967934054388963 4130522975951901081583445)
                ·
                  refine ⟨24202283062218170399903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4130522975951901081583445 24202283062218170399903)
                  ·
                    rfl

theorem cell23_424204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 9].length) (baseStart_424204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424204 prefixEnd_424204 := by exact prefixLift 424204
  have htrace : WordTrace (prefixWord ++ tailWord_424204) baseStart_424204 baseEnd_424204 := by
    simpa [prefixWord, tailWord_424204, baseEnd_424204] using wordTrace_append hprefix tailTrace_424204
  have hstable : (prefixWord ++ tailWord_424204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424204).length < 2 ^ (prefixWord ++ tailWord_424204).sum := by decide
  have hdescent : baseEnd_424204 < baseStart_424204 := by decide
  rcases family_descends (prefixWord ++ tailWord_424204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424271 : List Nat := [1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 4]
def baseStart_424271 : Nat := 118140960795 + 424271 * 2 ^ 59
def prefixEnd_424271 : Nat := 4983230072969 + 3 ^ 40 * 424271 * 2
def baseEnd_424271 : Nat := 217854950763814771461319

theorem tailTrace_424271 : CollatzResearch.WordTrace tailWord_424271 prefixEnd_424271 217854950763814771461319 := by
  unfold tailWord_424271
  simp only [CollatzResearch.WordTrace]
  refine ⟨15474434645946101563096667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10316289763964067708731111 15474434645946101563096667)
  ·
    refine ⟨23211651968919152344645001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15474434645946101563096667 23211651968919152344645001)
    ·
      refine ⟨17408738976689364258483751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23211651968919152344645001 17408738976689364258483751)
      ·
        refine ⟨26113108465034046387725627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17408738976689364258483751 26113108465034046387725627)
        ·
          refine ⟨39169662697551069581588441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26113108465034046387725627 39169662697551069581588441)
          ·
            refine ⟨29377247023163302186191331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39169662697551069581588441 29377247023163302186191331)
            ·
              refine ⟨44065870534744953279286997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29377247023163302186191331 44065870534744953279286997)
              ·
                refine ⟨1032793840658084842483289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 44065870534744953279286997 1032793840658084842483289)
                ·
                  refine ⟨774595380493563631862467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1032793840658084842483289 774595380493563631862467)
                  ·
                    refine ⟨1161893070740345447793701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 774595380493563631862467 1161893070740345447793701)
                    ·
                      refine ⟨217854950763814771461319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1161893070740345447793701 217854950763814771461319)
                      ·
                        rfl

theorem cell23_424271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 4].length) (baseStart_424271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424271 prefixEnd_424271 := by exact prefixLift 424271
  have htrace : WordTrace (prefixWord ++ tailWord_424271) baseStart_424271 baseEnd_424271 := by
    simpa [prefixWord, tailWord_424271, baseEnd_424271] using wordTrace_append hprefix tailTrace_424271
  have hstable : (prefixWord ++ tailWord_424271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424271).length < 2 ^ (prefixWord ++ tailWord_424271).sum := by decide
  have hdescent : baseEnd_424271 < baseStart_424271 := by decide
  rcases family_descends (prefixWord ++ tailWord_424271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424281 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 7, 4]
def baseStart_424281 : Nat := 118140960795 + 424281 * 2 ^ 59
def prefixEnd_424281 : Nat := 4983230072969 + 3 ^ 40 * 424281 * 2
def baseEnd_424281 : Nat := 72620028523453244112091

theorem tailTrace_424281 : CollatzResearch.WordTrace tailWord_424281 prefixEnd_424281 72620028523453244112091 := by
  unfold tailWord_424281
  simp only [CollatzResearch.WordTrace]
  refine ⟨15474799375909873270960697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10316532917273248847307131 15474799375909873270960697)
  ·
    refine ⟨11606099531932404953220523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15474799375909873270960697 11606099531932404953220523)
    ·
      refine ⟨17409149297898607429830785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11606099531932404953220523 17409149297898607429830785)
      ·
        refine ⟨13056861973423955572373089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17409149297898607429830785 13056861973423955572373089)
        ·
          refine ⟨9792646480067966679279817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13056861973423955572373089 9792646480067966679279817)
          ·
            refine ⟨7344484860050975009459863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9792646480067966679279817 7344484860050975009459863)
            ·
              refine ⟨11016727290076462514189795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7344484860050975009459863 11016727290076462514189795)
              ·
                refine ⟨16525090935114693771284693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11016727290076462514189795 16525090935114693771284693)
                ·
                  refine ⟨387306818791750635264485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16525090935114693771284693 387306818791750635264485)
                  ·
                    refine ⟨72620028523453244112091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 387306818791750635264485 72620028523453244112091)
                    ·
                      rfl

theorem cell23_424281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 4].length) (baseStart_424281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424281 prefixEnd_424281 := by exact prefixLift 424281
  have htrace : WordTrace (prefixWord ++ tailWord_424281) baseStart_424281 baseEnd_424281 := by
    simpa [prefixWord, tailWord_424281, baseEnd_424281] using wordTrace_append hprefix tailTrace_424281
  have hstable : (prefixWord ++ tailWord_424281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424281).length < 2 ^ (prefixWord ++ tailWord_424281).sum := by decide
  have hdescent : baseEnd_424281 < baseStart_424281 := by decide
  rcases family_descends (prefixWord ++ tailWord_424281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424301 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_424301 : Nat := 118140960795 + 424301 * 2 ^ 59
def prefixEnd_424301 : Nat := 4983230072969 + 3 ^ 40 * 424301 * 2
def baseEnd_424301 : Nat := 217870355183449654086181

theorem tailTrace_424301 : CollatzResearch.WordTrace tailWord_424301 prefixEnd_424301 217870355183449654086181 := by
  unfold tailWord_424301
  simp only [CollatzResearch.WordTrace]
  refine ⟨15475528835837416686688757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10317019223891611124459171 15475528835837416686688757)
  ·
    refine ⟨1450830828359757814377071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15475528835837416686688757 1450830828359757814377071)
    ·
      refine ⟨2176246242539636721565607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1450830828359757814377071 2176246242539636721565607)
      ·
        refine ⟨3264369363809455082348411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2176246242539636721565607 3264369363809455082348411)
        ·
          refine ⟨4896554045714182623522617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3264369363809455082348411 4896554045714182623522617)
          ·
            refine ⟨3672415534285636967641963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4896554045714182623522617 3672415534285636967641963)
            ·
              refine ⟨5508623301428455451462945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3672415534285636967641963 5508623301428455451462945)
              ·
                refine ⟨4131467476071341588597209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5508623301428455451462945 4131467476071341588597209)
                ·
                  refine ⟨3098600607053506191447907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4131467476071341588597209 3098600607053506191447907)
                  ·
                    refine ⟨4647900910580259287171861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3098600607053506191447907 4647900910580259287171861)
                    ·
                      refine ⟨217870355183449654086181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4647900910580259287171861 217870355183449654086181)
                      ·
                        rfl

theorem cell23_424301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_424301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424301 prefixEnd_424301 := by exact prefixLift 424301
  have htrace : WordTrace (prefixWord ++ tailWord_424301) baseStart_424301 baseEnd_424301 := by
    simpa [prefixWord, tailWord_424301, baseEnd_424301] using wordTrace_append hprefix tailTrace_424301
  have hstable : (prefixWord ++ tailWord_424301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424301).length < 2 ^ (prefixWord ++ tailWord_424301).sum := by decide
  have hdescent : baseEnd_424301 < baseStart_424301 := by decide
  rcases family_descends (prefixWord ++ tailWord_424301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424332 : List Nat := [2, 2, 1, 2, 1, 6, 1, 3, 1, 4]
def baseStart_424332 : Nat := 118140960795 + 424332 * 2 ^ 59
def prefixEnd_424332 : Nat := 4983230072969 + 3 ^ 40 * 424332 * 2
def baseEnd_424332 : Nat := 72628757694579677599513

theorem tailTrace_424332 : CollatzResearch.WordTrace tailWord_424332 prefixEnd_424332 72628757694579677599513 := by
  unfold tailWord_424332
  simp only [CollatzResearch.WordTrace]
  refine ⟨7738329749362554490533625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10317772999150072654044833 7738329749362554490533625)
  ·
    refine ⟨5803747312021915867900219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7738329749362554490533625 5803747312021915867900219)
    ·
      refine ⟨8705620968032873801850329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5803747312021915867900219 8705620968032873801850329)
      ·
        refine ⟨6529215726024655351387747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8705620968032873801850329 6529215726024655351387747)
        ·
          refine ⟨9793823589036983027081621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6529215726024655351387747 9793823589036983027081621)
          ·
            refine ⟨459085480736108579394451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9793823589036983027081621 459085480736108579394451)
            ·
              refine ⟨688628221104162869091677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459085480736108579394451 688628221104162869091677)
              ·
                refine ⟨258235582914061075909379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 688628221104162869091677 258235582914061075909379)
                ·
                  refine ⟨387353374371091613864069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258235582914061075909379 387353374371091613864069)
                  ·
                    refine ⟨72628757694579677599513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 387353374371091613864069 72628757694579677599513)
                    ·
                      rfl

theorem cell23_424332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 1, 4].length) (baseStart_424332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424332 prefixEnd_424332 := by exact prefixLift 424332
  have htrace : WordTrace (prefixWord ++ tailWord_424332) baseStart_424332 baseEnd_424332 := by
    simpa [prefixWord, tailWord_424332, baseEnd_424332] using wordTrace_append hprefix tailTrace_424332
  have hstable : (prefixWord ++ tailWord_424332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424332).length < 2 ^ (prefixWord ++ tailWord_424332).sum := by decide
  have hdescent : baseEnd_424332 < baseStart_424332 := by decide
  rcases family_descends (prefixWord ++ tailWord_424332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424341 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 5, 5]
def baseStart_424341 : Nat := 118140960795 + 424341 * 2 ^ 59
def prefixEnd_424341 : Nat := 4983230072969 + 3 ^ 40 * 424341 * 2
def baseEnd_424341 : Nat := 72630298136543165861999

theorem tailTrace_424341 : CollatzResearch.WordTrace tailWord_424341 prefixEnd_424341 72630298136543165861999 := by
  unfold tailWord_424341
  simp only [CollatzResearch.WordTrace]
  refine ⟨15476987755692503518144877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10317991837128335678763251 15476987755692503518144877)
  ·
    refine ⟨5803870408384688819304329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15476987755692503518144877 5803870408384688819304329)
    ·
      refine ⟨4352902806288516614478247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5803870408384688819304329 4352902806288516614478247)
      ·
        refine ⟨6529354209432774921717371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4352902806288516614478247 6529354209432774921717371)
        ·
          refine ⟨9794031314149162382576057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6529354209432774921717371 9794031314149162382576057)
          ·
            refine ⟨7345523485611871786932043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9794031314149162382576057 7345523485611871786932043)
            ·
              refine ⟨11018285228417807680398065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7345523485611871786932043 11018285228417807680398065)
              ·
                refine ⟨8263713921313355760298549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11018285228417807680398065 8263713921313355760298549)
                ·
                  refine ⟨774723180123127102527989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8263713921313355760298549 774723180123127102527989)
                  ·
                    refine ⟨72630298136543165861999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 774723180123127102527989 72630298136543165861999)
                    ·
                      rfl

theorem cell23_424341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_424341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424341 prefixEnd_424341 := by exact prefixLift 424341
  have htrace : WordTrace (prefixWord ++ tailWord_424341) baseStart_424341 baseEnd_424341 := by
    simpa [prefixWord, tailWord_424341, baseEnd_424341] using wordTrace_append hprefix tailTrace_424341
  have hstable : (prefixWord ++ tailWord_424341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424341).length < 2 ^ (prefixWord ++ tailWord_424341).sum := by decide
  have hdescent : baseEnd_424341 < baseStart_424341 := by decide
  rcases family_descends (prefixWord ++ tailWord_424341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424349 : List Nat := [1, 4, 2, 1, 4, 1, 3, 2, 1, 4]
def baseStart_424349 : Nat := 118140960795 + 424349 * 2 ^ 59
def prefixEnd_424349 : Nat := 4983230072969 + 3 ^ 40 * 424349 * 2
def baseEnd_424349 : Nat := 72631667418288488761987

theorem tailTrace_424349 : CollatzResearch.WordTrace tailWord_424349 prefixEnd_424349 72631667418288488761987 := by
  unfold tailWord_424349
  simp only [CollatzResearch.WordTrace]
  refine ⟨15477279539663520884436101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10318186359775680589624067 15477279539663520884436101)
  ·
    refine ⟨2901989913686910165831769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15477279539663520884436101 2901989913686910165831769)
    ·
      refine ⟨2176492435265182624373827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2901989913686910165831769 2176492435265182624373827)
      ·
        refine ⟨3264738652897773936560741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2176492435265182624373827 3264738652897773936560741)
        ·
          refine ⟨612138497418332613105139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3264738652897773936560741 612138497418332613105139)
          ·
            refine ⟨918207746127498919657709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612138497418332613105139 918207746127498919657709)
            ·
              refine ⟨344327904797812094871641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 918207746127498919657709 344327904797812094871641)
              ·
                refine ⟨258245928598359071153731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 344327904797812094871641 258245928598359071153731)
                ·
                  refine ⟨387368892897538606730597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258245928598359071153731 387368892897538606730597)
                  ·
                    refine ⟨72631667418288488761987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 387368892897538606730597 72631667418288488761987)
                    ·
                      rfl

theorem cell23_424349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_424349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424349 prefixEnd_424349 := by exact prefixLift 424349
  have htrace : WordTrace (prefixWord ++ tailWord_424349) baseStart_424349 baseEnd_424349 := by
    simpa [prefixWord, tailWord_424349, baseEnd_424349] using wordTrace_append hprefix tailTrace_424349
  have hstable : (prefixWord ++ tailWord_424349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424349).length < 2 ^ (prefixWord ++ tailWord_424349).sum := by decide
  have hdescent : baseEnd_424349 < baseStart_424349 := by decide
  rcases family_descends (prefixWord ++ tailWord_424349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424355 : List Nat := [1, 1, 1, 4, 1, 4, 3, 1, 3, 1, 3]
def baseStart_424355 : Nat := 118140960795 + 424355 * 2 ^ 59
def prefixEnd_424355 : Nat := 4983230072969 + 3 ^ 40 * 424355 * 2
def baseEnd_424355 : Nat := 217898083138792442810933

theorem tailTrace_424355 : CollatzResearch.WordTrace tailWord_424355 prefixEnd_424355 217898083138792442810933 := by
  unfold tailWord_424355
  simp only [CollatzResearch.WordTrace]
  refine ⟨15477498377641783909154519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10318332251761189272769679 15477498377641783909154519)
  ·
    refine ⟨23216247566462675863731779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15477498377641783909154519 23216247566462675863731779)
    ·
      refine ⟨34824371349694013795597669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23216247566462675863731779 34824371349694013795597669)
      ·
        refine ⟨6529569628067627586674563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34824371349694013795597669 6529569628067627586674563)
        ·
          refine ⟨9794354442101441380011845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6529569628067627586674563 9794354442101441380011845)
          ·
            refine ⟨1836441457894020258752221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9794354442101441380011845 1836441457894020258752221)
            ·
              refine ⟨688665546710257597032083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1836441457894020258752221 688665546710257597032083)
              ·
                refine ⟨1032998320065386395548125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 688665546710257597032083 1032998320065386395548125)
                ·
                  refine ⟨387374370024519898330547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1032998320065386395548125 387374370024519898330547)
                  ·
                    refine ⟨581061555036779847495821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 387374370024519898330547 581061555036779847495821)
                    ·
                      refine ⟨217898083138792442810933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 581061555036779847495821 217898083138792442810933)
                      ·
                        rfl

theorem cell23_424355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_424355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424355 prefixEnd_424355 := by exact prefixLift 424355
  have htrace : WordTrace (prefixWord ++ tailWord_424355) baseStart_424355 baseEnd_424355 := by
    simpa [prefixWord, tailWord_424355, baseEnd_424355] using wordTrace_append hprefix tailTrace_424355
  have hstable : (prefixWord ++ tailWord_424355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424355).length < 2 ^ (prefixWord ++ tailWord_424355).sum := by decide
  have hdescent : baseEnd_424355 < baseStart_424355 := by decide
  rcases family_descends (prefixWord ++ tailWord_424355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424375 : List Nat := [1, 1, 3, 1, 3, 5, 1, 2, 1, 5]
def baseStart_424375 : Nat := 118140960795 + 424375 * 2 ^ 59
def prefixEnd_424375 : Nat := 4983230072969 + 3 ^ 40 * 424375 * 2
def baseEnd_424375 : Nat := 72636117583960788186947

theorem tailTrace_424375 : CollatzResearch.WordTrace tailWord_424375 prefixEnd_424375 72636117583960788186947 := by
  unfold tailWord_424375
  simp only [CollatzResearch.WordTrace]
  refine ⟨15478227837569327324882579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10318818558379551549921719 15478227837569327324882579)
  ·
    refine ⟨23217341756353990987323869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15478227837569327324882579 23217341756353990987323869)
    ·
      refine ⟨8706503158632746620246451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23217341756353990987323869 8706503158632746620246451)
      ·
        refine ⟨13059754737949119930369677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8706503158632746620246451 13059754737949119930369677)
        ·
          refine ⟨4897408026730919973888629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13059754737949119930369677 4897408026730919973888629)
          ·
            refine ⟨459132002506023747552059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4897408026730919973888629 459132002506023747552059)
            ·
              refine ⟨688698003759035621328089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459132002506023747552059 688698003759035621328089)
              ·
                refine ⟨516523502819276715996067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 688698003759035621328089 516523502819276715996067)
                ·
                  refine ⟨774785254228915073994101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 516523502819276715996067 774785254228915073994101)
                  ·
                    refine ⟨72636117583960788186947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 774785254228915073994101 72636117583960788186947)
                    ·
                      rfl

theorem cell23_424375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 5].length) (baseStart_424375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424375 prefixEnd_424375 := by exact prefixLift 424375
  have htrace : WordTrace (prefixWord ++ tailWord_424375) baseStart_424375 baseEnd_424375 := by
    simpa [prefixWord, tailWord_424375, baseEnd_424375] using wordTrace_append hprefix tailTrace_424375
  have hstable : (prefixWord ++ tailWord_424375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424375).length < 2 ^ (prefixWord ++ tailWord_424375).sum := by decide
  have hdescent : baseEnd_424375 < baseStart_424375 := by decide
  rcases family_descends (prefixWord ++ tailWord_424375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424378 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2]
def baseStart_424378 : Nat := 118140960795 + 424378 * 2 ^ 59
def prefixEnd_424378 : Nat := 4983230072969 + 3 ^ 40 * 424378 * 2
def baseEnd_424378 : Nat := 217909893193845852823327

theorem tailTrace_424378 : CollatzResearch.WordTrace tailWord_424378 prefixEnd_424378 217909893193845852823327 := by
  unfold tailWord_424378
  simp only [CollatzResearch.WordTrace]
  refine ⟨3869584314139614709310447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10318891504372305891494525 3869584314139614709310447)
  ·
    refine ⟨5804376471209422063965671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3869584314139614709310447 5804376471209422063965671)
    ·
      refine ⟨8706564706814133095948507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5804376471209422063965671 8706564706814133095948507)
      ·
        refine ⟨13059847060221199643922761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8706564706814133095948507 13059847060221199643922761)
        ·
          refine ⟨9794885295165899732942071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13059847060221199643922761 9794885295165899732942071)
          ·
            refine ⟨14692327942748849599413107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9794885295165899732942071 14692327942748849599413107)
            ·
              refine ⟨22038491914123274399119661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14692327942748849599413107 22038491914123274399119661)
              ·
                refine ⟨8264434467796227899669873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22038491914123274399119661 8264434467796227899669873)
                ·
                  refine ⟨6198325850847170924752405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8264434467796227899669873 6198325850847170924752405)
                  ·
                    refine ⟨290546524258461137097769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6198325850847170924752405 290546524258461137097769)
                    ·
                      refine ⟨217909893193845852823327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 290546524258461137097769 217909893193845852823327)
                      ·
                        rfl

theorem cell23_424378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2].length) (baseStart_424378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424378 prefixEnd_424378 := by exact prefixLift 424378
  have htrace : WordTrace (prefixWord ++ tailWord_424378) baseStart_424378 baseEnd_424378 := by
    simpa [prefixWord, tailWord_424378, baseEnd_424378] using wordTrace_append hprefix tailTrace_424378
  have hstable : (prefixWord ++ tailWord_424378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424378).length < 2 ^ (prefixWord ++ tailWord_424378).sum := by decide
  have hdescent : baseEnd_424378 < baseStart_424378 := by decide
  rcases family_descends (prefixWord ++ tailWord_424378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424405 : List Nat := [1, 3, 2, 3, 1, 2, 1, 4, 2, 4]
def baseStart_424405 : Nat := 118140960795 + 424405 * 2 ^ 59
def prefixEnd_424405 : Nat := 4983230072969 + 3 ^ 40 * 424405 * 2
def baseEnd_424405 : Nat := 72641252390505749061901

theorem tailTrace_424405 : CollatzResearch.WordTrace tailWord_424405 prefixEnd_424405 72641252390505749061901 := by
  unfold tailWord_424405
  simp only [CollatzResearch.WordTrace]
  refine ⟨15479322027460642448474669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10319548018307094965649779 15479322027460642448474669)
  ·
    refine ⟨5804745760297740918178001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15479322027460642448474669 5804745760297740918178001)
    ·
      refine ⟨4353559320223305688633501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5804745760297740918178001 4353559320223305688633501)
      ·
        refine ⟨1632584745083739633237563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4353559320223305688633501 1632584745083739633237563)
        ·
          refine ⟨2448877117625609449856345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1632584745083739633237563 2448877117625609449856345)
          ·
            refine ⟨1836657838219207087392259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2448877117625609449856345 1836657838219207087392259)
            ·
              refine ⟨2754986757328810631088389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1836657838219207087392259 2754986757328810631088389)
              ·
                refine ⟨516560016999151993329073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2754986757328810631088389 516560016999151993329073)
                ·
                  refine ⟨387420012749363994996805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 516560016999151993329073 387420012749363994996805)
                  ·
                    refine ⟨72641252390505749061901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 387420012749363994996805 72641252390505749061901)
                    ·
                      rfl

theorem cell23_424405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_424405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424405 prefixEnd_424405 := by exact prefixLift 424405
  have htrace : WordTrace (prefixWord ++ tailWord_424405) baseStart_424405 baseEnd_424405 := by
    simpa [prefixWord, tailWord_424405, baseEnd_424405] using wordTrace_append hprefix tailTrace_424405
  have hstable : (prefixWord ++ tailWord_424405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424405).length < 2 ^ (prefixWord ++ tailWord_424405).sum := by decide
  have hdescent : baseEnd_424405 < baseStart_424405 := by decide
  rcases family_descends (prefixWord ++ tailWord_424405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424429 : List Nat := [1, 5, 1, 3, 1, 2, 1, 2, 3, 2, 2]
def baseStart_424429 : Nat := 118140960795 + 424429 * 2 ^ 59
def prefixEnd_424429 : Nat := 4983230072969 + 3 ^ 40 * 424429 * 2
def baseEnd_424429 : Nat := 217936080707225153285593

theorem tailTrace_424429 : CollatzResearch.WordTrace tailWord_424429 prefixEnd_424429 217936080707225153285593 := by
  unfold tailWord_424429
  simp only [CollatzResearch.WordTrace]
  refine ⟨15480197379373694547348341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10320131586249129698232227 15480197379373694547348341)
  ·
    refine ⟨1451268504316283863813907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15480197379373694547348341 1451268504316283863813907)
    ·
      refine ⟨2176902756474425795720861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1451268504316283863813907 2176902756474425795720861)
      ·
        refine ⟨816338533677909673395323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2176902756474425795720861 816338533677909673395323)
        ·
          refine ⟨1224507800516864510092985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 816338533677909673395323 1224507800516864510092985)
          ·
            refine ⟨918380850387648382569739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1224507800516864510092985 918380850387648382569739)
            ·
              refine ⟨1377571275581472573854609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 918380850387648382569739 1377571275581472573854609)
              ·
                refine ⟨1033178456686104430390957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1377571275581472573854609 1033178456686104430390957)
                ·
                  refine ⟨387441921257289161396609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1033178456686104430390957 387441921257289161396609)
                  ·
                    refine ⟨290581440942966871047457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 387441921257289161396609 290581440942966871047457)
                    ·
                      refine ⟨217936080707225153285593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 290581440942966871047457 217936080707225153285593)
                      ·
                        rfl

theorem cell23_424429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_424429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424429 prefixEnd_424429 := by exact prefixLift 424429
  have htrace : WordTrace (prefixWord ++ tailWord_424429) baseStart_424429 baseEnd_424429 := by
    simpa [prefixWord, tailWord_424429, baseEnd_424429] using wordTrace_append hprefix tailTrace_424429
  have hstable : (prefixWord ++ tailWord_424429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424429).length < 2 ^ (prefixWord ++ tailWord_424429).sum := by decide
  have hdescent : baseEnd_424429 < baseStart_424429 := by decide
  rcases family_descends (prefixWord ++ tailWord_424429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424431 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 4, 7]
def baseStart_424431 : Nat := 118140960795 + 424431 * 2 ^ 59
def prefixEnd_424431 : Nat := 4983230072969 + 3 ^ 40 * 424431 * 2
def baseEnd_424431 : Nat := 72645702556178048486861

theorem tailTrace_424431 : CollatzResearch.WordTrace tailWord_424431 prefixEnd_424431 72645702556178048486861 := by
  unfold tailWord_424431
  simp only [CollatzResearch.WordTrace]
  refine ⟨15480270325366448888921147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10320180216910965925947431 15480270325366448888921147)
  ·
    refine ⟨23220405488049673333381721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15480270325366448888921147 23220405488049673333381721)
    ·
      refine ⟨17415304116037255000036291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23220405488049673333381721 17415304116037255000036291)
      ·
        refine ⟨26122956174055882500054437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17415304116037255000036291 26122956174055882500054437)
        ·
          refine ⟨4898054282635477968760207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26122956174055882500054437 4898054282635477968760207)
          ·
            refine ⟨7347081423953216953140311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4898054282635477968760207 7347081423953216953140311)
            ·
              refine ⟨11020622135929825429710467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7347081423953216953140311 11020622135929825429710467)
              ·
                refine ⟨16530933203894738144565701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11020622135929825429710467 16530933203894738144565701)
                ·
                  refine ⟨3099549975730263402106069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16530933203894738144565701 3099549975730263402106069)
                  ·
                    refine ⟨72645702556178048486861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3099549975730263402106069 72645702556178048486861)
                    ·
                      rfl

theorem cell23_424431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 7].length) (baseStart_424431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424431 prefixEnd_424431 := by exact prefixLift 424431
  have htrace : WordTrace (prefixWord ++ tailWord_424431) baseStart_424431 baseEnd_424431 := by
    simpa [prefixWord, tailWord_424431, baseEnd_424431] using wordTrace_append hprefix tailTrace_424431
  have hstable : (prefixWord ++ tailWord_424431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424431).length < 2 ^ (prefixWord ++ tailWord_424431).sum := by decide
  have hdescent : baseEnd_424431 < baseStart_424431 := by decide
  rcases family_descends (prefixWord ++ tailWord_424431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424445 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 4, 1, 3]
def baseStart_424445 : Nat := 118140960795 + 424445 * 2 ^ 59
def prefixEnd_424445 : Nat := 4983230072969 + 3 ^ 40 * 424445 * 2
def baseEnd_424445 : Nat := 217944296397697090685519

theorem tailTrace_424445 : CollatzResearch.WordTrace tailWord_424445 prefixEnd_424445 217944296397697090685519 := by
  unfold tailWord_424445
  simp only [CollatzResearch.WordTrace]
  refine ⟨15480780947315729279930789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10320520631543819519953859 15480780947315729279930789)
  ·
    refine ⟨2902646427621699239987023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15480780947315729279930789 2902646427621699239987023)
    ·
      refine ⟨4353969641432548859980535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2902646427621699239987023 4353969641432548859980535)
      ·
        refine ⟨6530954462148823289970803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4353969641432548859980535 6530954462148823289970803)
        ·
          refine ⟨9796431693223234934956205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6530954462148823289970803 9796431693223234934956205)
          ·
            refine ⟨3673661884958713100608577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9796431693223234934956205 3673661884958713100608577)
            ·
              refine ⟨2755246413719034825456433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3673661884958713100608577 2755246413719034825456433)
              ·
                refine ⟨2066434810289276119092325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2755246413719034825456433 2066434810289276119092325)
                ·
                  refine ⟨387456526929239272329811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2066434810289276119092325 387456526929239272329811)
                  ·
                    refine ⟨581184790393858908494717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 387456526929239272329811 581184790393858908494717)
                    ·
                      refine ⟨217944296397697090685519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 581184790393858908494717 217944296397697090685519)
                      ·
                        rfl

theorem cell23_424445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_424445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424445 prefixEnd_424445 := by exact prefixLift 424445
  have htrace : WordTrace (prefixWord ++ tailWord_424445) baseStart_424445 baseEnd_424445 := by
    simpa [prefixWord, tailWord_424445, baseEnd_424445] using wordTrace_append hprefix tailTrace_424445
  have hstable : (prefixWord ++ tailWord_424445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424445).length < 2 ^ (prefixWord ++ tailWord_424445).sum := by decide
  have hdescent : baseEnd_424445 < baseStart_424445 := by decide
  rcases family_descends (prefixWord ++ tailWord_424445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424449 : List Nat := [1, 2, 4, 1, 3, 3, 2, 1, 1, 2, 3]
def baseStart_424449 : Nat := 118140960795 + 424449 * 2 ^ 59
def prefixEnd_424449 : Nat := 4983230072969 + 3 ^ 40 * 424449 * 2
def baseEnd_424449 : Nat := 217946350320315075035501

theorem tailTrace_424449 : CollatzResearch.WordTrace tailWord_424449 prefixEnd_424449 217946350320315075035501 := by
  unfold tailWord_424449
  simp only [CollatzResearch.WordTrace]
  refine ⟨15480926839301237963076401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10320617892867491975384267 15480926839301237963076401)
  ·
    refine ⟨11610695129475928472307301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15480926839301237963076401 11610695129475928472307301)
    ·
      refine ⟨2177005336776736588557619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11610695129475928472307301 2177005336776736588557619)
      ·
        refine ⟨3265508005165104882836429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2177005336776736588557619 3265508005165104882836429)
        ·
          refine ⟨1224565501936914331063661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3265508005165104882836429 1224565501936914331063661)
          ·
            refine ⟨459212063226342874148873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1224565501936914331063661 459212063226342874148873)
            ·
              refine ⟨344409047419757155611655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459212063226342874148873 344409047419757155611655)
              ·
                refine ⟨516613571129635733417483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344409047419757155611655 516613571129635733417483)
                ·
                  refine ⟨774920356694453600126225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 516613571129635733417483 774920356694453600126225)
                  ·
                    refine ⟨581190267520840200094669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 774920356694453600126225 581190267520840200094669)
                    ·
                      refine ⟨217946350320315075035501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 581190267520840200094669 217946350320315075035501)
                      ·
                        rfl

theorem cell23_424449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_424449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424449 prefixEnd_424449 := by exact prefixLift 424449
  have htrace : WordTrace (prefixWord ++ tailWord_424449) baseStart_424449 baseEnd_424449 := by
    simpa [prefixWord, tailWord_424449, baseEnd_424449] using wordTrace_append hprefix tailTrace_424449
  have hstable : (prefixWord ++ tailWord_424449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424449).length < 2 ^ (prefixWord ++ tailWord_424449).sum := by decide
  have hdescent : baseEnd_424449 < baseStart_424449 := by decide
  rcases family_descends (prefixWord ++ tailWord_424449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424462 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3]
def baseStart_424462 : Nat := 118140960795 + 424462 * 2 ^ 59
def prefixEnd_424462 : Nat := 4983230072969 + 3 ^ 40 * 424462 * 2
def baseEnd_424462 : Nat := 217953025568823524172941

theorem tailTrace_424462 : CollatzResearch.WordTrace tailWord_424462 prefixEnd_424462 217953025568823524172941 := by
  unfold tailWord_424462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1935175123531767647912455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10320933992169427455533093 1935175123531767647912455)
  ·
    refine ⟨2902762685297651471868683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1935175123531767647912455 2902762685297651471868683)
    ·
      refine ⟨4354144027946477207803025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2902762685297651471868683 4354144027946477207803025)
      ·
        refine ⟨3265608020959857905852269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4354144027946477207803025 3265608020959857905852269)
        ·
          refine ⟨1224603007859946714694601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3265608020959857905852269 1224603007859946714694601)
          ·
            refine ⟨918452255894960036020951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1224603007859946714694601 918452255894960036020951)
            ·
              refine ⟨1377678383842440054031427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 918452255894960036020951 1377678383842440054031427)
              ·
                refine ⟨2066517575763660081047141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1377678383842440054031427 2066517575763660081047141)
                ·
                  refine ⟨387472045455686265196339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2066517575763660081047141 387472045455686265196339)
                  ·
                    refine ⟨581208068183529397794509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 387472045455686265196339 581208068183529397794509)
                    ·
                      refine ⟨217953025568823524172941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 581208068183529397794509 217953025568823524172941)
                      ·
                        rfl

theorem cell23_424462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_424462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424462 prefixEnd_424462 := by exact prefixLift 424462
  have htrace : WordTrace (prefixWord ++ tailWord_424462) baseStart_424462 baseEnd_424462 := by
    simpa [prefixWord, tailWord_424462, baseEnd_424462] using wordTrace_append hprefix tailTrace_424462
  have hstable : (prefixWord ++ tailWord_424462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424462).length < 2 ^ (prefixWord ++ tailWord_424462).sum := by decide
  have hdescent : baseEnd_424462 < baseStart_424462 := by decide
  rcases family_descends (prefixWord ++ tailWord_424462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424498 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4]
def baseStart_424498 : Nat := 118140960795 + 424498 * 2 ^ 59
def prefixEnd_424498 : Nat := 4983230072969 + 3 ^ 40 * 424498 * 2
def baseEnd_424498 : Nat := 217971510872385383322775

theorem tailTrace_424498 : CollatzResearch.WordTrace tailWord_424498 prefixEnd_424498 217971510872385383322775 := by
  unfold tailWord_424498
  simp only [CollatzResearch.WordTrace]
  refine ⟨3870678504030929832902537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10321809344082479554406765 3870678504030929832902537)
  ·
    refine ⟨2903008878023197374676903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3870678504030929832902537 2903008878023197374676903)
    ·
      refine ⟨4354513317034796062015355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2903008878023197374676903 4354513317034796062015355)
      ·
        refine ⟨6531769975552194093023033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4354513317034796062015355 6531769975552194093023033)
        ·
          refine ⟨4898827481664145569767275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6531769975552194093023033 4898827481664145569767275)
          ·
            refine ⟨7348241222496218354650913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4898827481664145569767275 7348241222496218354650913)
            ·
              refine ⟨5511180916872163765988185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7348241222496218354650913 5511180916872163765988185)
              ·
                refine ⟨4133385687654122824491139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5511180916872163765988185 4133385687654122824491139)
                ·
                  refine ⟨6200078531481184236736709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4133385687654122824491139 6200078531481184236736709)
                  ·
                    refine ⟨1162514724652722044388133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6200078531481184236736709 1162514724652722044388133)
                    ·
                      refine ⟨217971510872385383322775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1162514724652722044388133 217971510872385383322775)
                      ·
                        rfl

theorem cell23_424498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_424498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424498 prefixEnd_424498 := by exact prefixLift 424498
  have htrace : WordTrace (prefixWord ++ tailWord_424498) baseStart_424498 baseEnd_424498 := by
    simpa [prefixWord, tailWord_424498, baseEnd_424498] using wordTrace_append hprefix tailTrace_424498
  have hstable : (prefixWord ++ tailWord_424498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424498).length < 2 ^ (prefixWord ++ tailWord_424498).sum := by decide
  have hdescent : baseEnd_424498 < baseStart_424498 := by decide
  rcases family_descends (prefixWord ++ tailWord_424498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424548 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 1, 1, 7]
def baseStart_424548 : Nat := 118140960795 + 424548 * 2 ^ 59
def prefixEnd_424548 : Nat := 4983230072969 + 3 ^ 40 * 424548 * 2
def baseEnd_424548 : Nat := 217997184905110187697545

theorem tailTrace_424548 : CollatzResearch.WordTrace tailWord_424548 prefixEnd_424548 217997184905110187697545 := by
  unfold tailWord_424548
  simp only [CollatzResearch.WordTrace]
  refine ⟨7742268832971288935465149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10323025110628385247286865 7742268832971288935465149)
  ·
    refine ⟨2903350812364233350799431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7742268832971288935465149 2903350812364233350799431)
    ·
      refine ⟨4355026218546350026199147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2903350812364233350799431 4355026218546350026199147)
      ·
        refine ⟨6532539327819525039298721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4355026218546350026199147 6532539327819525039298721)
        ·
          refine ⟨4899404495864643779474041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6532539327819525039298721 4899404495864643779474041)
          ·
            refine ⟨3674553371898482834605531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4899404495864643779474041 3674553371898482834605531)
            ·
              refine ⟨5511830057847724251908297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3674553371898482834605531 5511830057847724251908297)
              ·
                refine ⟨4133872543385793188931223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5511830057847724251908297 4133872543385793188931223)
                ·
                  refine ⟨6200808815078689783396835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4133872543385793188931223 6200808815078689783396835)
                  ·
                    refine ⟨9301213222618034675095253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6200808815078689783396835 9301213222618034675095253)
                    ·
                      refine ⟨217997184905110187697545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9301213222618034675095253 217997184905110187697545)
                      ·
                        rfl

theorem cell23_424548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_424548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424548 prefixEnd_424548 := by exact prefixLift 424548
  have htrace : WordTrace (prefixWord ++ tailWord_424548) baseStart_424548 baseEnd_424548 := by
    simpa [prefixWord, tailWord_424548, baseEnd_424548] using wordTrace_append hprefix tailTrace_424548
  have hstable : (prefixWord ++ tailWord_424548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424548).length < 2 ^ (prefixWord ++ tailWord_424548).sum := by decide
  have hdescent : baseEnd_424548 < baseStart_424548 := by decide
  rcases family_descends (prefixWord ++ tailWord_424548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424585 : List Nat := [1, 2, 1, 1, 4, 1, 1, 5, 3, 4]
def baseStart_424585 : Nat := 118140960795 + 424585 * 2 ^ 59
def prefixEnd_424585 : Nat := 4983230072969 + 3 ^ 40 * 424585 * 2
def baseEnd_424585 : Nat := 72672061229775514311625

theorem tailTrace_424585 : CollatzResearch.WordTrace tailWord_424585 prefixEnd_424585 72672061229775514311625 := by
  unfold tailWord_424585
  simp only [CollatzResearch.WordTrace]
  refine ⟨15485887166808533190027209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10323924777872355460018139 15485887166808533190027209)
  ·
    refine ⟨11614415375106399892520407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15485887166808533190027209 11614415375106399892520407)
    ·
      refine ⟨17421623062659599838780611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11614415375106399892520407 17421623062659599838780611)
      ·
        refine ⟨26132434593989399758170917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17421623062659599838780611 26132434593989399758170917)
        ·
          refine ⟨4899831486373012454657047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26132434593989399758170917 4899831486373012454657047)
          ·
            refine ⟨7349747229559518681985571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4899831486373012454657047 7349747229559518681985571)
            ·
              refine ⟨11024620844339278022978357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7349747229559518681985571 11024620844339278022978357)
              ·
                refine ⟨1033558204156807314654221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11024620844339278022978357 1033558204156807314654221)
                ·
                  refine ⟨387584326558802742995333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1033558204156807314654221 387584326558802742995333)
                  ·
                    refine ⟨72672061229775514311625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 387584326558802742995333 72672061229775514311625)
                    ·
                      rfl

theorem cell23_424585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 4].length) (baseStart_424585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424585 prefixEnd_424585 := by exact prefixLift 424585
  have htrace : WordTrace (prefixWord ++ tailWord_424585) baseStart_424585 baseEnd_424585 := by
    simpa [prefixWord, tailWord_424585, baseEnd_424585] using wordTrace_append hprefix tailTrace_424585
  have hstable : (prefixWord ++ tailWord_424585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424585).length < 2 ^ (prefixWord ++ tailWord_424585).sum := by decide
  have hdescent : baseEnd_424585 < baseStart_424585 := by decide
  rcases family_descends (prefixWord ++ tailWord_424585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424588 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 4, 1, 6]
def baseStart_424588 : Nat := 118140960795 + 424588 * 2 ^ 59
def prefixEnd_424588 : Nat := 4983230072969 + 3 ^ 40 * 424588 * 2
def baseEnd_424588 : Nat := 218017724131290031197361

theorem tailTrace_424588 : CollatzResearch.WordTrace tailWord_424588 prefixEnd_424588 218017724131290031197361 := by
  unfold tailWord_424588
  simp only [CollatzResearch.WordTrace]
  refine ⟨7742998292898832351193209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10323997723865109801590945 7742998292898832351193209)
  ·
    refine ⟨5807248719674124263394907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7742998292898832351193209 5807248719674124263394907)
    ·
      refine ⟨8710873079511186395092361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5807248719674124263394907 8710873079511186395092361)
      ·
        refine ⟨6533154809633389796319271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8710873079511186395092361 6533154809633389796319271)
        ·
          refine ⟨9799732214450084694478907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6533154809633389796319271 9799732214450084694478907)
          ·
            refine ⟨14699598321675127041718361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9799732214450084694478907 14699598321675127041718361)
            ·
              refine ⟨11024698741256345281288771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14699598321675127041718361 11024698741256345281288771)
              ·
                refine ⟨16537048111884517921933157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11024698741256345281288771 16537048111884517921933157)
                ·
                  refine ⟨3100696520978347110362467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16537048111884517921933157 3100696520978347110362467)
                  ·
                    refine ⟨4651044781467520665543701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3100696520978347110362467 4651044781467520665543701)
                    ·
                      refine ⟨218017724131290031197361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4651044781467520665543701 218017724131290031197361)
                      ·
                        rfl

theorem cell23_424588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_424588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424588 prefixEnd_424588 := by exact prefixLift 424588
  have htrace : WordTrace (prefixWord ++ tailWord_424588) baseStart_424588 baseEnd_424588 := by
    simpa [prefixWord, tailWord_424588, baseEnd_424588] using wordTrace_append hprefix tailTrace_424588
  have hstable : (prefixWord ++ tailWord_424588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424588).length < 2 ^ (prefixWord ++ tailWord_424588).sum := by decide
  have hdescent : baseEnd_424588 < baseStart_424588 := by decide
  rcases family_descends (prefixWord ++ tailWord_424588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424609 : List Nat := [1, 2, 3, 3, 3, 2, 1, 1, 2, 1, 4]
def baseStart_424609 : Nat := 118140960795 + 424609 * 2 ^ 59
def prefixEnd_424609 : Nat := 4983230072969 + 3 ^ 40 * 424609 * 2
def baseEnd_424609 : Nat := 218028507225034449034765

theorem tailTrace_424609 : CollatzResearch.WordTrace tailWord_424609 prefixEnd_424609 218028507225034449034765 := by
  unfold tailWord_424609
  simp only [CollatzResearch.WordTrace]
  refine ⟨15486762518721585288900881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10324508345814390192600587 15486762518721585288900881)
  ·
    refine ⟨11615071889041188966675661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15486762518721585288900881 11615071889041188966675661)
    ·
      refine ⟨4355651958390445862503373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11615071889041188966675661 4355651958390445862503373)
      ·
        refine ⟨1633369484396417198438765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4355651958390445862503373 1633369484396417198438765)
        ·
          refine ⟨612513556648656449414537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1633369484396417198438765 612513556648656449414537)
          ·
            refine ⟨459385167486492337060903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 612513556648656449414537 459385167486492337060903)
            ·
              refine ⟨689077751229738505591355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459385167486492337060903 689077751229738505591355)
              ·
                refine ⟨1033616626844607758387033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 689077751229738505591355 1033616626844607758387033)
                ·
                  refine ⟨775212470133455818790275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1033616626844607758387033 775212470133455818790275)
                  ·
                    refine ⟨1162818705200183728185413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 775212470133455818790275 1162818705200183728185413)
                    ·
                      refine ⟨218028507225034449034765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1162818705200183728185413 218028507225034449034765)
                      ·
                        rfl

theorem cell23_424609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_424609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424609 prefixEnd_424609 := by exact prefixLift 424609
  have htrace : WordTrace (prefixWord ++ tailWord_424609) baseStart_424609 baseEnd_424609 := by
    simpa [prefixWord, tailWord_424609, baseEnd_424609] using wordTrace_append hprefix tailTrace_424609
  have hstable : (prefixWord ++ tailWord_424609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424609).length < 2 ^ (prefixWord ++ tailWord_424609).sum := by decide
  have hdescent : baseEnd_424609 < baseStart_424609 := by decide
  rcases family_descends (prefixWord ++ tailWord_424609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424622 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_424622 : Nat := 118140960795 + 424622 * 2 ^ 59
def prefixEnd_424622 : Nat := 4983230072969 + 3 ^ 40 * 424622 * 2
def baseEnd_424622 : Nat := 218035182473542898172205

theorem tailTrace_424622 : CollatzResearch.WordTrace tailWord_424622 prefixEnd_424622 218035182473542898172205 := by
  unfold tailWord_424622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1935904583459311063640515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10324824445116325672749413 1935904583459311063640515)
  ·
    refine ⟨2903856875188966595460773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1935904583459311063640515 2903856875188966595460773)
    ·
      refine ⟨544473164097931236648895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2903856875188966595460773 544473164097931236648895)
      ·
        refine ⟨816709746146896854973343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544473164097931236648895 816709746146896854973343)
        ·
          refine ⟨1225064619220345282460015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 816709746146896854973343 1225064619220345282460015)
          ·
            refine ⟨1837596928830517923690023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1225064619220345282460015 1837596928830517923690023)
            ·
              refine ⟨2756395393245776885535035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1837596928830517923690023 2756395393245776885535035)
              ·
                refine ⟨4134593089868665328302553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2756395393245776885535035 4134593089868665328302553)
                ·
                  refine ⟨3100944817401498996226915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4134593089868665328302553 3100944817401498996226915)
                  ·
                    refine ⟨4651417226102248494340373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3100944817401498996226915 4651417226102248494340373)
                    ·
                      refine ⟨218035182473542898172205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4651417226102248494340373 218035182473542898172205)
                      ·
                        rfl

theorem cell23_424622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_424622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424622 prefixEnd_424622 := by exact prefixLift 424622
  have htrace : WordTrace (prefixWord ++ tailWord_424622) baseStart_424622 baseEnd_424622 := by
    simpa [prefixWord, tailWord_424622, baseEnd_424622] using wordTrace_append hprefix tailTrace_424622
  have hstable : (prefixWord ++ tailWord_424622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424622).length < 2 ^ (prefixWord ++ tailWord_424622).sum := by decide
  have hdescent : baseEnd_424622 < baseStart_424622 := by decide
  rcases family_descends (prefixWord ++ tailWord_424622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424676 : List Nat := [2, 3, 1, 1, 1, 4, 3, 3, 1, 1, 3]
def baseStart_424676 : Nat := 118140960795 + 424676 * 2 ^ 59
def prefixEnd_424676 : Nat := 4983230072969 + 3 ^ 40 * 424676 * 2
def baseEnd_424676 : Nat := 218062910428885686896957

theorem tailTrace_424676 : CollatzResearch.WordTrace tailWord_424676 prefixEnd_424676 218062910428885686896957 := by
  unfold tailWord_424676
  simp only [CollatzResearch.WordTrace]
  refine ⟨7744603104739427865794941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10326137472985903821059921 7744603104739427865794941)
  ·
    refine ⟨2904226164277285449673103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7744603104739427865794941 2904226164277285449673103)
    ·
      refine ⟨4356339246415928174509655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2904226164277285449673103 4356339246415928174509655)
      ·
        refine ⟨6534508869623892261764483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4356339246415928174509655 6534508869623892261764483)
        ·
          refine ⟨9801763304435838392646725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6534508869623892261764483 9801763304435838392646725)
          ·
            refine ⟨1837830619581719698621261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9801763304435838392646725 1837830619581719698621261)
            ·
              refine ⟨689186482343144886982973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1837830619581719698621261 689186482343144886982973)
              ·
                refine ⟨258444930878679332618615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 689186482343144886982973 258444930878679332618615)
                ·
                  refine ⟨387667396318018998927923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258444930878679332618615 387667396318018998927923)
                  ·
                    refine ⟨581501094477028498391885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 387667396318018998927923 581501094477028498391885)
                    ·
                      refine ⟨218062910428885686896957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 581501094477028498391885 218062910428885686896957)
                      ·
                        rfl

theorem cell23_424676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 1, 1, 3].length) (baseStart_424676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424676 prefixEnd_424676 := by exact prefixLift 424676
  have htrace : WordTrace (prefixWord ++ tailWord_424676) baseStart_424676 baseEnd_424676 := by
    simpa [prefixWord, tailWord_424676, baseEnd_424676] using wordTrace_append hprefix tailTrace_424676
  have hstable : (prefixWord ++ tailWord_424676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424676).length < 2 ^ (prefixWord ++ tailWord_424676).sum := by decide
  have hdescent : baseEnd_424676 < baseStart_424676 := by decide
  rcases family_descends (prefixWord ++ tailWord_424676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424732 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 3, 3, 3]
def baseStart_424732 : Nat := 118140960795 + 424732 * 2 ^ 59
def prefixEnd_424732 : Nat := 4983230072969 + 3 ^ 40 * 424732 * 2
def baseEnd_424732 : Nat := 218091665345537467796699

theorem tailTrace_424732 : CollatzResearch.WordTrace tailWord_424732 prefixEnd_424732 218091665345537467796699 := by
  unfold tailWord_424732
  simp only [CollatzResearch.WordTrace]
  refine ⟨7745624348637988647814225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10327499131517318197085633 7745624348637988647814225)
  ·
    refine ⟨5809218261478491485860669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7745624348637988647814225 5809218261478491485860669)
    ·
      refine ⟨2178456848054434307197751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5809218261478491485860669 2178456848054434307197751)
      ·
        refine ⟨3267685272081651460796627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2178456848054434307197751 3267685272081651460796627)
        ·
          refine ⟨4901527908122477191194941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3267685272081651460796627 4901527908122477191194941)
          ·
            refine ⟨1838072965545928946698103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4901527908122477191194941 1838072965545928946698103)
            ·
              refine ⟨2757109448318893420047155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1838072965545928946698103 2757109448318893420047155)
              ·
                refine ⟨4135664172478340130070733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2757109448318893420047155 4135664172478340130070733)
                ·
                  refine ⟨1550874064679377548776525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4135664172478340130070733 1550874064679377548776525)
                  ·
                    refine ⟨581577774254766580791197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1550874064679377548776525 581577774254766580791197)
                    ·
                      refine ⟨218091665345537467796699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 581577774254766580791197 218091665345537467796699)
                      ·
                        rfl

theorem cell23_424732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_424732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424732 prefixEnd_424732 := by exact prefixLift 424732
  have htrace : WordTrace (prefixWord ++ tailWord_424732) baseStart_424732 baseEnd_424732 := by
    simpa [prefixWord, tailWord_424732, baseEnd_424732] using wordTrace_append hprefix tailTrace_424732
  have hstable : (prefixWord ++ tailWord_424732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424732).length < 2 ^ (prefixWord ++ tailWord_424732).sum := by decide
  have hdescent : baseEnd_424732 < baseStart_424732 := by decide
  rcases family_descends (prefixWord ++ tailWord_424732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424733 : List Nat := [1, 4, 2, 4, 1, 1, 3, 1, 1, 1, 4]
def baseStart_424733 : Nat := 118140960795 + 424733 * 2 ^ 59
def prefixEnd_424733 : Nat := 4983230072969 + 3 ^ 40 * 424733 * 2
def baseEnd_424733 : Nat := 218092178826191963884195

theorem tailTrace_424733 : CollatzResearch.WordTrace tailWord_424733 prefixEnd_424733 218092178826191963884195 := by
  unfold tailWord_424733
  simp only [CollatzResearch.WordTrace]
  refine ⟨15491285170272354466414853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10327523446848236310943235 15491285170272354466414853)
  ·
    refine ⟨2904615969426066462452785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15491285170272354466414853 2904615969426066462452785)
    ·
      refine ⟨2178461977069549846839589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2904615969426066462452785 2178461977069549846839589)
      ·
        refine ⟨408461620700540596282423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2178461977069549846839589 408461620700540596282423)
        ·
          refine ⟨612692431050810894423635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408461620700540596282423 612692431050810894423635)
          ·
            refine ⟨919038646576216341635453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612692431050810894423635 919038646576216341635453)
            ·
              refine ⟨344639492466081128113295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 919038646576216341635453 344639492466081128113295)
              ·
                refine ⟨516959238699121692169943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344639492466081128113295 516959238699121692169943)
                ·
                  refine ⟨775438858048682538254915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 516959238699121692169943 775438858048682538254915)
                  ·
                    refine ⟨1163158287073023807382373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 775438858048682538254915 1163158287073023807382373)
                    ·
                      refine ⟨218092178826191963884195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1163158287073023807382373 218092178826191963884195)
                      ·
                        rfl

theorem cell23_424733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_424733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424733 prefixEnd_424733 := by exact prefixLift 424733
  have htrace : WordTrace (prefixWord ++ tailWord_424733) baseStart_424733 baseEnd_424733 := by
    simpa [prefixWord, tailWord_424733, baseEnd_424733] using wordTrace_append hprefix tailTrace_424733
  have hstable : (prefixWord ++ tailWord_424733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424733).length < 2 ^ (prefixWord ++ tailWord_424733).sum := by decide
  have hdescent : baseEnd_424733 < baseStart_424733 := by decide
  rcases family_descends (prefixWord ++ tailWord_424733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424736 : List Nat := [2, 1, 1, 5, 1, 3, 3, 1, 1, 2, 3]
def baseStart_424736 : Nat := 118140960795 + 424736 * 2 ^ 59
def prefixEnd_424736 : Nat := 4983230072969 + 3 ^ 40 * 424736 * 2
def baseEnd_424736 : Nat := 218093719268155452146681

theorem tailTrace_424736 : CollatzResearch.WordTrace tailWord_424736 prefixEnd_424736 218093719268155452146681 := by
  unfold tailWord_424736
  simp only [CollatzResearch.WordTrace]
  refine ⟨7745697294630742989387031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10327596392840990652516041 7745697294630742989387031)
  ·
    refine ⟨11618545941946114484080547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7745697294630742989387031 11618545941946114484080547)
    ·
      refine ⟨17427818912919171726120821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11618545941946114484080547 17427818912919171726120821)
      ·
        refine ⟨1633858023086172349323827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17427818912919171726120821 1633858023086172349323827)
        ·
          refine ⟨2450787034629258523985741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1633858023086172349323827 2450787034629258523985741)
          ·
            refine ⟨919045137985971946494653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2450787034629258523985741 919045137985971946494653)
            ·
              refine ⟨344641926744739479935495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 919045137985971946494653 344641926744739479935495)
              ·
                refine ⟨516962890117109219903243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344641926744739479935495 516962890117109219903243)
                ·
                  refine ⟨775444335175663829854865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 516962890117109219903243 775444335175663829854865)
                  ·
                    refine ⟨581583251381747872391149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 775444335175663829854865 581583251381747872391149)
                    ·
                      refine ⟨218093719268155452146681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 581583251381747872391149 218093719268155452146681)
                      ·
                        rfl

theorem cell23_424736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_424736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424736 prefixEnd_424736 := by exact prefixLift 424736
  have htrace : WordTrace (prefixWord ++ tailWord_424736) baseStart_424736 baseEnd_424736 := by
    simpa [prefixWord, tailWord_424736, baseEnd_424736] using wordTrace_append hprefix tailTrace_424736
  have hstable : (prefixWord ++ tailWord_424736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424736).length < 2 ^ (prefixWord ++ tailWord_424736).sum := by decide
  have hdescent : baseEnd_424736 < baseStart_424736 := by decide
  rcases family_descends (prefixWord ++ tailWord_424736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424750 : List Nat := [4, 1, 3, 2, 1, 2, 1, 4, 1, 2, 2]
def baseStart_424750 : Nat := 118140960795 + 424750 * 2 ^ 59
def prefixEnd_424750 : Nat := 4983230072969 + 3 ^ 40 * 424750 * 2
def baseEnd_424750 : Nat := 218100907997318397371617

theorem tailTrace_424750 : CollatzResearch.WordTrace tailWord_424750 prefixEnd_424750 218100907997318397371617 := by
  unfold tailWord_424750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1936488151401345796222963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10327936807473844246522469 1936488151401345796222963)
  ·
    refine ⟨2904732227102018694334445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1936488151401345796222963 2904732227102018694334445)
    ·
      refine ⟨1089274585163257010375417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2904732227102018694334445 1089274585163257010375417)
      ·
        refine ⟨816955938872442757781563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1089274585163257010375417 816955938872442757781563)
        ·
          refine ⟨1225433908308664136672345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 816955938872442757781563 1225433908308664136672345)
          ·
            refine ⟨919075431231498102504259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1225433908308664136672345 919075431231498102504259)
            ·
              refine ⟨1378613146847247153756389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 919075431231498102504259 1378613146847247153756389)
              ·
                refine ⟨258489965033858841329323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1378613146847247153756389 258489965033858841329323)
                ·
                  refine ⟨387734947550788261993985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258489965033858841329323 387734947550788261993985)
                  ·
                    refine ⟨290801210663091196495489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 387734947550788261993985 290801210663091196495489)
                    ·
                      refine ⟨218100907997318397371617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 290801210663091196495489 218100907997318397371617)
                      ·
                        rfl

theorem cell23_424750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_424750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424750 prefixEnd_424750 := by exact prefixLift 424750
  have htrace : WordTrace (prefixWord ++ tailWord_424750) baseStart_424750 baseEnd_424750 := by
    simpa [prefixWord, tailWord_424750, baseEnd_424750] using wordTrace_append hprefix tailTrace_424750
  have hstable : (prefixWord ++ tailWord_424750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424750).length < 2 ^ (prefixWord ++ tailWord_424750).sum := by decide
  have hdescent : baseEnd_424750 < baseStart_424750 := by decide
  rcases family_descends (prefixWord ++ tailWord_424750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424756 : List Nat := [2, 5, 1, 1, 4, 1, 1, 8]
def baseStart_424756 : Nat := 118140960795 + 424756 * 2 ^ 59
def prefixEnd_424756 : Nat := 4983230072969 + 3 ^ 40 * 424756 * 2
def baseEnd_424756 : Nat := 8077925514120199033207

theorem tailTrace_424756 : CollatzResearch.WordTrace tailWord_424756 prefixEnd_424756 8077925514120199033207 := by
  unfold tailWord_424756
  simp only [CollatzResearch.WordTrace]
  refine ⟨7746062024594514697251061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10328082699459352929668081 7746062024594514697251061)
  ·
    refine ⟨726193314805735752867287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7746062024594514697251061 726193314805735752867287)
    ·
      refine ⟨1089289972208603629300931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 726193314805735752867287 1089289972208603629300931)
      ·
        refine ⟨1633934958312905443951397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1089289972208603629300931 1633934958312905443951397)
        ·
          refine ⟨306362804683669770740887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1633934958312905443951397 306362804683669770740887)
          ·
            refine ⟨459544207025504656111331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306362804683669770740887 459544207025504656111331)
            ·
              refine ⟨689316310538256984166997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459544207025504656111331 689316310538256984166997)
              ·
                refine ⟨8077925514120199033207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 689316310538256984166997 8077925514120199033207)
                ·
                  rfl

theorem cell23_424756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 8].length) (baseStart_424756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424756 prefixEnd_424756 := by exact prefixLift 424756
  have htrace : WordTrace (prefixWord ++ tailWord_424756) baseStart_424756 baseEnd_424756 := by
    simpa [prefixWord, tailWord_424756, baseEnd_424756] using wordTrace_append hprefix tailTrace_424756
  have hstable : (prefixWord ++ tailWord_424756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424756).length < 2 ^ (prefixWord ++ tailWord_424756).sum := by decide
  have hdescent : baseEnd_424756 < baseStart_424756 := by decide
  rcases family_descends (prefixWord ++ tailWord_424756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424766 : List Nat := [4, 2, 1, 2, 3, 1, 2, 1, 1, 3, 3]
def baseStart_424766 : Nat := 118140960795 + 424766 * 2 ^ 59
def prefixEnd_424766 : Nat := 4983230072969 + 3 ^ 40 * 424766 * 2
def baseEnd_424766 : Nat := 218109123687790334771543

theorem tailTrace_424766 : CollatzResearch.WordTrace tailWord_424766 prefixEnd_424766 218109123687790334771543 := by
  unfold tailWord_424766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1936561097394100137795769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10328325852768534068244101 1936561097394100137795769)
  ·
    refine ⟨1452420823045575103346827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1936561097394100137795769 1452420823045575103346827)
    ·
      refine ⟨2178631234568362655020241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1452420823045575103346827 2178631234568362655020241)
      ·
        refine ⟨1633973425926271991265181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2178631234568362655020241 1633973425926271991265181)
        ·
          refine ⟨612740034722351996724443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1633973425926271991265181 612740034722351996724443)
          ·
            refine ⟨919110052083527995086665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612740034722351996724443 919110052083527995086665)
            ·
              refine ⟨689332539062645996314999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 919110052083527995086665 689332539062645996314999)
              ·
                refine ⟨1033998808593968994472499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 689332539062645996314999 1033998808593968994472499)
                ·
                  refine ⟨1550998212890953491708749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1033998808593968994472499 1550998212890953491708749)
                  ·
                    refine ⟨581624329834107559390781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1550998212890953491708749 581624329834107559390781)
                    ·
                      refine ⟨218109123687790334771543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 581624329834107559390781 218109123687790334771543)
                      ·
                        rfl

theorem cell23_424766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_424766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424766 prefixEnd_424766 := by exact prefixLift 424766
  have htrace : WordTrace (prefixWord ++ tailWord_424766) baseStart_424766 baseEnd_424766 := by
    simpa [prefixWord, tailWord_424766, baseEnd_424766] using wordTrace_append hprefix tailTrace_424766
  have hstable : (prefixWord ++ tailWord_424766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424766).length < 2 ^ (prefixWord ++ tailWord_424766).sum := by decide
  have hdescent : baseEnd_424766 < baseStart_424766 := by decide
  rcases family_descends (prefixWord ++ tailWord_424766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424789 : List Nat := [1, 3, 2, 2, 2, 1, 1, 4, 1, 4, 2]
def baseStart_424789 : Nat := 118140960795 + 424789 * 2 ^ 59
def prefixEnd_424789 : Nat := 4983230072969 + 3 ^ 40 * 424789 * 2
def baseEnd_424789 : Nat := 218120933742843744783937

theorem tailTrace_424789 : CollatzResearch.WordTrace tailWord_424789 prefixEnd_424789 218120933742843744783937 := by
  unfold tailWord_424789
  simp only [CollatzResearch.WordTrace]
  refine ⟨15493327658069476030453421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10328885105379650686968947 15493327658069476030453421)
  ·
    refine ⟨5809997871776053511420033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15493327658069476030453421 5809997871776053511420033)
    ·
      refine ⟨4357498403832040133565025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5809997871776053511420033 4357498403832040133565025)
      ·
        refine ⟨3268123802874030100173769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4357498403832040133565025 3268123802874030100173769)
        ·
          refine ⟨2451092852155522575130327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3268123802874030100173769 2451092852155522575130327)
          ·
            refine ⟨3676639278233283862695491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2451092852155522575130327 3676639278233283862695491)
            ·
              refine ⟨5514958917349925794043237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3676639278233283862695491 5514958917349925794043237)
              ·
                refine ⟨1034054797003111086383107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5514958917349925794043237 1034054797003111086383107)
                ·
                  refine ⟨1551082195504666629574661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1034054797003111086383107 1551082195504666629574661)
                  ·
                    refine ⟨290827911657124993045249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1551082195504666629574661 290827911657124993045249)
                    ·
                      refine ⟨218120933742843744783937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 290827911657124993045249 218120933742843744783937)
                      ·
                        rfl

theorem cell23_424789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_424789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424789 prefixEnd_424789 := by exact prefixLift 424789
  have htrace : WordTrace (prefixWord ++ tailWord_424789) baseStart_424789 baseEnd_424789 := by
    simpa [prefixWord, tailWord_424789, baseEnd_424789] using wordTrace_append hprefix tailTrace_424789
  have hstable : (prefixWord ++ tailWord_424789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424789).length < 2 ^ (prefixWord ++ tailWord_424789).sum := by decide
  have hdescent : baseEnd_424789 < baseStart_424789 := by decide
  rcases family_descends (prefixWord ++ tailWord_424789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424793 : List Nat := [1, 2, 1, 2, 2, 6, 2, 1, 1, 3, 2]
def baseStart_424793 : Nat := 118140960795 + 424793 * 2 ^ 59
def prefixEnd_424793 : Nat := 4983230072969 + 3 ^ 40 * 424793 * 2
def baseEnd_424793 : Nat := 218122987665461729133919

theorem tailTrace_424793 : CollatzResearch.WordTrace tailWord_424793 prefixEnd_424793 218122987665461729133919 := by
  unfold tailWord_424793
  simp only [CollatzResearch.WordTrace]
  refine ⟨15493473550054984713599033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10328982366703323142399355 15493473550054984713599033)
  ·
    refine ⟨11620105162541238535199275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15493473550054984713599033 11620105162541238535199275)
    ·
      refine ⟨17430157743811857802798913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11620105162541238535199275 17430157743811857802798913)
      ·
        refine ⟨13072618307858893352099185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17430157743811857802798913 13072618307858893352099185)
        ·
          refine ⟨9804463730894170014074389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13072618307858893352099185 9804463730894170014074389)
          ·
            refine ⟨459584237385664219409737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9804463730894170014074389 459584237385664219409737)
            ·
              refine ⟨344688178039248164557303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459584237385664219409737 344688178039248164557303)
              ·
                refine ⟨517032267058872246835955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344688178039248164557303 517032267058872246835955)
                ·
                  refine ⟨775548400588308370253933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 517032267058872246835955 775548400588308370253933)
                  ·
                    refine ⟨290830650220615638845225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 775548400588308370253933 290830650220615638845225)
                    ·
                      refine ⟨218122987665461729133919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 290830650220615638845225 218122987665461729133919)
                      ·
                        rfl

theorem cell23_424793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 1, 3, 2].length) (baseStart_424793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424793 prefixEnd_424793 := by exact prefixLift 424793
  have htrace : WordTrace (prefixWord ++ tailWord_424793) baseStart_424793 baseEnd_424793 := by
    simpa [prefixWord, tailWord_424793, baseEnd_424793] using wordTrace_append hprefix tailTrace_424793
  have hstable : (prefixWord ++ tailWord_424793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424793).length < 2 ^ (prefixWord ++ tailWord_424793).sum := by decide
  have hdescent : baseEnd_424793 < baseStart_424793 := by decide
  rcases family_descends (prefixWord ++ tailWord_424793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424812 : List Nat := [2, 2, 1, 1, 4, 1, 4, 1, 7]
def baseStart_424812 : Nat := 118140960795 + 424812 * 2 ^ 59
def prefixEnd_424812 : Nat := 4983230072969 + 3 ^ 40 * 424812 * 2
def baseEnd_424812 : Nat := 24236971533099683866259

theorem tailTrace_424812 : CollatzResearch.WordTrace tailWord_424812 prefixEnd_424812 24236971533099683866259 := by
  unfold tailWord_424812
  simp only [CollatzResearch.WordTrace]
  refine ⟨7747083268493075479270345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10329444357990767305693793 7747083268493075479270345)
  ·
    refine ⟨5810312451369806609452759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7747083268493075479270345 5810312451369806609452759)
    ·
      refine ⟨8715468677054709914179139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5810312451369806609452759 8715468677054709914179139)
      ·
        refine ⟨13073203015582064871268709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8715468677054709914179139 13073203015582064871268709)
        ·
          refine ⟨2451225565421637163362883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13073203015582064871268709 2451225565421637163362883)
          ·
            refine ⟨3676838348132455745044325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2451225565421637163362883 3676838348132455745044325)
            ·
              refine ⟨689407190274835452195811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3676838348132455745044325 689407190274835452195811)
              ·
                refine ⟨1034110785412253178293717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 689407190274835452195811 1034110785412253178293717)
                ·
                  refine ⟨24236971533099683866259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1034110785412253178293717 24236971533099683866259)
                  ·
                    rfl

theorem cell23_424812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 7].length) (baseStart_424812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424812 prefixEnd_424812 := by exact prefixLift 424812
  have htrace : WordTrace (prefixWord ++ tailWord_424812) baseStart_424812 baseEnd_424812 := by
    simpa [prefixWord, tailWord_424812, baseEnd_424812] using wordTrace_append hprefix tailTrace_424812
  have hstable : (prefixWord ++ tailWord_424812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424812).length < 2 ^ (prefixWord ++ tailWord_424812).sum := by decide
  have hdescent : baseEnd_424812 < baseStart_424812 := by decide
  rcases family_descends (prefixWord ++ tailWord_424812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424906 : List Nat := [3, 1, 2, 1, 2, 1, 1, 7, 1, 4]
def baseStart_424906 : Nat := 118140960795 + 424906 * 2 ^ 59
def prefixEnd_424906 : Nat := 4983230072969 + 3 ^ 40 * 424906 * 2
def baseEnd_424906 : Nat := 72727003659806595673633

theorem tailTrace_424906 : CollatzResearch.WordTrace tailWord_424906 prefixEnd_424906 72727003659806595673633 := by
  unfold tailWord_424906
  simp only [CollatzResearch.WordTrace]
  refine ⟨3874398749661401253115643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10331729999097070008308381 3874398749661401253115643)
  ·
    refine ⟨5811598124492101879673465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3874398749661401253115643 5811598124492101879673465)
    ·
      refine ⟨4358698593369076409755099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5811598124492101879673465 4358698593369076409755099)
      ·
        refine ⟨6538047890053614614632649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4358698593369076409755099 6538047890053614614632649)
        ·
          refine ⟨4903535917540210960974487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6538047890053614614632649 4903535917540210960974487)
          ·
            refine ⟨7355303876310316441461731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4903535917540210960974487 7355303876310316441461731)
            ·
              refine ⟨11032955814465474662192597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7355303876310316441461731 11032955814465474662192597)
              ·
                refine ⟨258584901901534562395139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11032955814465474662192597 258584901901534562395139)
                ·
                  refine ⟨387877352852301843592709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258584901901534562395139 387877352852301843592709)
                  ·
                    refine ⟨72727003659806595673633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 387877352852301843592709 72727003659806595673633)
                    ·
                      rfl

theorem cell23_424906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_424906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424906 prefixEnd_424906 := by exact prefixLift 424906
  have htrace : WordTrace (prefixWord ++ tailWord_424906) baseStart_424906 baseEnd_424906 := by
    simpa [prefixWord, tailWord_424906, baseEnd_424906] using wordTrace_append hprefix tailTrace_424906
  have hstable : (prefixWord ++ tailWord_424906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424906).length < 2 ^ (prefixWord ++ tailWord_424906).sum := by decide
  have hdescent : baseEnd_424906 < baseStart_424906 := by decide
  rcases family_descends (prefixWord ++ tailWord_424906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424916 : List Nat := [2, 4, 1, 2, 1, 2, 2, 2, 2, 2, 3]
def baseStart_424916 : Nat := 118140960795 + 424916 * 2 ^ 59
def prefixEnd_424916 : Nat := 4983230072969 + 3 ^ 40 * 424916 * 2
def baseEnd_424916 : Nat := 218186145785964747895853

theorem tailTrace_424916 : CollatzResearch.WordTrace tailWord_424916 prefixEnd_424916 218186145785964747895853 := by
  unfold tailWord_424916
  simp only [CollatzResearch.WordTrace]
  refine ⟨7748979864304688360163301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10331973152406251146884401 7748979864304688360163301)
  ·
    refine ⟨1452933724557129067530619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7748979864304688360163301 1452933724557129067530619)
    ·
      refine ⟨2179400586835693601295929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1452933724557129067530619 2179400586835693601295929)
      ·
        refine ⟨1634550440126770200971947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2179400586835693601295929 1634550440126770200971947)
        ·
          refine ⟨2451825660190155301457921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1634550440126770200971947 2451825660190155301457921)
          ·
            refine ⟨1838869245142616476093441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2451825660190155301457921 1838869245142616476093441)
            ·
              refine ⟨1379151933856962357070081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1838869245142616476093441 1379151933856962357070081)
              ·
                refine ⟨1034363950392721767802561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1379151933856962357070081 1034363950392721767802561)
                ·
                  refine ⟨775772962794541325851921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1034363950392721767802561 775772962794541325851921)
                  ·
                    refine ⟨581829722095905994388941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 775772962794541325851921 581829722095905994388941)
                    ·
                      refine ⟨218186145785964747895853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 581829722095905994388941 218186145785964747895853)
                      ·
                        rfl

theorem cell23_424916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_424916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424916 prefixEnd_424916 := by exact prefixLift 424916
  have htrace : WordTrace (prefixWord ++ tailWord_424916) baseStart_424916 baseEnd_424916 := by
    simpa [prefixWord, tailWord_424916, baseEnd_424916] using wordTrace_append hprefix tailTrace_424916
  have hstable : (prefixWord ++ tailWord_424916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424916).length < 2 ^ (prefixWord ++ tailWord_424916).sum := by decide
  have hdescent : baseEnd_424916 < baseStart_424916 := by decide
  rcases family_descends (prefixWord ++ tailWord_424916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424956 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 1, 5, 2]
def baseStart_424956 : Nat := 118140960795 + 424956 * 2 ^ 59
def prefixEnd_424956 : Nat := 4983230072969 + 3 ^ 40 * 424956 * 2
def baseEnd_424956 : Nat := 218206685012144591395669

theorem tailTrace_424956 : CollatzResearch.WordTrace tailWord_424956 prefixEnd_424956 218206685012144591395669 := by
  unfold tailWord_424956
  simp only [CollatzResearch.WordTrace]
  refine ⟨7749709324232231775891361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10332945765642975701188481 7749709324232231775891361)
  ·
    refine ⟨5812281993174173831918521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7749709324232231775891361 5812281993174173831918521)
    ·
      refine ⟨4359211494880630373938891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5812281993174173831918521 4359211494880630373938891)
      ·
        refine ⟨6538817242320945560908337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4359211494880630373938891 6538817242320945560908337)
        ·
          refine ⟨4904112931740709170681253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6538817242320945560908337 4904112931740709170681253)
          ·
            refine ⟨919521174701382969502735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4904112931740709170681253 919521174701382969502735)
            ·
              refine ⟨1379281762052074454254103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 919521174701382969502735 1379281762052074454254103)
              ·
                refine ⟨2068922643078111681381155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1379281762052074454254103 2068922643078111681381155)
                ·
                  refine ⟨3103383964617167522071733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2068922643078111681381155 3103383964617167522071733)
                  ·
                    refine ⟨290942246682859455194225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3103383964617167522071733 290942246682859455194225)
                    ·
                      refine ⟨218206685012144591395669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 290942246682859455194225 218206685012144591395669)
                      ·
                        rfl

theorem cell23_424956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 1, 5, 2].length) (baseStart_424956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424956 prefixEnd_424956 := by exact prefixLift 424956
  have htrace : WordTrace (prefixWord ++ tailWord_424956) baseStart_424956 baseEnd_424956 := by
    simpa [prefixWord, tailWord_424956, baseEnd_424956] using wordTrace_append hprefix tailTrace_424956
  have hstable : (prefixWord ++ tailWord_424956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424956).length < 2 ^ (prefixWord ++ tailWord_424956).sum := by decide
  have hdescent : baseEnd_424956 < baseStart_424956 := by decide
  rcases family_descends (prefixWord ++ tailWord_424956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424969 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 1, 8, 2]
def baseStart_424969 : Nat := 118140960795 + 424969 * 2 ^ 59
def prefixEnd_424969 : Nat := 4983230072969 + 3 ^ 40 * 424969 * 2
def baseEnd_424969 : Nat := 218213360260653040533109

theorem tailTrace_424969 : CollatzResearch.WordTrace tailWord_424969 prefixEnd_424969 218213360260653040533109 := by
  unfold tailWord_424969
  simp only [CollatzResearch.WordTrace]
  refine ⟨15499892797417366772005961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10333261864944911181337307 15499892797417366772005961)
  ·
    refine ⟨11624919598063025079004471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15499892797417366772005961 11624919598063025079004471)
    ·
      refine ⟨17437379397094537618506707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11624919598063025079004471 17437379397094537618506707)
      ·
        refine ⟨26156069095641806427760061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17437379397094537618506707 26156069095641806427760061)
        ·
          refine ⟨9808525910865677410410023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26156069095641806427760061 9808525910865677410410023)
          ·
            refine ⟨14712788866298516115615035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9808525910865677410410023 14712788866298516115615035)
            ·
              refine ⟨22069183299447774173422553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14712788866298516115615035 22069183299447774173422553)
              ·
                refine ⟨16551887474585830630066915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22069183299447774173422553 16551887474585830630066915)
                ·
                  refine ⟨24827831211878745945100373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16551887474585830630066915 24827831211878745945100373)
                  ·
                    refine ⟨290951147014204054044145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24827831211878745945100373 290951147014204054044145)
                    ·
                      refine ⟨218213360260653040533109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 290951147014204054044145 218213360260653040533109)
                      ·
                        rfl

theorem cell23_424969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 8, 2].length) (baseStart_424969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424969 prefixEnd_424969 := by exact prefixLift 424969
  have htrace : WordTrace (prefixWord ++ tailWord_424969) baseStart_424969 baseEnd_424969 := by
    simpa [prefixWord, tailWord_424969, baseEnd_424969] using wordTrace_append hprefix tailTrace_424969
  have hstable : (prefixWord ++ tailWord_424969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424969).length < 2 ^ (prefixWord ++ tailWord_424969).sum := by decide
  have hdescent : baseEnd_424969 < baseStart_424969 := by decide
  rcases family_descends (prefixWord ++ tailWord_424969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424996 : List Nat := [2, 3, 1, 4, 1, 1, 3, 1, 1, 6]
def baseStart_424996 : Nat := 118140960795 + 424996 * 2 ^ 59
def prefixEnd_424996 : Nat := 4983230072969 + 3 ^ 40 * 424996 * 2
def baseEnd_424996 : Nat := 72742408079441478298495

theorem tailTrace_424996 : CollatzResearch.WordTrace tailWord_424996 prefixEnd_424996 72742408079441478298495 := by
  unfold tailWord_424996
  simp only [CollatzResearch.WordTrace]
  refine ⟨7750438784159775191619421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10333918378879700255492561 7750438784159775191619421)
  ·
    refine ⟨2906414544059915696857283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7750438784159775191619421 2906414544059915696857283)
    ·
      refine ⟨4359621816089873545285925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2906414544059915696857283 4359621816089873545285925)
      ·
        refine ⟨817429090516851289741111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4359621816089873545285925 817429090516851289741111)
        ·
          refine ⟨1226143635775276934611667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817429090516851289741111 1226143635775276934611667)
          ·
            refine ⟨1839215453662915401917501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1226143635775276934611667 1839215453662915401917501)
            ·
              refine ⟨689705795123593275719063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1839215453662915401917501 689705795123593275719063)
              ·
                refine ⟨1034558692685389913578595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 689705795123593275719063 1034558692685389913578595)
                ·
                  refine ⟨1551838039028084870367893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1034558692685389913578595 1551838039028084870367893)
                  ·
                    refine ⟨72742408079441478298495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1551838039028084870367893 72742408079441478298495)
                    ·
                      rfl

theorem cell23_424996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_424996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_424996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_424996 prefixEnd_424996 := by exact prefixLift 424996
  have htrace : WordTrace (prefixWord ++ tailWord_424996) baseStart_424996 baseEnd_424996 := by
    simpa [prefixWord, tailWord_424996, baseEnd_424996] using wordTrace_append hprefix tailTrace_424996
  have hstable : (prefixWord ++ tailWord_424996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424996).length < 2 ^ (prefixWord ++ tailWord_424996).sum := by decide
  have hdescent : baseEnd_424996 < baseStart_424996 := by decide
  rcases family_descends (prefixWord ++ tailWord_424996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425037 : List Nat := [1, 6, 1, 1, 1, 4, 1, 1, 3, 2, 2]
def baseStart_425037 : Nat := 118140960795 + 425037 * 2 ^ 59
def prefixEnd_425037 : Nat := 4983230072969 + 3 ^ 40 * 425037 * 2
def baseEnd_425037 : Nat := 218248276945158774482797

theorem tailTrace_425037 : CollatzResearch.WordTrace tailWord_425037 prefixEnd_425037 218248276945158774482797 := by
  unfold tailWord_425037
  simp only [CollatzResearch.WordTrace]
  refine ⟨15502372961171014385481365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10334915307447342923654243 15502372961171014385481365)
  ·
    refine ⟨726673732554891299319439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15502372961171014385481365 726673732554891299319439)
    ·
      refine ⟨1090010598832336948979159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 726673732554891299319439 1090010598832336948979159)
      ·
        refine ⟨1635015898248505423468739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1090010598832336948979159 1635015898248505423468739)
        ·
          refine ⟨2452523847372758135203109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1635015898248505423468739 2452523847372758135203109)
          ·
            refine ⟨459848221382392150350583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2452523847372758135203109 459848221382392150350583)
            ·
              refine ⟨689772332073588225525875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459848221382392150350583 689772332073588225525875)
              ·
                refine ⟨1034658498110382338288813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 689772332073588225525875 1034658498110382338288813)
                ·
                  refine ⟨387996936791393376858305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1034658498110382338288813 387996936791393376858305)
                  ·
                    refine ⟨290997702593545032643729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 387996936791393376858305 290997702593545032643729)
                    ·
                      refine ⟨218248276945158774482797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 290997702593545032643729 218248276945158774482797)
                      ·
                        rfl

theorem cell23_425037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_425037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425037 prefixEnd_425037 := by exact prefixLift 425037
  have htrace : WordTrace (prefixWord ++ tailWord_425037) baseStart_425037 baseEnd_425037 := by
    simpa [prefixWord, tailWord_425037, baseEnd_425037] using wordTrace_append hprefix tailTrace_425037
  have hstable : (prefixWord ++ tailWord_425037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425037).length < 2 ^ (prefixWord ++ tailWord_425037).sum := by decide
  have hdescent : baseEnd_425037 < baseStart_425037 := by decide
  rcases family_descends (prefixWord ++ tailWord_425037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425063 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 3, 3, 2]
def baseStart_425063 : Nat := 118140960795 + 425063 * 2 ^ 59
def prefixEnd_425063 : Nat := 4983230072969 + 3 ^ 40 * 425063 * 2
def baseEnd_425063 : Nat := 218261627442175672757677

theorem tailTrace_425063 : CollatzResearch.WordTrace tailWord_425063 prefixEnd_425063 218261627442175672757677 := by
  unfold tailWord_425063
  simp only [CollatzResearch.WordTrace]
  refine ⟨15503321259076820825927843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10335547506051213883951895 15503321259076820825927843)
  ·
    refine ⟨23254981888615231238891765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15503321259076820825927843 23254981888615231238891765)
    ·
      refine ⟨2180154552057677928646103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23254981888615231238891765 2180154552057677928646103)
      ·
        refine ⟨3270231828086516892969155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2180154552057677928646103 3270231828086516892969155)
        ·
          refine ⟨4905347742129775339453733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3270231828086516892969155 4905347742129775339453733)
          ·
            refine ⟨919752701649332876147575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4905347742129775339453733 919752701649332876147575)
            ·
              refine ⟨1379629052473999314221363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 919752701649332876147575 1379629052473999314221363)
              ·
                refine ⟨2069443578710998971332045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1379629052473999314221363 2069443578710998971332045)
                ·
                  refine ⟨776041342016624614249517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2069443578710998971332045 776041342016624614249517)
                  ·
                    refine ⟨291015503256234230343569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 776041342016624614249517 291015503256234230343569)
                    ·
                      refine ⟨218261627442175672757677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 291015503256234230343569 218261627442175672757677)
                      ·
                        rfl

theorem cell23_425063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_425063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425063 prefixEnd_425063 := by exact prefixLift 425063
  have htrace : WordTrace (prefixWord ++ tailWord_425063) baseStart_425063 baseEnd_425063 := by
    simpa [prefixWord, tailWord_425063, baseEnd_425063] using wordTrace_append hprefix tailTrace_425063
  have hstable : (prefixWord ++ tailWord_425063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425063).length < 2 ^ (prefixWord ++ tailWord_425063).sum := by decide
  have hdescent : baseEnd_425063 < baseStart_425063 := by decide
  rcases family_descends (prefixWord ++ tailWord_425063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425079 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 5]
def baseStart_425079 : Nat := 118140960795 + 425079 * 2 ^ 59
def prefixEnd_425079 : Nat := 4983230072969 + 3 ^ 40 * 425079 * 2
def baseEnd_425079 : Nat := 218269843132647610157603

theorem tailTrace_425079 : CollatzResearch.WordTrace tailWord_425079 prefixEnd_425079 218269843132647610157603 := by
  unfold tailWord_425079
  simp only [CollatzResearch.WordTrace]
  refine ⟨15503904827018855558510291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10335936551345903705673527 15503904827018855558510291)
  ·
    refine ⟨23255857240528283337765437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15503904827018855558510291 23255857240528283337765437)
    ·
      refine ⟨8720946465198106251662039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23255857240528283337765437 8720946465198106251662039)
      ·
        refine ⟨13081419697797159377493059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8720946465198106251662039 13081419697797159377493059)
        ·
          refine ⟨19622129546695739066239589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13081419697797159377493059 19622129546695739066239589)
          ·
            refine ⟨3679149290005451074919923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19622129546695739066239589 3679149290005451074919923)
            ·
              refine ⟨5518723935008176612379885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3679149290005451074919923 5518723935008176612379885)
              ·
                refine ⟨2069521475628066229642457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5518723935008176612379885 2069521475628066229642457)
                ·
                  refine ⟨1552141106721049672231843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2069521475628066229642457 1552141106721049672231843)
                  ·
                    refine ⟨2328211660081574508347765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1552141106721049672231843 2328211660081574508347765)
                    ·
                      refine ⟨218269843132647610157603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2328211660081574508347765 218269843132647610157603)
                      ·
                        rfl

theorem cell23_425079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_425079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425079 prefixEnd_425079 := by exact prefixLift 425079
  have htrace : WordTrace (prefixWord ++ tailWord_425079) baseStart_425079 baseEnd_425079 := by
    simpa [prefixWord, tailWord_425079, baseEnd_425079] using wordTrace_append hprefix tailTrace_425079
  have hstable : (prefixWord ++ tailWord_425079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425079).length < 2 ^ (prefixWord ++ tailWord_425079).sum := by decide
  have hdescent : baseEnd_425079 < baseStart_425079 := by decide
  rcases family_descends (prefixWord ++ tailWord_425079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425106 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_425106 : Nat := 118140960795 + 425106 * 2 ^ 59
def prefixEnd_425106 : Nat := 4983230072969 + 3 ^ 40 * 425106 * 2
def baseEnd_425106 : Nat := 218283707110319004519979

theorem tailTrace_425106 : CollatzResearch.WordTrace tailWord_425106 prefixEnd_425106 218283707110319004519979 := by
  unfold tailWord_425106
  simp only [CollatzResearch.WordTrace]
  refine ⟨3876222399480259792435793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10336593065280692779828781 3876222399480259792435793)
  ·
    refine ⟨2907166799610194844326845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3876222399480259792435793 2907166799610194844326845)
    ·
      refine ⟨1090187549853823066622567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2907166799610194844326845 1090187549853823066622567)
      ·
        refine ⟨1635281324780734599933851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1090187549853823066622567 1635281324780734599933851)
        ·
          refine ⟨2452921987171101899900777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1635281324780734599933851 2452921987171101899900777)
          ·
            refine ⟨1839691490378326424925583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2452921987171101899900777 1839691490378326424925583)
            ·
              refine ⟨2759537235567489637388375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1839691490378326424925583 2759537235567489637388375)
              ·
                refine ⟨4139305853351234456082563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2759537235567489637388375 4139305853351234456082563)
                ·
                  refine ⟨6208958780026851684123845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4139305853351234456082563 6208958780026851684123845)
                  ·
                    refine ⟨1164179771255034690773221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6208958780026851684123845 1164179771255034690773221)
                    ·
                      refine ⟨218283707110319004519979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1164179771255034690773221 218283707110319004519979)
                      ·
                        rfl

theorem cell23_425106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_425106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425106 prefixEnd_425106 := by exact prefixLift 425106
  have htrace : WordTrace (prefixWord ++ tailWord_425106) baseStart_425106 baseEnd_425106 := by
    simpa [prefixWord, tailWord_425106, baseEnd_425106] using wordTrace_append hprefix tailTrace_425106
  have hstable : (prefixWord ++ tailWord_425106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425106).length < 2 ^ (prefixWord ++ tailWord_425106).sum := by decide
  have hdescent : baseEnd_425106 < baseStart_425106 := by decide
  rcases family_descends (prefixWord ++ tailWord_425106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425116 : List Nat := [2, 2, 3, 2, 1, 3, 1, 2, 7]
def baseStart_425116 : Nat := 118140960795 + 425116 * 2 ^ 59
def prefixEnd_425116 : Nat := 4983230072969 + 3 ^ 40 * 425116 * 2
def baseEnd_425116 : Nat := 24254315768540440599437

theorem tailTrace_425116 : CollatzResearch.WordTrace tailWord_425116 prefixEnd_425116 24254315768540440599437 := by
  unfold tailWord_425116
  simp only [CollatzResearch.WordTrace]
  refine ⟨7752627163942405438803601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10336836218589873918404801 7752627163942405438803601)
  ·
    refine ⟨5814470372956804079102701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7752627163942405438803601 5814470372956804079102701)
    ·
      refine ⟨2180426389858801529663513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5814470372956804079102701 2180426389858801529663513)
      ·
        refine ⟨1635319792394101147247635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2180426389858801529663513 1635319792394101147247635)
        ·
          refine ⟨2452979688591151720871453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1635319792394101147247635 2452979688591151720871453)
          ·
            refine ⟨919867383221681895326795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2452979688591151720871453 919867383221681895326795)
            ·
              refine ⟨1379801074832522842990193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 919867383221681895326795 1379801074832522842990193)
              ·
                refine ⟨1034850806124392132242645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1379801074832522842990193 1034850806124392132242645)
                ·
                  refine ⟨24254315768540440599437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1034850806124392132242645 24254315768540440599437)
                  ·
                    rfl

theorem cell23_425116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 7].length) (baseStart_425116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425116 prefixEnd_425116 := by exact prefixLift 425116
  have htrace : WordTrace (prefixWord ++ tailWord_425116) baseStart_425116 baseEnd_425116 := by
    simpa [prefixWord, tailWord_425116, baseEnd_425116] using wordTrace_append hprefix tailTrace_425116
  have hstable : (prefixWord ++ tailWord_425116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425116).length < 2 ^ (prefixWord ++ tailWord_425116).sum := by decide
  have hdescent : baseEnd_425116 < baseStart_425116 := by decide
  rcases family_descends (prefixWord ++ tailWord_425116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425129 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 8, 5]
def baseStart_425129 : Nat := 118140960795 + 425129 * 2 ^ 59
def prefixEnd_425129 : Nat := 4983230072969 + 3 ^ 40 * 425129 * 2
def baseEnd_425129 : Nat := 72765172388457471510791

theorem tailTrace_425129 : CollatzResearch.WordTrace tailWord_425129 prefixEnd_425129 72765172388457471510791 := by
  unfold tailWord_425129
  simp only [CollatzResearch.WordTrace]
  refine ⟨15505728476837714097830441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10337152317891809398553627 15505728476837714097830441)
  ·
    refine ⟨11629296357628285573372831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15505728476837714097830441 11629296357628285573372831)
    ·
      refine ⟨17443944536442428360059247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11629296357628285573372831 17443944536442428360059247)
      ·
        refine ⟨26165916804663642540088871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17443944536442428360059247 26165916804663642540088871)
        ·
          refine ⟨39248875206995463810133307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26165916804663642540088871 39248875206995463810133307)
          ·
            refine ⟨58873312810493195715199961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39248875206995463810133307 58873312810493195715199961)
            ·
              refine ⟨44154984607869896786399971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58873312810493195715199961 44154984607869896786399971)
              ·
                refine ⟨66232476911804845179599957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44154984607869896786399971 66232476911804845179599957)
                ·
                  refine ⟨776161838810213029448437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 66232476911804845179599957 776161838810213029448437)
                  ·
                    refine ⟨72765172388457471510791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 776161838810213029448437 72765172388457471510791)
                    ·
                      rfl

theorem cell23_425129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 5].length) (baseStart_425129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425129 prefixEnd_425129 := by exact prefixLift 425129
  have htrace : WordTrace (prefixWord ++ tailWord_425129) baseStart_425129 baseEnd_425129 := by
    simpa [prefixWord, tailWord_425129, baseEnd_425129] using wordTrace_append hprefix tailTrace_425129
  have hstable : (prefixWord ++ tailWord_425129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425129).length < 2 ^ (prefixWord ++ tailWord_425129).sum := by decide
  have hdescent : baseEnd_425129 < baseStart_425129 := by decide
  rcases family_descends (prefixWord ++ tailWord_425129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425136 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 4, 5, 2]
def baseStart_425136 : Nat := 118140960795 + 425136 * 2 ^ 59
def prefixEnd_425136 : Nat := 4983230072969 + 3 ^ 40 * 425136 * 2
def baseEnd_425136 : Nat := 218299111529953887144841

theorem tailTrace_425136 : CollatzResearch.WordTrace tailWord_425136 prefixEnd_425136 218299111529953887144841 := by
  unfold tailWord_425136
  simp only [CollatzResearch.WordTrace]
  refine ⟨7752991893906177146667631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10337322525208236195556841 7752991893906177146667631)
  ·
    refine ⟨11629487840859265720001447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7752991893906177146667631 11629487840859265720001447)
    ·
      refine ⟨17444231761288898580002171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11629487840859265720001447 17444231761288898580002171)
      ·
        refine ⟨26166347641933347870003257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17444231761288898580002171 26166347641933347870003257)
        ·
          refine ⟨19624760731450010902502443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26166347641933347870003257 19624760731450010902502443)
          ·
            refine ⟨29437141097175016353753665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19624760731450010902502443 29437141097175016353753665)
            ·
              refine ⟨22077855822881262265315249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29437141097175016353753665 22077855822881262265315249)
              ·
                refine ⟨16558391867160946698986437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22077855822881262265315249 16558391867160946698986437)
                ·
                  refine ⟨3104698475092677506059957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16558391867160946698986437 3104698475092677506059957)
                  ·
                    refine ⟨291065482039938516193121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3104698475092677506059957 291065482039938516193121)
                    ·
                      refine ⟨218299111529953887144841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 291065482039938516193121 218299111529953887144841)
                      ·
                        rfl

theorem cell23_425136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 4, 5, 2].length) (baseStart_425136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425136 prefixEnd_425136 := by exact prefixLift 425136
  have htrace : WordTrace (prefixWord ++ tailWord_425136) baseStart_425136 baseEnd_425136 := by
    simpa [prefixWord, tailWord_425136, baseEnd_425136] using wordTrace_append hprefix tailTrace_425136
  have hstable : (prefixWord ++ tailWord_425136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425136).length < 2 ^ (prefixWord ++ tailWord_425136).sum := by decide
  have hdescent : baseEnd_425136 < baseStart_425136 := by decide
  rcases family_descends (prefixWord ++ tailWord_425136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425139 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 5]
def baseStart_425139 : Nat := 118140960795 + 425139 * 2 ^ 59
def prefixEnd_425139 : Nat := 4983230072969 + 3 ^ 40 * 425139 * 2
def baseEnd_425139 : Nat := 218300651971917375407327

theorem tailTrace_425139 : CollatzResearch.WordTrace tailWord_425139 prefixEnd_425139 218300651971917375407327 := by
  unfold tailWord_425139
  simp only [CollatzResearch.WordTrace]
  refine ⟨15506093206801485805694471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10337395471200990537129647 15506093206801485805694471)
  ·
    refine ⟨23259139810202228708541707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15506093206801485805694471 23259139810202228708541707)
    ·
      refine ⟨34888709715303343062812561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23259139810202228708541707 34888709715303343062812561)
      ·
        refine ⟨26166532286477507297109421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34888709715303343062812561 26166532286477507297109421)
        ·
          refine ⟨9812449607429065236416033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26166532286477507297109421 9812449607429065236416033)
          ·
            refine ⟨7359337205571798927312025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9812449607429065236416033 7359337205571798927312025)
            ·
              refine ⟨5519502904178849195484019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7359337205571798927312025 5519502904178849195484019)
              ·
                refine ⟨8279254356268273793226029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5519502904178849195484019 8279254356268273793226029)
                ·
                  refine ⟨3104720383600602672459761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8279254356268273793226029 3104720383600602672459761)
                  ·
                    refine ⟨2328540287700452004344821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3104720383600602672459761 2328540287700452004344821)
                    ·
                      refine ⟨218300651971917375407327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2328540287700452004344821 218300651971917375407327)
                      ·
                        rfl

theorem cell23_425139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_425139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425139 prefixEnd_425139 := by exact prefixLift 425139
  have htrace : WordTrace (prefixWord ++ tailWord_425139) baseStart_425139 baseEnd_425139 := by
    simpa [prefixWord, tailWord_425139, baseEnd_425139] using wordTrace_append hprefix tailTrace_425139
  have hstable : (prefixWord ++ tailWord_425139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425139).length < 2 ^ (prefixWord ++ tailWord_425139).sum := by decide
  have hdescent : baseEnd_425139 < baseStart_425139 := by decide
  rcases family_descends (prefixWord ++ tailWord_425139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425203 : List Nat := [1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 3]
def baseStart_425203 : Nat := 118140960795 + 425203 * 2 ^ 59
def prefixEnd_425203 : Nat := 4983230072969 + 3 ^ 40 * 425203 * 2
def baseEnd_425203 : Nat := 218333514733805125007033

theorem tailTrace_425203 : CollatzResearch.WordTrace tailWord_425203 prefixEnd_425203 218333514733805125007033 := by
  unfold tailWord_425203
  simp only [CollatzResearch.WordTrace]
  refine ⟨15508427478569624736024263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10338951652379749824016175 15508427478569624736024263)
  ·
    refine ⟨23262641217854437104036395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15508427478569624736024263 23262641217854437104036395)
    ·
      refine ⟨34893961826781655656054593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23262641217854437104036395 34893961826781655656054593)
      ·
        refine ⟨26170471370086241742040945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34893961826781655656054593 26170471370086241742040945)
        ·
          refine ⟨19627853527564681306530709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26170471370086241742040945 19627853527564681306530709)
          ·
            refine ⟨920055634104594436243627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19627853527564681306530709 920055634104594436243627)
            ·
              refine ⟨1380083451156891654365441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920055634104594436243627 1380083451156891654365441)
              ·
                refine ⟨1035062588367668740774081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1380083451156891654365441 1035062588367668740774081)
                ·
                  refine ⟨776296941275751555580561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1035062588367668740774081 776296941275751555580561)
                  ·
                    refine ⟨582222705956813666685421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 776296941275751555580561 582222705956813666685421)
                    ·
                      refine ⟨218333514733805125007033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 582222705956813666685421 218333514733805125007033)
                      ·
                        rfl

theorem cell23_425203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 3].length) (baseStart_425203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425203 prefixEnd_425203 := by exact prefixLift 425203
  have htrace : WordTrace (prefixWord ++ tailWord_425203) baseStart_425203 baseEnd_425203 := by
    simpa [prefixWord, tailWord_425203, baseEnd_425203] using wordTrace_append hprefix tailTrace_425203
  have hstable : (prefixWord ++ tailWord_425203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425203).length < 2 ^ (prefixWord ++ tailWord_425203).sum := by decide
  have hdescent : baseEnd_425203 < baseStart_425203 := by decide
  rcases family_descends (prefixWord ++ tailWord_425203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425233 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 5, 1, 3]
def baseStart_425233 : Nat := 118140960795 + 425233 * 2 ^ 59
def prefixEnd_425233 : Nat := 4983230072969 + 3 ^ 40 * 425233 * 2
def baseEnd_425233 : Nat := 218348919153440007631895

theorem tailTrace_425233 : CollatzResearch.WordTrace tailWord_425233 prefixEnd_425233 218348919153440007631895 := by
  unfold tailWord_425233
  simp only [CollatzResearch.WordTrace]
  refine ⟨15509521668460939859616353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10339681112307293239744235 15509521668460939859616353)
  ·
    refine ⟨11632141251345704894712265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15509521668460939859616353 11632141251345704894712265)
    ·
      refine ⟨8724105938509278671034199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11632141251345704894712265 8724105938509278671034199)
      ·
        refine ⟨13086158907763918006551299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8724105938509278671034199 13086158907763918006551299)
        ·
          refine ⟨19629238361645877009826949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13086158907763918006551299 19629238361645877009826949)
          ·
            refine ⟨3680482192808601939342553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19629238361645877009826949 3680482192808601939342553)
            ·
              refine ⟨2760361644606451454506915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3680482192808601939342553 2760361644606451454506915)
              ·
                refine ⟨4140542466909677181760373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2760361644606451454506915 4140542466909677181760373)
                ·
                  refine ⟨388175856272782235790035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4140542466909677181760373 388175856272782235790035)
                  ·
                    refine ⟨582263784409173353685053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 388175856272782235790035 582263784409173353685053)
                    ·
                      refine ⟨218348919153440007631895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 582263784409173353685053 218348919153440007631895)
                      ·
                        rfl

theorem cell23_425233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 1, 3].length) (baseStart_425233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425233 prefixEnd_425233 := by exact prefixLift 425233
  have htrace : WordTrace (prefixWord ++ tailWord_425233) baseStart_425233 baseEnd_425233 := by
    simpa [prefixWord, tailWord_425233, baseEnd_425233] using wordTrace_append hprefix tailTrace_425233
  have hstable : (prefixWord ++ tailWord_425233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425233).length < 2 ^ (prefixWord ++ tailWord_425233).sum := by decide
  have hdescent : baseEnd_425233 < baseStart_425233 := by decide
  rcases family_descends (prefixWord ++ tailWord_425233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425261 : List Nat := [1, 5, 3, 1, 1, 3, 2, 2, 1, 4]
def baseStart_425261 : Nat := 118140960795 + 425261 * 2 ^ 59
def prefixEnd_425261 : Nat := 4983230072969 + 3 ^ 40 * 425261 * 2
def baseEnd_425261 : Nat := 72787765537255299360589

theorem tailTrace_425261 : CollatzResearch.WordTrace tailWord_425261 prefixEnd_425261 72787765537255299360589 := by
  unfold tailWord_425261
  simp only [CollatzResearch.WordTrace]
  refine ⟨15510542912359500641635637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10340361941573000427757091 15510542912359500641635637)
  ·
    refine ⟨1454113398033703185153341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15510542912359500641635637 1454113398033703185153341)
    ·
      refine ⟨545292524262638694432503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1454113398033703185153341 545292524262638694432503)
      ·
        refine ⟨817938786393958041648755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545292524262638694432503 817938786393958041648755)
        ·
          refine ⟨1226908179590937062473133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817938786393958041648755 1226908179590937062473133)
          ·
            refine ⟨460090567346601398427425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1226908179590937062473133 460090567346601398427425)
            ·
              refine ⟨345067925509951048820569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460090567346601398427425 345067925509951048820569)
              ·
                refine ⟨258800944132463286615427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345067925509951048820569 258800944132463286615427)
                ·
                  refine ⟨388201416198694929923141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258800944132463286615427 388201416198694929923141)
                  ·
                    refine ⟨72787765537255299360589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 388201416198694929923141 72787765537255299360589)
                    ·
                      rfl

theorem cell23_425261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_425261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425261 prefixEnd_425261 := by exact prefixLift 425261
  have htrace : WordTrace (prefixWord ++ tailWord_425261) baseStart_425261 baseEnd_425261 := by
    simpa [prefixWord, tailWord_425261, baseEnd_425261] using wordTrace_append hprefix tailTrace_425261
  have hstable : (prefixWord ++ tailWord_425261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425261).length < 2 ^ (prefixWord ++ tailWord_425261).sum := by decide
  have hdescent : baseEnd_425261 < baseStart_425261 := by decide
  rcases family_descends (prefixWord ++ tailWord_425261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425267 : List Nat := [1, 1, 1, 2, 5, 3, 1, 4, 1, 1, 3]
def baseStart_425267 : Nat := 118140960795 + 425267 * 2 ^ 59
def prefixEnd_425267 : Nat := 4983230072969 + 3 ^ 40 * 425267 * 2
def baseEnd_425267 : Nat := 218366377495692874606739

theorem tailTrace_425267 : CollatzResearch.WordTrace tailWord_425267 prefixEnd_425267 218366377495692874606739 := by
  unfold tailWord_425267
  simp only [CollatzResearch.WordTrace]
  refine ⟨15510761750337763666354055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10340507833558509110902703 15510761750337763666354055)
  ·
    refine ⟨23266142625506645499531083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15510761750337763666354055 23266142625506645499531083)
    ·
      refine ⟨34899213938259968249296625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23266142625506645499531083 34899213938259968249296625)
      ·
        refine ⟨26174410453694976186972469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34899213938259968249296625 26174410453694976186972469)
        ·
          refine ⟨2453850980033904017528669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26174410453694976186972469 2453850980033904017528669)
          ·
            refine ⟨920194117512714006573251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2453850980033904017528669 920194117512714006573251)
            ·
              refine ⟨1380291176269071009859877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920194117512714006573251 1380291176269071009859877)
              ·
                refine ⟨258804595550450814348727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1380291176269071009859877 258804595550450814348727)
                ·
                  refine ⟨388206893325676221523091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258804595550450814348727 388206893325676221523091)
                  ·
                    refine ⟨582310339988514332284637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 388206893325676221523091 582310339988514332284637)
                    ·
                      refine ⟨218366377495692874606739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 582310339988514332284637 218366377495692874606739)
                      ·
                        rfl

theorem cell23_425267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 1, 1, 3].length) (baseStart_425267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425267 prefixEnd_425267 := by exact prefixLift 425267
  have htrace : WordTrace (prefixWord ++ tailWord_425267) baseStart_425267 baseEnd_425267 := by
    simpa [prefixWord, tailWord_425267, baseEnd_425267] using wordTrace_append hprefix tailTrace_425267
  have hstable : (prefixWord ++ tailWord_425267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425267).length < 2 ^ (prefixWord ++ tailWord_425267).sum := by decide
  have hdescent : baseEnd_425267 < baseStart_425267 := by decide
  rcases family_descends (prefixWord ++ tailWord_425267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425303 : List Nat := [1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 4]
def baseStart_425303 : Nat := 118140960795 + 425303 * 2 ^ 59
def prefixEnd_425303 : Nat := 4983230072969 + 3 ^ 40 * 425303 * 2
def baseEnd_425303 : Nat := 218384862799254733756573

theorem tailTrace_425303 : CollatzResearch.WordTrace tailWord_425303 prefixEnd_425303 218384862799254733756573 := by
  unfold tailWord_425303
  simp only [CollatzResearch.WordTrace]
  refine ⟨15512074778207341814664563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10341383185471561209776375 15512074778207341814664563)
  ·
    refine ⟨23268112167311012721996845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15512074778207341814664563 23268112167311012721996845)
    ·
      refine ⟨8725542062741629770748817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23268112167311012721996845 8725542062741629770748817)
      ·
        refine ⟨6544156547056222328061613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8725542062741629770748817 6544156547056222328061613)
        ·
          refine ⟨2454058705146083373023105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6544156547056222328061613 2454058705146083373023105)
          ·
            refine ⟨1840544028859562529767329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2454058705146083373023105 1840544028859562529767329)
            ·
              refine ⟨1380408021644671897325497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1840544028859562529767329 1380408021644671897325497)
              ·
                refine ⟨1035306016233503922994123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1380408021644671897325497 1035306016233503922994123)
                ·
                  refine ⟨1552959024350255884491185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1035306016233503922994123 1552959024350255884491185)
                  ·
                    refine ⟨1164719268262691913368389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1552959024350255884491185 1164719268262691913368389)
                    ·
                      refine ⟨218384862799254733756573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1164719268262691913368389 218384862799254733756573)
                      ·
                        rfl

theorem cell23_425303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_425303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425303 prefixEnd_425303 := by exact prefixLift 425303
  have htrace : WordTrace (prefixWord ++ tailWord_425303) baseStart_425303 baseEnd_425303 := by
    simpa [prefixWord, tailWord_425303, baseEnd_425303] using wordTrace_append hprefix tailTrace_425303
  have hstable : (prefixWord ++ tailWord_425303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425303).length < 2 ^ (prefixWord ++ tailWord_425303).sum := by decide
  have hdescent : baseEnd_425303 < baseStart_425303 := by decide
  rcases family_descends (prefixWord ++ tailWord_425303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425324 : List Nat := [2, 2, 1, 1, 5, 1, 2, 4, 1, 2, 2]
def baseStart_425324 : Nat := 118140960795 + 425324 * 2 ^ 59
def prefixEnd_425324 : Nat := 4983230072969 + 3 ^ 40 * 425324 * 2
def baseEnd_425324 : Nat := 218395645892999151593977

theorem tailTrace_425324 : CollatzResearch.WordTrace tailWord_425324 prefixEnd_425324 218395645892999151593977 := by
  unfold tailWord_425324
  simp only [CollatzResearch.WordTrace]
  refine ⟨7756420355565631200589513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10341893807420841600786017 7756420355565631200589513)
  ·
    refine ⟨5817315266674223400442135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7756420355565631200589513 5817315266674223400442135)
    ·
      refine ⟨8725972900011335100663203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5817315266674223400442135 8725972900011335100663203)
      ·
        refine ⟨13088959350017002650994805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8725972900011335100663203 13088959350017002650994805)
        ·
          refine ⟨1227089939064093998530763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13088959350017002650994805 1227089939064093998530763)
          ·
            refine ⟨1840634908596140997796145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1227089939064093998530763 1840634908596140997796145)
            ·
              refine ⟨1380476181447105748347109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1840634908596140997796145 1380476181447105748347109)
              ·
                refine ⟨258839284021332327815083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1380476181447105748347109 258839284021332327815083)
                ·
                  refine ⟨388258926031998491722625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258839284021332327815083 388258926031998491722625)
                  ·
                    refine ⟨291194194523998868791969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 388258926031998491722625 291194194523998868791969)
                    ·
                      refine ⟨218395645892999151593977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 291194194523998868791969 218395645892999151593977)
                      ·
                        rfl

theorem cell23_425324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 1, 2, 2].length) (baseStart_425324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425324 prefixEnd_425324 := by exact prefixLift 425324
  have htrace : WordTrace (prefixWord ++ tailWord_425324) baseStart_425324 baseEnd_425324 := by
    simpa [prefixWord, tailWord_425324, baseEnd_425324] using wordTrace_append hprefix tailTrace_425324
  have hstable : (prefixWord ++ tailWord_425324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425324).length < 2 ^ (prefixWord ++ tailWord_425324).sum := by decide
  have hdescent : baseEnd_425324 < baseStart_425324 := by decide
  rcases family_descends (prefixWord ++ tailWord_425324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425336 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 6, 2, 5]
def baseStart_425336 : Nat := 118140960795 + 425336 * 2 ^ 59
def prefixEnd_425336 : Nat := 4983230072969 + 3 ^ 40 * 425336 * 2
def baseEnd_425336 : Nat := 218401807660853104643921

theorem tailTrace_425336 : CollatzResearch.WordTrace tailWord_425336 prefixEnd_425336 218401807660853104643921 := by
  unfold tailWord_425336
  simp only [CollatzResearch.WordTrace]
  refine ⟨7756639193543894225307931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10342185591391858967077241 7756639193543894225307931)
  ·
    refine ⟨11634958790315841337961897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7756639193543894225307931 11634958790315841337961897)
    ·
      refine ⟨8726219092736881003471423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11634958790315841337961897 8726219092736881003471423)
      ·
        refine ⟨13089328639105321505207135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8726219092736881003471423 13089328639105321505207135)
        ·
          refine ⟨19633992958657982257810703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13089328639105321505207135 19633992958657982257810703)
          ·
            refine ⟨29450989437986973386716055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19633992958657982257810703 29450989437986973386716055)
            ·
              refine ⟨44176484156980460080074083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29450989437986973386716055 44176484156980460080074083)
              ·
                refine ⟨66264726235470690120111125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44176484156980460080074083 66264726235470690120111125)
                ·
                  refine ⟨3106159042287688599380209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66264726235470690120111125 3106159042287688599380209)
                  ·
                    refine ⟨2329619281715766449535157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3106159042287688599380209 2329619281715766449535157)
                    ·
                      refine ⟨218401807660853104643921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2329619281715766449535157 218401807660853104643921)
                      ·
                        rfl

theorem cell23_425336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_425336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425336 prefixEnd_425336 := by exact prefixLift 425336
  have htrace : WordTrace (prefixWord ++ tailWord_425336) baseStart_425336 baseEnd_425336 := by
    simpa [prefixWord, tailWord_425336, baseEnd_425336] using wordTrace_append hprefix tailTrace_425336
  have hstable : (prefixWord ++ tailWord_425336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425336).length < 2 ^ (prefixWord ++ tailWord_425336).sum := by decide
  have hdescent : baseEnd_425336 < baseStart_425336 := by decide
  rcases family_descends (prefixWord ++ tailWord_425336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425358 : List Nat := [4, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2]
def baseStart_425358 : Nat := 118140960795 + 425358 * 2 ^ 59
def prefixEnd_425358 : Nat := 4983230072969 + 3 ^ 40 * 425358 * 2
def baseEnd_425358 : Nat := 218413104235252018568821

theorem tailTrace_425358 : CollatzResearch.WordTrace tailWord_425358 prefixEnd_425358 218413104235252018568821 := by
  unfold tailWord_425358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1939260099126010775989591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10342720528672057471944485 1939260099126010775989591)
  ·
    refine ⟨2908890148689016163984387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1939260099126010775989591 2908890148689016163984387)
    ·
      refine ⟨4363335223033524245976581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2908890148689016163984387 4363335223033524245976581)
      ·
        refine ⟨818125354318785796120609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4363335223033524245976581 818125354318785796120609)
        ·
          refine ⟨613594015739089347090457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 818125354318785796120609 613594015739089347090457)
          ·
            refine ⟨460195511804317010317843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 613594015739089347090457 460195511804317010317843)
            ·
              refine ⟨690293267706475515476765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460195511804317010317843 690293267706475515476765)
              ·
                refine ⟨258859975389928318303787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 690293267706475515476765 258859975389928318303787)
                ·
                  refine ⟨388289963084892477455681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258859975389928318303787 388289963084892477455681)
                  ·
                    refine ⟨291217472313669358091761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 388289963084892477455681 291217472313669358091761)
                    ·
                      refine ⟨218413104235252018568821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 291217472313669358091761 218413104235252018568821)
                      ·
                        rfl

theorem cell23_425358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_425358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425358 prefixEnd_425358 := by exact prefixLift 425358
  have htrace : WordTrace (prefixWord ++ tailWord_425358) baseStart_425358 baseEnd_425358 := by
    simpa [prefixWord, tailWord_425358, baseEnd_425358] using wordTrace_append hprefix tailTrace_425358
  have hstable : (prefixWord ++ tailWord_425358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425358).length < 2 ^ (prefixWord ++ tailWord_425358).sum := by decide
  have hdescent : baseEnd_425358 < baseStart_425358 := by decide
  rcases family_descends (prefixWord ++ tailWord_425358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425383 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_425383 : Nat := 118140960795 + 425383 * 2 ^ 59
def prefixEnd_425383 : Nat := 4983230072969 + 3 ^ 40 * 425383 * 2
def baseEnd_425383 : Nat := 218425941251614420756205

theorem tailTrace_425383 : CollatzResearch.WordTrace tailWord_425383 prefixEnd_425383 218425941251614420756205 := by
  unfold tailWord_425383
  simp only [CollatzResearch.WordTrace]
  refine ⟨15514992617917515477576803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10343328411945010318384535 15514992617917515477576803)
  ·
    refine ⟨23272488926876273216365205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15514992617917515477576803 23272488926876273216365205)
    ·
      refine ⟨1090897918447325307017119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23272488926876273216365205 1090897918447325307017119)
      ·
        refine ⟨1636346877670987960525679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1090897918447325307017119 1636346877670987960525679)
        ·
          refine ⟨2454520316506481940788519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1636346877670987960525679 2454520316506481940788519)
          ·
            refine ⟨3681780474759722911182779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2454520316506481940788519 3681780474759722911182779)
            ·
              refine ⟨5522670712139584366774169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3681780474759722911182779 5522670712139584366774169)
              ·
                refine ⟨4142003034104688275080627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5522670712139584366774169 4142003034104688275080627)
                ·
                  refine ⟨6213004551157032412620941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4142003034104688275080627 6213004551157032412620941)
                  ·
                    refine ⟨2329876706683887154732853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6213004551157032412620941 2329876706683887154732853)
                    ·
                      refine ⟨218425941251614420756205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2329876706683887154732853 218425941251614420756205)
                      ·
                        rfl

theorem cell23_425383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_425383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425383 prefixEnd_425383 := by exact prefixLift 425383
  have htrace : WordTrace (prefixWord ++ tailWord_425383) baseStart_425383 baseEnd_425383 := by
    simpa [prefixWord, tailWord_425383, baseEnd_425383] using wordTrace_append hprefix tailTrace_425383
  have hstable : (prefixWord ++ tailWord_425383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425383).length < 2 ^ (prefixWord ++ tailWord_425383).sum := by decide
  have hdescent : baseEnd_425383 < baseStart_425383 := by decide
  rcases family_descends (prefixWord ++ tailWord_425383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425393 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 1, 4, 4]
def baseStart_425393 : Nat := 118140960795 + 425393 * 2 ^ 59
def prefixEnd_425393 : Nat := 4983230072969 + 3 ^ 40 * 425393 * 2
def baseEnd_425393 : Nat := 218431076058159381631159

theorem tailTrace_425393 : CollatzResearch.WordTrace tailWord_425393 prefixEnd_425393 218431076058159381631159 := by
  unfold tailWord_425393
  simp only [CollatzResearch.WordTrace]
  refine ⟨15515357347881287185440833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10343571565254191456960555 15515357347881287185440833)
  ·
    refine ⟨11636518010910965389080625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15515357347881287185440833 11636518010910965389080625)
    ·
      refine ⟨8727388508183224041810469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11636518010910965389080625 8727388508183224041810469)
      ·
        refine ⟨1636385345284354507839463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8727388508183224041810469 1636385345284354507839463)
        ·
          refine ⟨2454578017926531761759195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1636385345284354507839463 2454578017926531761759195)
          ·
            refine ⟨3681867026889797642638793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2454578017926531761759195 3681867026889797642638793)
            ·
              refine ⟨2761400270167348231979095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3681867026889797642638793 2761400270167348231979095)
              ·
                refine ⟨4142100405251022347968643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2761400270167348231979095 4142100405251022347968643)
                ·
                  refine ⟨6213150607876533521952965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4142100405251022347968643 6213150607876533521952965)
                  ·
                    refine ⟨1164965738976850035366181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6213150607876533521952965 1164965738976850035366181)
                    ·
                      refine ⟨218431076058159381631159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1164965738976850035366181 218431076058159381631159)
                      ·
                        rfl

theorem cell23_425393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_425393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425393 prefixEnd_425393 := by exact prefixLift 425393
  have htrace : WordTrace (prefixWord ++ tailWord_425393) baseStart_425393 baseEnd_425393 := by
    simpa [prefixWord, tailWord_425393, baseEnd_425393] using wordTrace_append hprefix tailTrace_425393
  have hstable : (prefixWord ++ tailWord_425393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425393).length < 2 ^ (prefixWord ++ tailWord_425393).sum := by decide
  have hdescent : baseEnd_425393 < baseStart_425393 := by decide
  rcases family_descends (prefixWord ++ tailWord_425393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425401 : List Nat := [1, 2, 1, 4, 5, 1, 1, 2, 1, 3, 2]
def baseStart_425401 : Nat := 118140960795 + 425401 * 2 ^ 59
def prefixEnd_425401 : Nat := 4983230072969 + 3 ^ 40 * 425401 * 2
def baseEnd_425401 : Nat := 218435183903395350331123

theorem tailTrace_425401 : CollatzResearch.WordTrace tailWord_425401 prefixEnd_425401 218435183903395350331123 := by
  unfold tailWord_425401
  simp only [CollatzResearch.WordTrace]
  refine ⟨15515649131852304551732057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10343766087901536367821371 15515649131852304551732057)
  ·
    refine ⟨11636736848889228413799043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15515649131852304551732057 11636736848889228413799043)
    ·
      refine ⟨17455105273333842620698565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11636736848889228413799043 17455105273333842620698565)
      ·
        refine ⟨3272832238750095491380981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17455105273333842620698565 3272832238750095491380981)
        ·
          refine ⟨306828022382821452316967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3272832238750095491380981 306828022382821452316967)
          ·
            refine ⟨460242033574232178475451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306828022382821452316967 460242033574232178475451)
            ·
              refine ⟨690363050361348267713177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460242033574232178475451 690363050361348267713177)
              ·
                refine ⟨517772287771011200784883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 690363050361348267713177 517772287771011200784883)
                ·
                  refine ⟨776658431656516801177325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 517772287771011200784883 776658431656516801177325)
                  ·
                    refine ⟨291246911871193800441497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 776658431656516801177325 291246911871193800441497)
                    ·
                      refine ⟨218435183903395350331123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 291246911871193800441497 218435183903395350331123)
                      ·
                        rfl

theorem cell23_425401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_425401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425401 prefixEnd_425401 := by exact prefixLift 425401
  have htrace : WordTrace (prefixWord ++ tailWord_425401) baseStart_425401 baseEnd_425401 := by
    simpa [prefixWord, tailWord_425401, baseEnd_425401] using wordTrace_append hprefix tailTrace_425401
  have hstable : (prefixWord ++ tailWord_425401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425401).length < 2 ^ (prefixWord ++ tailWord_425401).sum := by decide
  have hdescent : baseEnd_425401 < baseStart_425401 := by decide
  rcases family_descends (prefixWord ++ tailWord_425401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425437 : List Nat := [1, 4, 3, 1, 1, 3, 1, 4, 5]
def baseStart_425437 : Nat := 118140960795 + 425437 * 2 ^ 59
def prefixEnd_425437 : Nat := 4983230072969 + 3 ^ 40 * 425437 * 2
def baseEnd_425437 : Nat := 24272629911884134386773

theorem tailTrace_425437 : CollatzResearch.WordTrace tailWord_425437 prefixEnd_425437 24272629911884134386773 := by
  unfold tailWord_425437
  simp only [CollatzResearch.WordTrace]
  refine ⟨15516962159721882700042565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10344641439814588466695043 15516962159721882700042565)
  ·
    refine ⟨2909430404947853006257981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15516962159721882700042565 2909430404947853006257981)
    ·
      refine ⟨1091036401855444877346743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2909430404947853006257981 1091036401855444877346743)
      ·
        refine ⟨1636554602783167316020115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1091036401855444877346743 1636554602783167316020115)
        ·
          refine ⟨2454831904174750974030173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1636554602783167316020115 2454831904174750974030173)
          ·
            refine ⟨920561964065531615261315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2454831904174750974030173 920561964065531615261315)
            ·
              refine ⟨1380842946098297422891973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920561964065531615261315 1380842946098297422891973)
              ·
                refine ⟨258908052393430766792245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1380842946098297422891973 258908052393430766792245)
                ·
                  refine ⟨24272629911884134386773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 258908052393430766792245 24272629911884134386773)
                  ·
                    rfl

theorem cell23_425437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_425437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425437 prefixEnd_425437 := by exact prefixLift 425437
  have htrace : WordTrace (prefixWord ++ tailWord_425437) baseStart_425437 baseEnd_425437 := by
    simpa [prefixWord, tailWord_425437, baseEnd_425437] using wordTrace_append hprefix tailTrace_425437
  have hstable : (prefixWord ++ tailWord_425437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425437).length < 2 ^ (prefixWord ++ tailWord_425437).sum := by decide
  have hdescent : baseEnd_425437 < baseStart_425437 := by decide
  rcases family_descends (prefixWord ++ tailWord_425437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425554 : List Nat := [3, 2, 2, 1, 2, 2, 3, 1, 3, 1, 3]
def baseStart_425554 : Nat := 118140960795 + 425554 * 2 ^ 59
def prefixEnd_425554 : Nat := 4983230072969 + 3 ^ 40 * 425554 * 2
def baseEnd_425554 : Nat := 218513746443533251717919

theorem tailTrace_425554 : CollatzResearch.WordTrace tailWord_425554 prefixEnd_425554 218513746443533251717919 := by
  unfold tailWord_425554
  simp only [CollatzResearch.WordTrace]
  refine ⟨3880307375074502920512929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10347486333532007788034477 3880307375074502920512929)
  ·
    refine ⟨2910230531305877190384697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3880307375074502920512929 2910230531305877190384697)
    ·
      refine ⟨2182672898479407892788523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2910230531305877190384697 2182672898479407892788523)
      ·
        refine ⟨3274009347719111839182785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2182672898479407892788523 3274009347719111839182785)
        ·
          refine ⟨2455507010789333879387089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3274009347719111839182785 2455507010789333879387089)
          ·
            refine ⟨1841630258092000409540317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2455507010789333879387089 1841630258092000409540317)
            ·
              refine ⟨690611346784500153577619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1841630258092000409540317 690611346784500153577619)
              ·
                refine ⟨1035917020176750230366429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 690611346784500153577619 1035917020176750230366429)
                ·
                  refine ⟨388468882566281336387411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1035917020176750230366429 388468882566281336387411)
                  ·
                    refine ⟨582703323849422004581117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 388468882566281336387411 582703323849422004581117)
                    ·
                      refine ⟨218513746443533251717919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 582703323849422004581117 218513746443533251717919)
                      ·
                        rfl

theorem cell23_425554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_425554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425554 prefixEnd_425554 := by exact prefixLift 425554
  have htrace : WordTrace (prefixWord ++ tailWord_425554) baseStart_425554 baseEnd_425554 := by
    simpa [prefixWord, tailWord_425554, baseEnd_425554] using wordTrace_append hprefix tailTrace_425554
  have hstable : (prefixWord ++ tailWord_425554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425554).length < 2 ^ (prefixWord ++ tailWord_425554).sum := by decide
  have hdescent : baseEnd_425554 < baseStart_425554 := by decide
  rcases family_descends (prefixWord ++ tailWord_425554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425560 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 3, 1, 4]
def baseStart_425560 : Nat := 118140960795 + 425560 * 2 ^ 59
def prefixEnd_425560 : Nat := 4983230072969 + 3 ^ 40 * 425560 * 2
def baseEnd_425560 : Nat := 218516827327460228242891

theorem tailTrace_425560 : CollatzResearch.WordTrace tailWord_425560 prefixEnd_425560 218516827327460228242891 := by
  unfold tailWord_425560
  simp only [CollatzResearch.WordTrace]
  refine ⟨7760724169138137353385067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10347632225517516471180089 7760724169138137353385067)
  ·
    refine ⟨11641086253707206030077601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7760724169138137353385067 11641086253707206030077601)
    ·
      refine ⟨8730814690280404522558201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11641086253707206030077601 8730814690280404522558201)
      ·
        refine ⟨6548111017710303391918651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8730814690280404522558201 6548111017710303391918651)
        ·
          refine ⟨9822166526565455087877977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6548111017710303391918651 9822166526565455087877977)
          ·
            refine ⟨7366624894924091315908483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9822166526565455087877977 7366624894924091315908483)
            ·
              refine ⟨11049937342386136973862725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7366624894924091315908483 11049937342386136973862725)
              ·
                refine ⟨2071863251697400682599261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11049937342386136973862725 2071863251697400682599261)
                ·
                  refine ⟨776948719386525255974723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2071863251697400682599261 776948719386525255974723)
                  ·
                    refine ⟨1165423079079787883962085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 776948719386525255974723 1165423079079787883962085)
                    ·
                      refine ⟨218516827327460228242891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1165423079079787883962085 218516827327460228242891)
                      ·
                        rfl

theorem cell23_425560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_425560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425560 prefixEnd_425560 := by exact prefixLift 425560
  have htrace : WordTrace (prefixWord ++ tailWord_425560) baseStart_425560 baseEnd_425560 := by
    simpa [prefixWord, tailWord_425560, baseEnd_425560] using wordTrace_append hprefix tailTrace_425560
  have hstable : (prefixWord ++ tailWord_425560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425560).length < 2 ^ (prefixWord ++ tailWord_425560).sum := by decide
  have hdescent : baseEnd_425560 < baseStart_425560 := by decide
  rcases family_descends (prefixWord ++ tailWord_425560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425577 : List Nat := [1, 2, 1, 1, 1, 4, 5, 2, 1, 1, 4]
def baseStart_425577 : Nat := 118140960795 + 425577 * 2 ^ 59
def prefixEnd_425577 : Nat := 4983230072969 + 3 ^ 40 * 425577 * 2
def baseEnd_425577 : Nat := 218525556498586661730313

theorem tailTrace_425577 : CollatzResearch.WordTrace tailWord_425577 prefixEnd_425577 218525556498586661730313 := by
  unfold tailWord_425577
  simp only [CollatzResearch.WordTrace]
  refine ⟨15522068379214686610138985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10348045586143124406759323 15522068379214686610138985)
  ·
    refine ⟨11641551284411014957604239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15522068379214686610138985 11641551284411014957604239)
    ·
      refine ⟨17462326926616522436406359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11641551284411014957604239 17462326926616522436406359)
      ·
        refine ⟨26193490389924783654609539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17462326926616522436406359 26193490389924783654609539)
        ·
          refine ⟨39290235584887175481914309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26193490389924783654609539 39290235584887175481914309)
          ·
            refine ⟨7366919172166345402858933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39290235584887175481914309 7366919172166345402858933)
            ·
              refine ⟨690648672390594881518025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7366919172166345402858933 690648672390594881518025)
              ·
                refine ⟨517986504292946161138519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 690648672390594881518025 517986504292946161138519)
                ·
                  refine ⟨776979756439419241707779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 517986504292946161138519 776979756439419241707779)
                  ·
                    refine ⟨1165469634659128862561669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 776979756439419241707779 1165469634659128862561669)
                    ·
                      refine ⟨218525556498586661730313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1165469634659128862561669 218525556498586661730313)
                      ·
                        rfl

theorem cell23_425577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 1, 4].length) (baseStart_425577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425577 prefixEnd_425577 := by exact prefixLift 425577
  have htrace : WordTrace (prefixWord ++ tailWord_425577) baseStart_425577 baseEnd_425577 := by
    simpa [prefixWord, tailWord_425577, baseEnd_425577] using wordTrace_append hprefix tailTrace_425577
  have hstable : (prefixWord ++ tailWord_425577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425577).length < 2 ^ (prefixWord ++ tailWord_425577).sum := by decide
  have hdescent : baseEnd_425577 < baseStart_425577 := by decide
  rcases family_descends (prefixWord ++ tailWord_425577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425581 : List Nat := [1, 5, 1, 1, 4, 1, 2, 1, 2, 3, 2]
def baseStart_425581 : Nat := 118140960795 + 425581 * 2 ^ 59
def prefixEnd_425581 : Nat := 4983230072969 + 3 ^ 40 * 425581 * 2
def baseEnd_425581 : Nat := 218527610421204646080295

theorem tailTrace_425581 : CollatzResearch.WordTrace tailWord_425581 prefixEnd_425581 218527610421204646080295 := by
  unfold tailWord_425581
  simp only [CollatzResearch.WordTrace]
  refine ⟨15522214271200195293284597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10348142847466796862189731 15522214271200195293284597)
  ·
    refine ⟨1455207587925018308745431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15522214271200195293284597 1455207587925018308745431)
    ·
      refine ⟨2182811381887527463118147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1455207587925018308745431 2182811381887527463118147)
      ·
        refine ⟨3274217072831291194677221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2182811381887527463118147 3274217072831291194677221)
        ·
          refine ⟨613915701155867099001979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3274217072831291194677221 613915701155867099001979)
          ·
            refine ⟨920873551733800648502969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613915701155867099001979 920873551733800648502969)
            ·
              refine ⟨690655163800350486377227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 920873551733800648502969 690655163800350486377227)
              ·
                refine ⟨1035982745700525729565841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 690655163800350486377227 1035982745700525729565841)
                ·
                  refine ⟨776987059275394297174381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1035982745700525729565841 776987059275394297174381)
                  ·
                    refine ⟨291370147228272861440393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 776987059275394297174381 291370147228272861440393)
                    ·
                      refine ⟨218527610421204646080295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 291370147228272861440393 218527610421204646080295)
                      ·
                        rfl

theorem cell23_425581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_425581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425581 prefixEnd_425581 := by exact prefixLift 425581
  have htrace : WordTrace (prefixWord ++ tailWord_425581) baseStart_425581 baseEnd_425581 := by
    simpa [prefixWord, tailWord_425581, baseEnd_425581] using wordTrace_append hprefix tailTrace_425581
  have hstable : (prefixWord ++ tailWord_425581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425581).length < 2 ^ (prefixWord ++ tailWord_425581).sum := by decide
  have hdescent : baseEnd_425581 < baseStart_425581 := by decide
  rcases family_descends (prefixWord ++ tailWord_425581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425597 : List Nat := [1, 4, 1, 1, 4, 1, 3, 1, 1, 1, 5]
def baseStart_425597 : Nat := 118140960795 + 425597 * 2 ^ 59
def prefixEnd_425597 : Nat := 4983230072969 + 3 ^ 40 * 425597 * 2
def baseEnd_425597 : Nat := 218535826111676583480221

theorem tailTrace_425597 : CollatzResearch.WordTrace tailWord_425597 prefixEnd_425597 218535826111676583480221 := by
  unfold tailWord_425597
  simp only [CollatzResearch.WordTrace]
  refine ⟨15522797839142230025867045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10348531892761486683911363 15522797839142230025867045)
  ·
    refine ⟨2910524594839168129850071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15522797839142230025867045 2910524594839168129850071)
    ·
      refine ⟨4365786892258752194775107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2910524594839168129850071 4365786892258752194775107)
      ·
        refine ⟨6548680338388128292162661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4365786892258752194775107 6548680338388128292162661)
        ·
          refine ⟨1227877563447774054780499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6548680338388128292162661 1227877563447774054780499)
          ·
            refine ⟨1841816345171661082170749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1227877563447774054780499 1841816345171661082170749)
            ·
              refine ⟨690681129439372905814031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1841816345171661082170749 690681129439372905814031)
              ·
                refine ⟨1036021694159059358721047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 690681129439372905814031 1036021694159059358721047)
                ·
                  refine ⟨1554032541238589038081571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1036021694159059358721047 1554032541238589038081571)
                  ·
                    refine ⟨2331048811857883557122357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1554032541238589038081571 2331048811857883557122357)
                    ·
                      refine ⟨218535826111676583480221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2331048811857883557122357 218535826111676583480221)
                      ·
                        rfl

theorem cell23_425597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_425597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425597 prefixEnd_425597 := by exact prefixLift 425597
  have htrace : WordTrace (prefixWord ++ tailWord_425597) baseStart_425597 baseEnd_425597 := by
    simpa [prefixWord, tailWord_425597, baseEnd_425597] using wordTrace_append hprefix tailTrace_425597
  have hstable : (prefixWord ++ tailWord_425597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425597).length < 2 ^ (prefixWord ++ tailWord_425597).sum := by decide
  have hdescent : baseEnd_425597 < baseStart_425597 := by decide
  rcases family_descends (prefixWord ++ tailWord_425597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425611 : List Nat := [1, 1, 1, 1, 4, 1, 5, 4, 1, 2, 2]
def baseStart_425611 : Nat := 118140960795 + 425611 * 2 ^ 59
def prefixEnd_425611 : Nat := 4983230072969 + 3 ^ 40 * 425611 * 2
def baseEnd_425611 : Nat := 218543014840839528705157

theorem tailTrace_425611 : CollatzResearch.WordTrace tailWord_425611 prefixEnd_425611 218543014840839528705157 := by
  unfold tailWord_425611
  simp only [CollatzResearch.WordTrace]
  refine ⟨15523308461091510416876687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10348872307394340277917791 15523308461091510416876687)
  ·
    refine ⟨23284962691637265625315031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15523308461091510416876687 23284962691637265625315031)
    ·
      refine ⟨34927444037455898437972547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23284962691637265625315031 34927444037455898437972547)
      ·
        refine ⟨52391166056183847656958821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34927444037455898437972547 52391166056183847656958821)
        ·
          refine ⟨9823343635534471435679779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52391166056183847656958821 9823343635534471435679779)
          ·
            refine ⟨14735015453301707153519669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9823343635534471435679779 14735015453301707153519669)
            ·
              refine ⟨1381407698747035045642469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14735015453301707153519669 1381407698747035045642469)
              ·
                refine ⟨259013943515069071057963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1381407698747035045642469 259013943515069071057963)
                ·
                  refine ⟨388520915272603606586945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259013943515069071057963 388520915272603606586945)
                  ·
                    refine ⟨291390686454452704940209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 388520915272603606586945 291390686454452704940209)
                    ·
                      refine ⟨218543014840839528705157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 291390686454452704940209 218543014840839528705157)
                      ·
                        rfl

theorem cell23_425611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 1, 2, 2].length) (baseStart_425611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425611 prefixEnd_425611 := by exact prefixLift 425611
  have htrace : WordTrace (prefixWord ++ tailWord_425611) baseStart_425611 baseEnd_425611 := by
    simpa [prefixWord, tailWord_425611, baseEnd_425611] using wordTrace_append hprefix tailTrace_425611
  have hstable : (prefixWord ++ tailWord_425611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425611).length < 2 ^ (prefixWord ++ tailWord_425611).sum := by decide
  have hdescent : baseEnd_425611 < baseStart_425611 := by decide
  rcases family_descends (prefixWord ++ tailWord_425611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425680 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 4]
def baseStart_425680 : Nat := 118140960795 + 425680 * 2 ^ 59
def prefixEnd_425680 : Nat := 4983230072969 + 3 ^ 40 * 425680 * 2
def baseEnd_425680 : Nat := 218578445005999758742339

theorem tailTrace_425680 : CollatzResearch.WordTrace tailWord_425680 prefixEnd_425680 218578445005999758742339 := by
  unfold tailWord_425680
  simp only [CollatzResearch.WordTrace]
  refine ⟨7762912548920767600569247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10350550065227690134092329 7762912548920767600569247)
  ·
    refine ⟨11644368823381151400853871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7762912548920767600569247 11644368823381151400853871)
    ·
      refine ⟨17466553235071727101280807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11644368823381151400853871 17466553235071727101280807)
      ·
        refine ⟨26199829852607590651921211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17466553235071727101280807 26199829852607590651921211)
        ·
          refine ⟨39299744778911385977881817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26199829852607590651921211 39299744778911385977881817)
          ·
            refine ⟨29474808584183539483411363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39299744778911385977881817 29474808584183539483411363)
            ·
              refine ⟨44212212876275309225117045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29474808584183539483411363 44212212876275309225117045)
              ·
                refine ⟨4144894957150810239854723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44212212876275309225117045 4144894957150810239854723)
                ·
                  refine ⟨6217342435726215359782085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4144894957150810239854723 6217342435726215359782085)
                  ·
                    refine ⟨1165751706698665379959141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6217342435726215359782085 1165751706698665379959141)
                    ·
                      refine ⟨218578445005999758742339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1165751706698665379959141 218578445005999758742339)
                      ·
                        rfl

theorem cell23_425680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 4].length) (baseStart_425680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425680 prefixEnd_425680 := by exact prefixLift 425680
  have htrace : WordTrace (prefixWord ++ tailWord_425680) baseStart_425680 baseEnd_425680 := by
    simpa [prefixWord, tailWord_425680, baseEnd_425680] using wordTrace_append hprefix tailTrace_425680
  have hstable : (prefixWord ++ tailWord_425680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425680).length < 2 ^ (prefixWord ++ tailWord_425680).sum := by decide
  have hdescent : baseEnd_425680 < baseStart_425680 := by decide
  rcases family_descends (prefixWord ++ tailWord_425680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425720 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 3, 7]
def baseStart_425720 : Nat := 118140960795 + 425720 * 2 ^ 59
def prefixEnd_425720 : Nat := 4983230072969 + 3 ^ 40 * 425720 * 2
def baseEnd_425720 : Nat := 72866328077393200747385

theorem tailTrace_425720 : CollatzResearch.WordTrace tailWord_425720 prefixEnd_425720 72866328077393200747385 := by
  unfold tailWord_425720
  simp only [CollatzResearch.WordTrace]
  refine ⟨7763642008848311016297307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10351522678464414688396409 7763642008848311016297307)
  ·
    refine ⟨11645463013272466524445961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7763642008848311016297307 11645463013272466524445961)
    ·
      refine ⟨8734097259954349893334471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11645463013272466524445961 8734097259954349893334471)
      ·
        refine ⟨13101145889931524840001707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8734097259954349893334471 13101145889931524840001707)
        ·
          refine ⟨19651718834897287260002561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13101145889931524840001707 19651718834897287260002561)
          ·
            refine ⟨14738789126172965445001921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19651718834897287260002561 14738789126172965445001921)
            ·
              refine ⟨11054091844629724083751441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14738789126172965445001921 11054091844629724083751441)
              ·
                refine ⟨8290568883472293062813581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11054091844629724083751441 8290568883472293062813581)
                ·
                  refine ⟨3108963331302109898555093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8290568883472293062813581 3108963331302109898555093)
                  ·
                    refine ⟨72866328077393200747385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3108963331302109898555093 72866328077393200747385)
                    ·
                      rfl

theorem cell23_425720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_425720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425720 prefixEnd_425720 := by exact prefixLift 425720
  have htrace : WordTrace (prefixWord ++ tailWord_425720) baseStart_425720 baseEnd_425720 := by
    simpa [prefixWord, tailWord_425720, baseEnd_425720] using wordTrace_append hprefix tailTrace_425720
  have hstable : (prefixWord ++ tailWord_425720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425720).length < 2 ^ (prefixWord ++ tailWord_425720).sum := by decide
  have hdescent : baseEnd_425720 < baseStart_425720 := by decide
  rcases family_descends (prefixWord ++ tailWord_425720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425754 : List Nat := [3, 1, 1, 3, 2, 3, 2, 1, 2, 5]
def baseStart_425754 : Nat := 118140960795 + 425754 * 2 ^ 59
def prefixEnd_425754 : Nat := 4983230072969 + 3 ^ 40 * 425754 * 2
def baseEnd_425754 : Nat := 72872147524810823072333

theorem tailTrace_425754 : CollatzResearch.WordTrace tailWord_425754 prefixEnd_425754 72872147524810823072333 := by
  unfold tailWord_425754
  simp only [CollatzResearch.WordTrace]
  refine ⟨3882131024893361459833079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10352349399715630559554877 3882131024893361459833079)
  ·
    refine ⟨5823196537340042189749619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3882131024893361459833079 5823196537340042189749619)
    ·
      refine ⟨8734794806010063284624429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5823196537340042189749619 8734794806010063284624429)
      ·
        refine ⟨3275548052253773731734161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8734794806010063284624429 3275548052253773731734161)
        ·
          refine ⟨2456661039190330298800621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3275548052253773731734161 2456661039190330298800621)
          ·
            refine ⟨921247889696373862050233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2456661039190330298800621 921247889696373862050233)
            ·
              refine ⟨690935917272280396537675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 921247889696373862050233 690935917272280396537675)
              ·
                refine ⟨1036403875908420594806513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 690935917272280396537675 1036403875908420594806513)
                ·
                  refine ⟨777302906931315446104885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1036403875908420594806513 777302906931315446104885)
                  ·
                    refine ⟨72872147524810823072333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 777302906931315446104885 72872147524810823072333)
                    ·
                      rfl

theorem cell23_425754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 2, 5].length) (baseStart_425754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425754 prefixEnd_425754 := by exact prefixLift 425754
  have htrace : WordTrace (prefixWord ++ tailWord_425754) baseStart_425754 baseEnd_425754 := by
    simpa [prefixWord, tailWord_425754, baseEnd_425754] using wordTrace_append hprefix tailTrace_425754
  have hstable : (prefixWord ++ tailWord_425754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425754).length < 2 ^ (prefixWord ++ tailWord_425754).sum := by decide
  have hdescent : baseEnd_425754 < baseStart_425754 := by decide
  rcases family_descends (prefixWord ++ tailWord_425754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425791 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 2, 4, 2]
def baseStart_425791 : Nat := 118140960795 + 425791 * 2 ^ 59
def prefixEnd_425791 : Nat := 4983230072969 + 3 ^ 40 * 425791 * 2
def baseEnd_425791 : Nat := 218635441358648824454329

theorem tailTrace_425791 : CollatzResearch.WordTrace tailWord_425791 prefixEnd_425791 218635441358648824454329 := by
  unfold tailWord_425791
  simp only [CollatzResearch.WordTrace]
  refine ⟨15529873600439401158429227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10353249066959600772286151 15529873600439401158429227)
  ·
    refine ⟨23294810400659101737643841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15529873600439401158429227 23294810400659101737643841)
    ·
      refine ⟨17471107800494326303232881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23294810400659101737643841 17471107800494326303232881)
      ·
        refine ⟨13103330850370744727424661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17471107800494326303232881 13103330850370744727424661)
        ·
          refine ⟨614218633611128659098031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13103330850370744727424661 614218633611128659098031)
          ·
            refine ⟨921327950416692988647047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614218633611128659098031 921327950416692988647047)
            ·
              refine ⟨1381991925625039482970571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 921327950416692988647047 1381991925625039482970571)
              ·
                refine ⟨2072987888437559224455857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1381991925625039482970571 2072987888437559224455857)
                ·
                  refine ⟨1554740916328169418341893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2072987888437559224455857 1554740916328169418341893)
                  ·
                    refine ⟨291513921811531765939105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1554740916328169418341893 291513921811531765939105)
                    ·
                      refine ⟨218635441358648824454329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 291513921811531765939105 218635441358648824454329)
                      ·
                        rfl

theorem cell23_425791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 4, 2].length) (baseStart_425791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425791 prefixEnd_425791 := by exact prefixLift 425791
  have htrace : WordTrace (prefixWord ++ tailWord_425791) baseStart_425791 baseEnd_425791 := by
    simpa [prefixWord, tailWord_425791, baseEnd_425791] using wordTrace_append hprefix tailTrace_425791
  have hstable : (prefixWord ++ tailWord_425791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425791).length < 2 ^ (prefixWord ++ tailWord_425791).sum := by decide
  have hdescent : baseEnd_425791 < baseStart_425791 := by decide
  rcases family_descends (prefixWord ++ tailWord_425791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425797 : List Nat := [1, 3, 1, 1, 1, 2, 3, 5, 6]
def baseStart_425797 : Nat := 118140960795 + 425797 * 2 ^ 59
def prefixEnd_425797 : Nat := 4983230072969 + 3 ^ 40 * 425797 * 2
def baseEnd_425797 : Nat := 24293169138063977886589

theorem tailTrace_425797 : CollatzResearch.WordTrace tailWord_425797 prefixEnd_425797 24293169138063977886589 := by
  unfold tailWord_425797
  simp only [CollatzResearch.WordTrace]
  refine ⟨15530092438417664183147645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10353394958945109455431763 15530092438417664183147645)
  ·
    refine ⟨5823784664406624068680367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15530092438417664183147645 5823784664406624068680367)
    ·
      refine ⟨8735676996609936103020551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5823784664406624068680367 8735676996609936103020551)
      ·
        refine ⟨13103515494914904154530827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8735676996609936103020551 13103515494914904154530827)
        ·
          refine ⟨19655273242372356231796241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13103515494914904154530827 19655273242372356231796241)
          ·
            refine ⟨14741454931779267173847181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19655273242372356231796241 14741454931779267173847181)
            ·
              refine ⟨5528045599417225190192693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14741454931779267173847181 5528045599417225190192693)
              ·
                refine ⟨518254274945364861580565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5528045599417225190192693 518254274945364861580565)
                ·
                  refine ⟨24293169138063977886589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 518254274945364861580565 24293169138063977886589)
                  ·
                    rfl

theorem cell23_425797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 6].length) (baseStart_425797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425797 prefixEnd_425797 := by exact prefixLift 425797
  have htrace : WordTrace (prefixWord ++ tailWord_425797) baseStart_425797 baseEnd_425797 := by
    simpa [prefixWord, tailWord_425797, baseEnd_425797] using wordTrace_append hprefix tailTrace_425797
  have hstable : (prefixWord ++ tailWord_425797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425797).length < 2 ^ (prefixWord ++ tailWord_425797).sum := by decide
  have hdescent : baseEnd_425797 < baseStart_425797 := by decide
  rcases family_descends (prefixWord ++ tailWord_425797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425841 : List Nat := [1, 2, 2, 2, 1, 3, 4, 1, 3, 1, 3]
def baseStart_425841 : Nat := 118140960795 + 425841 * 2 ^ 59
def prefixEnd_425841 : Nat := 4983230072969 + 3 ^ 40 * 425841 * 2
def baseEnd_425841 : Nat := 218661115391373628829099

theorem tailTrace_425841 : CollatzResearch.WordTrace tailWord_425841 prefixEnd_425841 218661115391373628829099 := by
  unfold tailWord_425841
  simp only [CollatzResearch.WordTrace]
  refine ⟨15531697250258259697749377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10354464833505506465166251 15531697250258259697749377)
  ·
    refine ⟨11648772937693694773312033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15531697250258259697749377 11648772937693694773312033)
    ·
      refine ⟨8736579703270271079984025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11648772937693694773312033 8736579703270271079984025)
      ·
        refine ⟨6552434777452703309988019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8736579703270271079984025 6552434777452703309988019)
        ·
          refine ⟨9828652166179054964982029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6552434777452703309988019 9828652166179054964982029)
          ·
            refine ⟨3685744562317145611868261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9828652166179054964982029 3685744562317145611868261)
            ·
              refine ⟨691077105434464802225299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3685744562317145611868261 691077105434464802225299)
              ·
                refine ⟨1036615658151697203337949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691077105434464802225299 1036615658151697203337949)
                ·
                  refine ⟨388730871806886451251731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1036615658151697203337949 388730871806886451251731)
                  ·
                    refine ⟨583096307710329676877597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 388730871806886451251731 583096307710329676877597)
                    ·
                      refine ⟨218661115391373628829099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 583096307710329676877597 218661115391373628829099)
                      ·
                        rfl

theorem cell23_425841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_425841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425841 prefixEnd_425841 := by exact prefixLift 425841
  have htrace : WordTrace (prefixWord ++ tailWord_425841) baseStart_425841 baseEnd_425841 := by
    simpa [prefixWord, tailWord_425841, baseEnd_425841] using wordTrace_append hprefix tailTrace_425841
  have hstable : (prefixWord ++ tailWord_425841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425841).length < 2 ^ (prefixWord ++ tailWord_425841).sum := by decide
  have hdescent : baseEnd_425841 < baseStart_425841 := by decide
  rcases family_descends (prefixWord ++ tailWord_425841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425867 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 5]
def baseStart_425867 : Nat := 118140960795 + 425867 * 2 ^ 59
def prefixEnd_425867 : Nat := 4983230072969 + 3 ^ 40 * 425867 * 2
def baseEnd_425867 : Nat := 218674465888390527103979

theorem tailTrace_425867 : CollatzResearch.WordTrace tailWord_425867 prefixEnd_425867 218674465888390527103979 := by
  unfold tailWord_425867
  simp only [CollatzResearch.WordTrace]
  refine ⟨15532645548164066138195855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10355097032109377425463903 15532645548164066138195855)
  ·
    refine ⟨23298968322246099207293783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15532645548164066138195855 23298968322246099207293783)
    ·
      refine ⟨34948452483369148810940675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23298968322246099207293783 34948452483369148810940675)
      ·
        refine ⟨52422678725053723216411013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34948452483369148810940675 52422678725053723216411013)
        ·
          refine ⟨9829252260947573103077065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52422678725053723216411013 9829252260947573103077065)
          ·
            refine ⟨7371939195710679827307799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9829252260947573103077065 7371939195710679827307799)
            ·
              refine ⟨11057908793566019740961699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7371939195710679827307799 11057908793566019740961699)
              ·
                refine ⟨16586863190349029611442549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11057908793566019740961699 16586863190349029611442549)
                ·
                  refine ⟨1555018424095221526072739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16586863190349029611442549 1555018424095221526072739)
                  ·
                    refine ⟨2332527636142832289109109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1555018424095221526072739 2332527636142832289109109)
                    ·
                      refine ⟨218674465888390527103979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2332527636142832289109109 218674465888390527103979)
                      ·
                        rfl

theorem cell23_425867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 5].length) (baseStart_425867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425867 prefixEnd_425867 := by exact prefixLift 425867
  have htrace : WordTrace (prefixWord ++ tailWord_425867) baseStart_425867 baseEnd_425867 := by
    simpa [prefixWord, tailWord_425867, baseEnd_425867] using wordTrace_append hprefix tailTrace_425867
  have hstable : (prefixWord ++ tailWord_425867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425867).length < 2 ^ (prefixWord ++ tailWord_425867).sum := by decide
  have hdescent : baseEnd_425867 < baseStart_425867 := by decide
  rcases family_descends (prefixWord ++ tailWord_425867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425881 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 5, 2, 2]
def baseStart_425881 : Nat := 118140960795 + 425881 * 2 ^ 59
def prefixEnd_425881 : Nat := 4983230072969 + 3 ^ 40 * 425881 * 2
def baseEnd_425881 : Nat := 218681654617553472328915

theorem tailTrace_425881 : CollatzResearch.WordTrace tailWord_425881 prefixEnd_425881 218681654617553472328915 := by
  unfold tailWord_425881
  simp only [CollatzResearch.WordTrace]
  refine ⟨15533156170113346529205497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10355437446742231019470331 15533156170113346529205497)
  ·
    refine ⟨11649867127585009896904123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15533156170113346529205497 11649867127585009896904123)
    ·
      refine ⟨17474800691377514845356185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11649867127585009896904123 17474800691377514845356185)
      ·
        refine ⟨13106100518533136134017139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17474800691377514845356185 13106100518533136134017139)
        ·
          refine ⟨19659150777799704201025709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13106100518533136134017139 19659150777799704201025709)
          ·
            refine ⟨7372181541674889075384641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19659150777799704201025709 7372181541674889075384641)
            ·
              refine ⟨5529136156256166806538481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7372181541674889075384641 5529136156256166806538481)
              ·
                refine ⟨4146852117192125104903861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5529136156256166806538481 4146852117192125104903861)
                ·
                  refine ⟨388767385986761728584737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4146852117192125104903861 388767385986761728584737)
                  ·
                    refine ⟨291575539490071296438553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 388767385986761728584737 291575539490071296438553)
                    ·
                      refine ⟨218681654617553472328915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 291575539490071296438553 218681654617553472328915)
                      ·
                        rfl

theorem cell23_425881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 2, 2].length) (baseStart_425881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425881 prefixEnd_425881 := by exact prefixLift 425881
  have htrace : WordTrace (prefixWord ++ tailWord_425881) baseStart_425881 baseEnd_425881 := by
    simpa [prefixWord, tailWord_425881, baseEnd_425881] using wordTrace_append hprefix tailTrace_425881
  have hstable : (prefixWord ++ tailWord_425881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425881).length < 2 ^ (prefixWord ++ tailWord_425881).sum := by decide
  have hdescent : baseEnd_425881 < baseStart_425881 := by decide
  rcases family_descends (prefixWord ++ tailWord_425881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425907 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 6]
def baseStart_425907 : Nat := 118140960795 + 425907 * 2 ^ 59
def prefixEnd_425907 : Nat := 4983230072969 + 3 ^ 40 * 425907 * 2
def baseEnd_425907 : Nat := 218695005114570370603795

theorem tailTrace_425907 : CollatzResearch.WordTrace tailWord_425907 prefixEnd_425907 218695005114570370603795 := by
  unfold tailWord_425907
  simp only [CollatzResearch.WordTrace]
  refine ⟨15534104468019152969651975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10356069645346101979767983 15534104468019152969651975)
  ·
    refine ⟨23301156702028729454477963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15534104468019152969651975 23301156702028729454477963)
    ·
      refine ⟨34951735053043094181716945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23301156702028729454477963 34951735053043094181716945)
      ·
        refine ⟨26213801289782320636287709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34951735053043094181716945 26213801289782320636287709)
        ·
          refine ⟨9830175483668370238607891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26213801289782320636287709 9830175483668370238607891)
          ·
            refine ⟨14745263225502555357911837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9830175483668370238607891 14745263225502555357911837)
            ·
              refine ⟨5529473709563458259216939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14745263225502555357911837 5529473709563458259216939)
              ·
                refine ⟨8294210564345187388825409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5529473709563458259216939 8294210564345187388825409)
                ·
                  refine ⟨6220657923258890541619057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8294210564345187388825409 6220657923258890541619057)
                  ·
                    refine ⟨4665493442444167906214293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6220657923258890541619057 4665493442444167906214293)
                    ·
                      refine ⟨218695005114570370603795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4665493442444167906214293 218695005114570370603795)
                      ·
                        rfl

theorem cell23_425907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_425907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425907 prefixEnd_425907 := by exact prefixLift 425907
  have htrace : WordTrace (prefixWord ++ tailWord_425907) baseStart_425907 baseEnd_425907 := by
    simpa [prefixWord, tailWord_425907, baseEnd_425907] using wordTrace_append hprefix tailTrace_425907
  have hstable : (prefixWord ++ tailWord_425907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425907).length < 2 ^ (prefixWord ++ tailWord_425907).sum := by decide
  have hdescent : baseEnd_425907 < baseStart_425907 := by decide
  rcases family_descends (prefixWord ++ tailWord_425907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425918 : List Nat := [4, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3]
def baseStart_425918 : Nat := 118140960795 + 425918 * 2 ^ 59
def prefixEnd_425918 : Nat := 4983230072969 + 3 ^ 40 * 425918 * 2
def baseEnd_425918 : Nat := 218700653401769827566245

theorem tailTrace_425918 : CollatzResearch.WordTrace tailWord_425918 prefixEnd_425918 218700653401769827566245 := by
  unfold tailWord_425918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1941813208872412731037801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10356337113986201232201605 1941813208872412731037801)
  ·
    refine ⟨1456359906654309548278351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1941813208872412731037801 1456359906654309548278351)
    ·
      refine ⟨2184539859981464322417527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1456359906654309548278351 2184539859981464322417527)
      ·
        refine ⟨3276809789972196483626291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2184539859981464322417527 3276809789972196483626291)
        ·
          refine ⟨4915214684958294725439437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3276809789972196483626291 4915214684958294725439437)
          ·
            refine ⟨1843205506859360522039789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4915214684958294725439437 1843205506859360522039789)
            ·
              refine ⟨691202065072260195764921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1843205506859360522039789 691202065072260195764921)
              ·
                refine ⟨518401548804195146823691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 691202065072260195764921 518401548804195146823691)
                ·
                  refine ⟨777602323206292720235537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 518401548804195146823691 777602323206292720235537)
                  ·
                    refine ⟨583201742404719540176653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 777602323206292720235537 583201742404719540176653)
                    ·
                      refine ⟨218700653401769827566245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 583201742404719540176653 218700653401769827566245)
                      ·
                        rfl

theorem cell23_425918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_425918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425918 prefixEnd_425918 := by exact prefixLift 425918
  have htrace : WordTrace (prefixWord ++ tailWord_425918) baseStart_425918 baseEnd_425918 := by
    simpa [prefixWord, tailWord_425918, baseEnd_425918] using wordTrace_append hprefix tailTrace_425918
  have hstable : (prefixWord ++ tailWord_425918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425918).length < 2 ^ (prefixWord ++ tailWord_425918).sum := by decide
  have hdescent : baseEnd_425918 < baseStart_425918 := by decide
  rcases family_descends (prefixWord ++ tailWord_425918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425965 : List Nat := [1, 5, 1, 4, 1, 1, 2, 1, 1, 3, 3]
def baseStart_425965 : Nat := 118140960795 + 425965 * 2 ^ 59
def prefixEnd_425965 : Nat := 4983230072969 + 3 ^ 40 * 425965 * 2
def baseEnd_425965 : Nat := 218724786992531143678529

theorem tailTrace_425965 : CollatzResearch.WordTrace tailWord_425965 prefixEnd_425965 218724786992531143678529 := by
  unfold tailWord_425965
  simp only [CollatzResearch.WordTrace]
  refine ⟨15536219901809028875263349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10357479934539352583508899 15536219901809028875263349)
  ·
    refine ⟨1456520615794596457055939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15536219901809028875263349 1456520615794596457055939)
    ·
      refine ⟨2184780923691894685583909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1456520615794596457055939 2184780923691894685583909)
      ·
        refine ⟨409646423192230253546983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2184780923691894685583909 409646423192230253546983)
        ·
          refine ⟨614469634788345380320475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409646423192230253546983 614469634788345380320475)
          ·
            refine ⟨921704452182518070480713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614469634788345380320475 921704452182518070480713)
            ·
              refine ⟨691278339136888552860535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 921704452182518070480713 691278339136888552860535)
              ·
                refine ⟨1036917508705332829290803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691278339136888552860535 1036917508705332829290803)
                ·
                  refine ⟨1555376263057999243936205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1036917508705332829290803 1555376263057999243936205)
                  ·
                    refine ⟨583266098646749716476077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1555376263057999243936205 583266098646749716476077)
                    ·
                      refine ⟨218724786992531143678529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 583266098646749716476077 218724786992531143678529)
                      ·
                        rfl

theorem cell23_425965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_425965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_425965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_425965 prefixEnd_425965 := by exact prefixLift 425965
  have htrace : WordTrace (prefixWord ++ tailWord_425965) baseStart_425965 baseEnd_425965 := by
    simpa [prefixWord, tailWord_425965, baseEnd_425965] using wordTrace_append hprefix tailTrace_425965
  have hstable : (prefixWord ++ tailWord_425965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425965).length < 2 ^ (prefixWord ++ tailWord_425965).sum := by decide
  have hdescent : baseEnd_425965 < baseStart_425965 := by decide
  rcases family_descends (prefixWord ++ tailWord_425965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426005 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 4, 2, 2]
def baseStart_426005 : Nat := 118140960795 + 426005 * 2 ^ 59
def prefixEnd_426005 : Nat := 4983230072969 + 3 ^ 40 * 426005 * 2
def baseEnd_426005 : Nat := 218745326218710987178345

theorem tailTrace_426005 : CollatzResearch.WordTrace tailWord_426005 prefixEnd_426005 218745326218710987178345 := by
  unfold tailWord_426005
  simp only [CollatzResearch.WordTrace]
  refine ⟨15537678821664115706719469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10358452547776077137812979 15537678821664115706719469)
  ·
    refine ⟨5826629558124043390019801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15537678821664115706719469 5826629558124043390019801)
    ·
      refine ⟨4369972168593032542514851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5826629558124043390019801 4369972168593032542514851)
      ·
        refine ⟨6554958252889548813772277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4369972168593032542514851 6554958252889548813772277)
        ·
          refine ⟨614527336208395201291151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6554958252889548813772277 614527336208395201291151)
          ·
            refine ⟨921791004312592801936727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614527336208395201291151 921791004312592801936727)
            ·
              refine ⟨1382686506468889202905091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 921791004312592801936727 1382686506468889202905091)
              ·
                refine ⟨2074029759703333804357637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1382686506468889202905091 2074029759703333804357637)
                ·
                  refine ⟨388880579944375088317057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2074029759703333804357637 388880579944375088317057)
                  ·
                    refine ⟨291660434958281316237793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 388880579944375088317057 291660434958281316237793)
                    ·
                      refine ⟨218745326218710987178345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 291660434958281316237793 218745326218710987178345)
                      ·
                        rfl

theorem cell23_426005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 2, 2].length) (baseStart_426005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426005 prefixEnd_426005 := by exact prefixLift 426005
  have htrace : WordTrace (prefixWord ++ tailWord_426005) baseStart_426005 baseEnd_426005 := by
    simpa [prefixWord, tailWord_426005, baseEnd_426005] using wordTrace_append hprefix tailTrace_426005
  have hstable : (prefixWord ++ tailWord_426005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426005).length < 2 ^ (prefixWord ++ tailWord_426005).sum := by decide
  have hdescent : baseEnd_426005 < baseStart_426005 := by decide
  rcases family_descends (prefixWord ++ tailWord_426005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426021 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 2, 3, 3]
def baseStart_426021 : Nat := 118140960795 + 426021 * 2 ^ 59
def prefixEnd_426021 : Nat := 4983230072969 + 3 ^ 40 * 426021 * 2
def baseEnd_426021 : Nat := 218753541909182924578271

theorem tailTrace_426021 : CollatzResearch.WordTrace tailWord_426021 prefixEnd_426021 218753541909182924578271 := by
  unfold tailWord_426021
  simp only [CollatzResearch.WordTrace]
  refine ⟨15538262389606150439301917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10358841593070766959534611 15538262389606150439301917)
  ·
    refine ⟨5826848396102306414738219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15538262389606150439301917 5826848396102306414738219)
    ·
      refine ⟨8740272594153459622107329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5826848396102306414738219 8740272594153459622107329)
      ·
        refine ⟨6555204445615094716580497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8740272594153459622107329 6555204445615094716580497)
        ·
          refine ⟨4916403334211321037435373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6555204445615094716580497 4916403334211321037435373)
          ·
            refine ⟨1843651250329245389038265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4916403334211321037435373 1843651250329245389038265)
            ·
              refine ⟨1382738437746934041778699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1843651250329245389038265 1382738437746934041778699)
              ·
                refine ⟨2074107656620401062668049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1382738437746934041778699 2074107656620401062668049)
                ·
                  refine ⟨1555580742465300797001037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2074107656620401062668049 1555580742465300797001037)
                  ·
                    refine ⟨583342778424487798875389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1555580742465300797001037 583342778424487798875389)
                    ·
                      refine ⟨218753541909182924578271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 583342778424487798875389 218753541909182924578271)
                      ·
                        rfl

theorem cell23_426021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_426021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426021 prefixEnd_426021 := by exact prefixLift 426021
  have htrace : WordTrace (prefixWord ++ tailWord_426021) baseStart_426021 baseEnd_426021 := by
    simpa [prefixWord, tailWord_426021, baseEnd_426021] using wordTrace_append hprefix tailTrace_426021
  have hstable : (prefixWord ++ tailWord_426021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426021).length < 2 ^ (prefixWord ++ tailWord_426021).sum := by decide
  have hdescent : baseEnd_426021 < baseStart_426021 := by decide
  rcases family_descends (prefixWord ++ tailWord_426021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426081 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 6, 2, 3]
def baseStart_426081 : Nat := 118140960795 + 426081 * 2 ^ 59
def prefixEnd_426081 : Nat := 4983230072969 + 3 ^ 40 * 426081 * 2
def baseEnd_426081 : Nat := 218784350748452689827995

theorem tailTrace_426081 : CollatzResearch.WordTrace tailWord_426081 prefixEnd_426081 218784350748452689827995 := by
  unfold tailWord_426081
  simp only [CollatzResearch.WordTrace]
  refine ⟨15540450769388780686486097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10360300512925853790990731 15540450769388780686486097)
  ·
    refine ⟨11655338077041585514864573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15540450769388780686486097 11655338077041585514864573)
    ·
      refine ⟨4370751778890594568074215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11655338077041585514864573 4370751778890594568074215)
      ·
        refine ⟨6556127668335891852111323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4370751778890594568074215 6556127668335891852111323)
        ·
          refine ⟨9834191502503837778166985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6556127668335891852111323 9834191502503837778166985)
          ·
            refine ⟨7375643626877878333625239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9834191502503837778166985 7375643626877878333625239)
            ·
              refine ⟨11063465440316817500437859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7375643626877878333625239 11063465440316817500437859)
              ·
                refine ⟨16595198160475226250656789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11063465440316817500437859 16595198160475226250656789)
                ·
                  refine ⟨777899913772276230499537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16595198160475226250656789 777899913772276230499537)
                  ·
                    refine ⟨583424935329207172874653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 777899913772276230499537 583424935329207172874653)
                    ·
                      refine ⟨218784350748452689827995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 583424935329207172874653 218784350748452689827995)
                      ·
                        rfl

theorem cell23_426081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_426081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426081 prefixEnd_426081 := by exact prefixLift 426081
  have htrace : WordTrace (prefixWord ++ tailWord_426081) baseStart_426081 baseEnd_426081 := by
    simpa [prefixWord, tailWord_426081, baseEnd_426081] using wordTrace_append hprefix tailTrace_426081
  have hstable : (prefixWord ++ tailWord_426081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426081).length < 2 ^ (prefixWord ++ tailWord_426081).sum := by decide
  have hdescent : baseEnd_426081 < baseStart_426081 := by decide
  rcases family_descends (prefixWord ++ tailWord_426081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426098 : List Nat := [3, 2, 1, 2, 2, 2, 1, 3, 2, 2, 3]
def baseStart_426098 : Nat := 118140960795 + 426098 * 2 ^ 59
def prefixEnd_426098 : Nat := 4983230072969 + 3 ^ 40 * 426098 * 2
def baseEnd_426098 : Nat := 218793079919579123315417

theorem tailTrace_426098 : CollatzResearch.WordTrace tailWord_426098 prefixEnd_426098 218793079919579123315417 := by
  unfold tailWord_426098
  simp only [CollatzResearch.WordTrace]
  refine ⟨3885267702581798147463737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10360713873551461726569965 3885267702581798147463737)
  ·
    refine ⟨2913950776936348610597803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3885267702581798147463737 2913950776936348610597803)
    ·
      refine ⟨4370926165404522915896705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2913950776936348610597803 4370926165404522915896705)
      ·
        refine ⟨3278194624053392186922529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4370926165404522915896705 3278194624053392186922529)
        ·
          refine ⟨2458645968040044140191897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3278194624053392186922529 2458645968040044140191897)
          ·
            refine ⟨1843984476030033105143923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2458645968040044140191897 1843984476030033105143923)
            ·
              refine ⟨2765976714045049657715885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1843984476030033105143923 2765976714045049657715885)
              ·
                refine ⟨1037241267766893621643457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2765976714045049657715885 1037241267766893621643457)
                ·
                  refine ⟨777930950825170216232593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1037241267766893621643457 777930950825170216232593)
                  ·
                    refine ⟨583448213118877662174445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 777930950825170216232593 583448213118877662174445)
                    ·
                      refine ⟨218793079919579123315417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 583448213118877662174445 218793079919579123315417)
                      ·
                        rfl

theorem cell23_426098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_426098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426098 prefixEnd_426098 := by exact prefixLift 426098
  have htrace : WordTrace (prefixWord ++ tailWord_426098) baseStart_426098 baseEnd_426098 := by
    simpa [prefixWord, tailWord_426098, baseEnd_426098] using wordTrace_append hprefix tailTrace_426098
  have hstable : (prefixWord ++ tailWord_426098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426098).length < 2 ^ (prefixWord ++ tailWord_426098).sum := by decide
  have hdescent : baseEnd_426098 < baseStart_426098 := by decide
  rcases family_descends (prefixWord ++ tailWord_426098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426104 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 1, 1, 8]
def baseStart_426104 : Nat := 118140960795 + 426104 * 2 ^ 59
def prefixEnd_426104 : Nat := 4983230072969 + 3 ^ 40 * 426104 * 2
def baseEnd_426104 : Nat := 218796160803506099840389

theorem tailTrace_426104 : CollatzResearch.WordTrace tailWord_426104 prefixEnd_426104 218796160803506099840389 := by
  unfold tailWord_426104
  simp only [CollatzResearch.WordTrace]
  refine ⟨7770644824152727807286683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10360859765536970409715577 7770644824152727807286683)
  ·
    refine ⟨11655967236229091710930025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7770644824152727807286683 11655967236229091710930025)
    ·
      refine ⟨8741975427171818783197519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11655967236229091710930025 8741975427171818783197519)
      ·
        refine ⟨13112963140757728174796279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8741975427171818783197519 13112963140757728174796279)
        ·
          refine ⟨19669444711136592262194419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13112963140757728174796279 19669444711136592262194419)
          ·
            refine ⟨29504167066704888393291629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19669444711136592262194419 29504167066704888393291629)
            ·
              refine ⟨11064062650014333147484361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29504167066704888393291629 11064062650014333147484361)
              ·
                refine ⟨8298046987510749860613271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11064062650014333147484361 8298046987510749860613271)
                ·
                  refine ⟨12447070481266124790919907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8298046987510749860613271 12447070481266124790919907)
                  ·
                    refine ⟨18670605721899187186379861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12447070481266124790919907 18670605721899187186379861)
                    ·
                      refine ⟨218796160803506099840389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 18670605721899187186379861 218796160803506099840389)
                      ·
                        rfl

theorem cell23_426104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_426104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426104 prefixEnd_426104 := by exact prefixLift 426104
  have htrace : WordTrace (prefixWord ++ tailWord_426104) baseStart_426104 baseEnd_426104 := by
    simpa [prefixWord, tailWord_426104, baseEnd_426104] using wordTrace_append hprefix tailTrace_426104
  have hstable : (prefixWord ++ tailWord_426104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426104).length < 2 ^ (prefixWord ++ tailWord_426104).sum := by decide
  have hdescent : baseEnd_426104 < baseStart_426104 := by decide
  rcases family_descends (prefixWord ++ tailWord_426104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426122 : List Nat := [3, 1, 2, 3, 1, 2, 4, 2, 1, 4]
def baseStart_426122 : Nat := 118140960795 + 426122 * 2 ^ 59
def prefixEnd_426122 : Nat := 4983230072969 + 3 ^ 40 * 426122 * 2
def baseEnd_426122 : Nat := 72935134485095676471769

theorem tailTrace_426122 : CollatzResearch.WordTrace tailWord_426122 prefixEnd_426122 72935134485095676471769 := by
  unfold tailWord_426122
  simp only [CollatzResearch.WordTrace]
  refine ⟨3885486540560061172182155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10361297441493496459152413 3885486540560061172182155)
  ·
    refine ⟨5828229810840091758273233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3885486540560061172182155 5828229810840091758273233)
    ·
      refine ⟨4371172358130068818704925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5828229810840091758273233 4371172358130068818704925)
      ·
        refine ⟨1639189634298775807014347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4371172358130068818704925 1639189634298775807014347)
        ·
          refine ⟨2458784451448163710521521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1639189634298775807014347 2458784451448163710521521)
          ·
            refine ⟨1844088338586122782891141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2458784451448163710521521 1844088338586122782891141)
            ·
              refine ⟨345766563484898021792089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1844088338586122782891141 345766563484898021792089)
              ·
                refine ⟨259324922613673516344067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345766563484898021792089 259324922613673516344067)
                ·
                  refine ⟨388987383920510274516101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259324922613673516344067 388987383920510274516101)
                  ·
                    refine ⟨72935134485095676471769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 388987383920510274516101 72935134485095676471769)
                    ·
                      rfl

theorem cell23_426122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_426122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426122 prefixEnd_426122 := by exact prefixLift 426122
  have htrace : WordTrace (prefixWord ++ tailWord_426122) baseStart_426122 baseEnd_426122 := by
    simpa [prefixWord, tailWord_426122, baseEnd_426122] using wordTrace_append hprefix tailTrace_426122
  have hstable : (prefixWord ++ tailWord_426122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426122).length < 2 ^ (prefixWord ++ tailWord_426122).sum := by decide
  have hdescent : baseEnd_426122 < baseStart_426122 := by decide
  rcases family_descends (prefixWord ++ tailWord_426122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426128 : List Nat := [2, 1, 1, 1, 1, 1, 6, 3, 3, 1, 3]
def baseStart_426128 : Nat := 118140960795 + 426128 * 2 ^ 59
def prefixEnd_426128 : Nat := 4983230072969 + 3 ^ 40 * 426128 * 2
def baseEnd_426128 : Nat := 218808484339214005940279

theorem tailTrace_426128 : CollatzResearch.WordTrace tailWord_426128 prefixEnd_426128 218808484339214005940279 := by
  unfold tailWord_426128
  simp only [CollatzResearch.WordTrace]
  refine ⟨7771082500109253856723519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10361443333479005142298025 7771082500109253856723519)
  ·
    refine ⟨11656623750163880785085279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7771082500109253856723519 11656623750163880785085279)
    ·
      refine ⟨17484935625245821177627919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11656623750163880785085279 17484935625245821177627919)
      ·
        refine ⟨26227403437868731766441879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17484935625245821177627919 26227403437868731766441879)
        ·
          refine ⟨39341105156803097649662819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26227403437868731766441879 39341105156803097649662819)
          ·
            refine ⟨59011657735204646474494229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39341105156803097649662819 59011657735204646474494229)
            ·
              refine ⟨2766171456337717803491917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59011657735204646474494229 2766171456337717803491917)
              ·
                refine ⟨1037314296126644176309469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2766171456337717803491917 1037314296126644176309469)
                ·
                  refine ⟨388992861047491566116051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1037314296126644176309469 388992861047491566116051)
                  ·
                    refine ⟨583489291571237349174077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 388992861047491566116051 583489291571237349174077)
                    ·
                      refine ⟨218808484339214005940279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 583489291571237349174077 218808484339214005940279)
                      ·
                        rfl

theorem cell23_426128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 3, 1, 3].length) (baseStart_426128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426128 prefixEnd_426128 := by exact prefixLift 426128
  have htrace : WordTrace (prefixWord ++ tailWord_426128) baseStart_426128 baseEnd_426128 := by
    simpa [prefixWord, tailWord_426128, baseEnd_426128] using wordTrace_append hprefix tailTrace_426128
  have hstable : (prefixWord ++ tailWord_426128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426128).length < 2 ^ (prefixWord ++ tailWord_426128).sum := by decide
  have hdescent : baseEnd_426128 < baseStart_426128 := by decide
  rcases family_descends (prefixWord ++ tailWord_426128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426145 : List Nat := [1, 2, 3, 3, 1, 3, 1, 2, 3, 1, 3]
def baseStart_426145 : Nat := 118140960795 + 426145 * 2 ^ 59
def prefixEnd_426145 : Nat := 4983230072969 + 3 ^ 40 * 426145 * 2
def baseEnd_426145 : Nat := 218817213510340439427701

theorem tailTrace_426145 : CollatzResearch.WordTrace tailWord_426145 prefixEnd_426145 218817213510340439427701 := by
  unfold tailWord_426145
  simp only [CollatzResearch.WordTrace]
  refine ⟨15542785041156919616815889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10361856694104613077877259 15542785041156919616815889)
  ·
    refine ⟨11657088780867689712611917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15542785041156919616815889 11657088780867689712611917)
    ·
      refine ⟨4371408292825383642229469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11657088780867689712611917 4371408292825383642229469)
      ·
        refine ⟨1639278109809518865836051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4371408292825383642229469 1639278109809518865836051)
        ·
          refine ⟨2458917164714278298754077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1639278109809518865836051 2458917164714278298754077)
          ·
            refine ⟨922093936767854362032779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2458917164714278298754077 922093936767854362032779)
            ·
              refine ⟨1383140905151781543049169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922093936767854362032779 1383140905151781543049169)
              ·
                refine ⟨1037355678863836157286877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1383140905151781543049169 1037355678863836157286877)
                ·
                  refine ⟨389008379573938558982579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1037355678863836157286877 389008379573938558982579)
                  ·
                    refine ⟨583512569360907838473869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 389008379573938558982579 583512569360907838473869)
                    ·
                      refine ⟨218817213510340439427701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 583512569360907838473869 218817213510340439427701)
                      ·
                        rfl

theorem cell23_426145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_426145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426145 prefixEnd_426145 := by exact prefixLift 426145
  have htrace : WordTrace (prefixWord ++ tailWord_426145) baseStart_426145 baseEnd_426145 := by
    simpa [prefixWord, tailWord_426145, baseEnd_426145] using wordTrace_append hprefix tailTrace_426145
  have hstable : (prefixWord ++ tailWord_426145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426145).length < 2 ^ (prefixWord ++ tailWord_426145).sum := by decide
  have hdescent : baseEnd_426145 < baseStart_426145 := by decide
  rcases family_descends (prefixWord ++ tailWord_426145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426162 : List Nat := [3, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3]
def baseStart_426162 : Nat := 118140960795 + 426162 * 2 ^ 59
def prefixEnd_426162 : Nat := 4983230072969 + 3 ^ 40 * 426162 * 2
def baseEnd_426162 : Nat := 218825942681466872915123

theorem tailTrace_426162 : CollatzResearch.WordTrace tailWord_426162 prefixEnd_426162 218825942681466872915123 := by
  unfold tailWord_426162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3885851270523832880046185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10362270054730221013456493 3885851270523832880046185)
  ·
    refine ⟨2914388452892874660034639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3885851270523832880046185 2914388452892874660034639)
    ·
      refine ⟨4371582679339311990051959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2914388452892874660034639 4371582679339311990051959)
      ·
        refine ⟨6557374019008967985077939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4371582679339311990051959 6557374019008967985077939)
        ·
          refine ⟨9836061028513451977616909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6557374019008967985077939 9836061028513451977616909)
          ·
            refine ⟨3688522885692544491606341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9836061028513451977616909 3688522885692544491606341)
            ·
              refine ⟨691598041067352092176189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3688522885692544491606341 691598041067352092176189)
              ·
                refine ⟨259349265400257034566071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 691598041067352092176189 259349265400257034566071)
                ·
                  refine ⟨389023898100385551849107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259349265400257034566071 389023898100385551849107)
                  ·
                    refine ⟨583535847150578327773661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 389023898100385551849107 583535847150578327773661)
                    ·
                      refine ⟨218825942681466872915123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 583535847150578327773661 218825942681466872915123)
                      ·
                        rfl

theorem cell23_426162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3].length) (baseStart_426162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426162 prefixEnd_426162 := by exact prefixLift 426162
  have htrace : WordTrace (prefixWord ++ tailWord_426162) baseStart_426162 baseEnd_426162 := by
    simpa [prefixWord, tailWord_426162, baseEnd_426162] using wordTrace_append hprefix tailTrace_426162
  have hstable : (prefixWord ++ tailWord_426162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426162).length < 2 ^ (prefixWord ++ tailWord_426162).sum := by decide
  have hdescent : baseEnd_426162 < baseStart_426162 := by decide
  rcases family_descends (prefixWord ++ tailWord_426162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426168 : List Nat := [2, 1, 2, 1, 2, 1, 5, 3, 1, 1, 4]
def baseStart_426168 : Nat := 118140960795 + 426168 * 2 ^ 59
def prefixEnd_426168 : Nat := 4983230072969 + 3 ^ 40 * 426168 * 2
def baseEnd_426168 : Nat := 218829023565393849440095

theorem tailTrace_426168 : CollatzResearch.WordTrace tailWord_426168 prefixEnd_426168 218829023565393849440095 := by
  unfold tailWord_426168
  simp only [CollatzResearch.WordTrace]
  refine ⟨7771811960036797272451579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10362415946715729696602105 7771811960036797272451579)
  ·
    refine ⟨11657717940055195908677369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7771811960036797272451579 11657717940055195908677369)
    ·
      refine ⟨8743288455041396931508027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11657717940055195908677369 8743288455041396931508027)
      ·
        refine ⟨13114932682562095397262041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8743288455041396931508027 13114932682562095397262041)
        ·
          refine ⟨9836199511921571547946531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13114932682562095397262041 9836199511921571547946531)
          ·
            refine ⟨14754299267882357321919797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9836199511921571547946531 14754299267882357321919797)
            ·
              refine ⟨1383215556363970998929981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14754299267882357321919797 1383215556363970998929981)
              ·
                refine ⟨518705833636489124598743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1383215556363970998929981 518705833636489124598743)
                ·
                  refine ⟨778058750454733686898115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 518705833636489124598743 778058750454733686898115)
                  ·
                    refine ⟨1167088125682100530347173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 778058750454733686898115 1167088125682100530347173)
                    ·
                      refine ⟨218829023565393849440095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1167088125682100530347173 218829023565393849440095)
                      ·
                        rfl

theorem cell23_426168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 1, 1, 4].length) (baseStart_426168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426168 prefixEnd_426168 := by exact prefixLift 426168
  have htrace : WordTrace (prefixWord ++ tailWord_426168) baseStart_426168 baseEnd_426168 := by
    simpa [prefixWord, tailWord_426168, baseEnd_426168] using wordTrace_append hprefix tailTrace_426168
  have hstable : (prefixWord ++ tailWord_426168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426168).length < 2 ^ (prefixWord ++ tailWord_426168).sum := by decide
  have hdescent : baseEnd_426168 < baseStart_426168 := by decide
  rcases family_descends (prefixWord ++ tailWord_426168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426171 : List Nat := [1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 5]
def baseStart_426171 : Nat := 118140960795 + 426171 * 2 ^ 59
def prefixEnd_426171 : Nat := 4983230072969 + 3 ^ 40 * 426171 * 2
def baseEnd_426171 : Nat := 218830564007357337702581

theorem tailTrace_426171 : CollatzResearch.WordTrace tailWord_426171 prefixEnd_426171 218830564007357337702581 := by
  unfold tailWord_426171
  simp only [CollatzResearch.WordTrace]
  refine ⟨15543733339062726057262367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10362488892708484038174911 15543733339062726057262367)
  ·
    refine ⟨23315600008594089085893551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15543733339062726057262367 23315600008594089085893551)
    ·
      refine ⟨34973400012891133628840327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23315600008594089085893551 34973400012891133628840327)
      ·
        refine ⟨52460100019336700443260491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34973400012891133628840327 52460100019336700443260491)
        ·
          refine ⟨78690150029005050664890737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52460100019336700443260491 78690150029005050664890737)
          ·
            refine ⟨59017612521753787998668053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78690150029005050664890737 59017612521753787998668053)
            ·
              refine ⟨2766450586957208812437565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59017612521753787998668053 2766450586957208812437565)
              ·
                refine ⟨1037418970108953304664087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2766450586957208812437565 1037418970108953304664087)
                ·
                  refine ⟨1556128455163429956996131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1037418970108953304664087 1556128455163429956996131)
                  ·
                    refine ⟨2334192682745144935494197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1556128455163429956996131 2334192682745144935494197)
                    ·
                      refine ⟨218830564007357337702581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2334192682745144935494197 218830564007357337702581)
                      ·
                        rfl

theorem cell23_426171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 5].length) (baseStart_426171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426171 prefixEnd_426171 := by exact prefixLift 426171
  have htrace : WordTrace (prefixWord ++ tailWord_426171) baseStart_426171 baseEnd_426171 := by
    simpa [prefixWord, tailWord_426171, baseEnd_426171] using wordTrace_append hprefix tailTrace_426171
  have hstable : (prefixWord ++ tailWord_426171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426171).length < 2 ^ (prefixWord ++ tailWord_426171).sum := by decide
  have hdescent : baseEnd_426171 < baseStart_426171 := by decide
  rcases family_descends (prefixWord ++ tailWord_426171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426181 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 3, 2, 4]
def baseStart_426181 : Nat := 118140960795 + 426181 * 2 ^ 59
def prefixEnd_426181 : Nat := 4983230072969 + 3 ^ 40 * 426181 * 2
def baseEnd_426181 : Nat := 218835698813902298577535

theorem tailTrace_426181 : CollatzResearch.WordTrace tailWord_426181 prefixEnd_426181 218835698813902298577535 := by
  unfold tailWord_426181
  simp only [CollatzResearch.WordTrace]
  refine ⟨15544098069026497765126397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10362732046017665176750931 15544098069026497765126397)
  ·
    refine ⟨5829036775884936661922399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15544098069026497765126397 5829036775884936661922399)
    ·
      refine ⟨8743555163827404992883599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5829036775884936661922399 8743555163827404992883599)
      ·
        refine ⟨13115332745741107489325399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8743555163827404992883599 13115332745741107489325399)
        ·
          refine ⟨19672999118611661233988099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13115332745741107489325399 19672999118611661233988099)
          ·
            refine ⟨29509498677917491850982149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19672999118611661233988099 29509498677917491850982149)
            ·
              refine ⟨5533031002109529722059153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29509498677917491850982149 5533031002109529722059153)
              ·
                refine ⟨4149773251582147291544365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5533031002109529722059153 4149773251582147291544365)
                ·
                  refine ⟨1556164969343305234329137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4149773251582147291544365 1556164969343305234329137)
                  ·
                    refine ⟨1167123727007478925746853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1556164969343305234329137 1167123727007478925746853)
                    ·
                      refine ⟨218835698813902298577535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1167123727007478925746853 218835698813902298577535)
                      ·
                        rfl

theorem cell23_426181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_426181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426181 prefixEnd_426181 := by exact prefixLift 426181
  have htrace : WordTrace (prefixWord ++ tailWord_426181) baseStart_426181 baseEnd_426181 := by
    simpa [prefixWord, tailWord_426181, baseEnd_426181] using wordTrace_append hprefix tailTrace_426181
  have hstable : (prefixWord ++ tailWord_426181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426181).length < 2 ^ (prefixWord ++ tailWord_426181).sum := by decide
  have hdescent : baseEnd_426181 < baseStart_426181 := by decide
  rcases family_descends (prefixWord ++ tailWord_426181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426218 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 3, 3, 3]
def baseStart_426218 : Nat := 118140960795 + 426218 * 2 ^ 59
def prefixEnd_426218 : Nat := 4983230072969 + 3 ^ 40 * 426218 * 2
def baseEnd_426218 : Nat := 218854697598118653814865

theorem tailTrace_426218 : CollatzResearch.WordTrace tailWord_426218 prefixEnd_426218 218854697598118653814865 := by
  unfold tailWord_426218
  simp only [CollatzResearch.WordTrace]
  refine ⟨3886361892473113271055827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10363631713261635389482205 3886361892473113271055827)
  ·
    refine ⟨5829542838709669906583741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3886361892473113271055827 5829542838709669906583741)
    ·
      refine ⟨2186078564516126214968903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5829542838709669906583741 2186078564516126214968903)
      ·
        refine ⟨3279117846774189322453355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2186078564516126214968903 3279117846774189322453355)
        ·
          refine ⟨4918676770161283983680033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3279117846774189322453355 4918676770161283983680033)
          ·
            refine ⟨3689007577620962987760025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4918676770161283983680033 3689007577620962987760025)
            ·
              refine ⟨2766755683215722240820019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3689007577620962987760025 2766755683215722240820019)
              ·
                refine ⟨4150133524823583361230029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2766755683215722240820019 4150133524823583361230029)
                ·
                  refine ⟨1556300071808843760461261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4150133524823583361230029 1556300071808843760461261)
                  ·
                    refine ⟨583612526928316410172973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1556300071808843760461261 583612526928316410172973)
                    ·
                      refine ⟨218854697598118653814865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 583612526928316410172973 218854697598118653814865)
                      ·
                        rfl

theorem cell23_426218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_426218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426218 prefixEnd_426218 := by exact prefixLift 426218
  have htrace : WordTrace (prefixWord ++ tailWord_426218) baseStart_426218 baseEnd_426218 := by
    simpa [prefixWord, tailWord_426218, baseEnd_426218] using wordTrace_append hprefix tailTrace_426218
  have hstable : (prefixWord ++ tailWord_426218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426218).length < 2 ^ (prefixWord ++ tailWord_426218).sum := by decide
  have hdescent : baseEnd_426218 < baseStart_426218 := by decide
  rcases family_descends (prefixWord ++ tailWord_426218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426236 : List Nat := [2, 2, 2, 1, 4, 2, 3, 2, 1, 2, 2]
def baseStart_426236 : Nat := 118140960795 + 426236 * 2 ^ 59
def prefixEnd_426236 : Nat := 4983230072969 + 3 ^ 40 * 426236 * 2
def baseEnd_426236 : Nat := 218863940249899583389783

theorem tailTrace_426236 : CollatzResearch.WordTrace tailWord_426236 prefixEnd_426236 218863940249899583389783 := by
  unfold tailWord_426236
  simp only [CollatzResearch.WordTrace]
  refine ⟨7773052041913621079189281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10364069389218161438919041 7773052041913621079189281)
  ·
    refine ⟨5829789031435215809391961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7773052041913621079189281 5829789031435215809391961)
    ·
      refine ⟨4372341773576411857043971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5829789031435215809391961 4372341773576411857043971)
      ·
        refine ⟨6558512660364617785565957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4372341773576411857043971 6558512660364617785565957)
        ·
          refine ⟨1229721123818365834793617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6558512660364617785565957 1229721123818365834793617)
          ·
            refine ⟨922290842863774376095213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1229721123818365834793617 922290842863774376095213)
            ·
              refine ⟨345859066073915391035705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 922290842863774376095213 345859066073915391035705)
              ·
                refine ⟨259394299555436543276779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345859066073915391035705 259394299555436543276779)
                ·
                  refine ⟨389091449333154814915169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259394299555436543276779 389091449333154814915169)
                  ·
                    refine ⟨291818586999866111186377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 389091449333154814915169 291818586999866111186377)
                    ·
                      refine ⟨218863940249899583389783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 291818586999866111186377 218863940249899583389783)
                      ·
                        rfl

theorem cell23_426236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 1, 2, 2].length) (baseStart_426236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426236 prefixEnd_426236 := by exact prefixLift 426236
  have htrace : WordTrace (prefixWord ++ tailWord_426236) baseStart_426236 baseEnd_426236 := by
    simpa [prefixWord, tailWord_426236, baseEnd_426236] using wordTrace_append hprefix tailTrace_426236
  have hstable : (prefixWord ++ tailWord_426236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426236).length < 2 ^ (prefixWord ++ tailWord_426236).sum := by decide
  have hdescent : baseEnd_426236 < baseStart_426236 := by decide
  rcases family_descends (prefixWord ++ tailWord_426236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426238 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 2, 7]
def baseStart_426238 : Nat := 118140960795 + 426238 * 2 ^ 59
def prefixEnd_426238 : Nat := 4983230072969 + 3 ^ 40 * 426238 * 2
def baseEnd_426238 : Nat := 72954989070402858521591

theorem tailTrace_426238 : CollatzResearch.WordTrace tailWord_426238 prefixEnd_426238 72954989070402858521591 := by
  unfold tailWord_426238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1943272128727499562493921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10364118019879997666634245 1943272128727499562493921)
  ·
    refine ⟨1457454096545624671870441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1943272128727499562493921 1457454096545624671870441)
    ·
      refine ⟨1093090572409218503902831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1457454096545624671870441 1093090572409218503902831)
      ·
        refine ⟨1639635858613827755854247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1093090572409218503902831 1639635858613827755854247)
        ·
          refine ⟨2459453787920741633781371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1639635858613827755854247 2459453787920741633781371)
          ·
            refine ⟨3689180681881112450672057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2459453787920741633781371 3689180681881112450672057)
            ·
              refine ⟨2766885511410834338004043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3689180681881112450672057 2766885511410834338004043)
              ·
                refine ⟨4150328267116251507006065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2766885511410834338004043 4150328267116251507006065)
                ·
                  refine ⟨3112746200337188630254549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4150328267116251507006065 3112746200337188630254549)
                  ·
                    refine ⟨72954989070402858521591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3112746200337188630254549 72954989070402858521591)
                    ·
                      rfl

theorem cell23_426238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_426238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426238 prefixEnd_426238 := by exact prefixLift 426238
  have htrace : WordTrace (prefixWord ++ tailWord_426238) baseStart_426238 baseEnd_426238 := by
    simpa [prefixWord, tailWord_426238, baseEnd_426238] using wordTrace_append hprefix tailTrace_426238
  have hstable : (prefixWord ++ tailWord_426238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426238).length < 2 ^ (prefixWord ++ tailWord_426238).sum := by decide
  have hdescent : baseEnd_426238 < baseStart_426238 := by decide
  rcases family_descends (prefixWord ++ tailWord_426238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426251 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 1, 8]
def baseStart_426251 : Nat := 118140960795 + 426251 * 2 ^ 59
def prefixEnd_426251 : Nat := 4983230072969 + 3 ^ 40 * 426251 * 2
def baseEnd_426251 : Nat := 72957214153239008234071

theorem tailTrace_426251 : CollatzResearch.WordTrace tailWord_426251 prefixEnd_426251 72957214153239008234071 := by
  unfold tailWord_426251
  simp only [CollatzResearch.WordTrace]
  refine ⟨15546651178772899720174607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10364434119181933146783071 15546651178772899720174607)
  ·
    refine ⟨23319976768159349580261911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15546651178772899720174607 23319976768159349580261911)
    ·
      refine ⟨34979965152239024370392867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23319976768159349580261911 34979965152239024370392867)
      ·
        refine ⟨52469947728358536555589301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34979965152239024370392867 52469947728358536555589301)
        ·
          refine ⟨4919057599533612802086497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52469947728358536555589301 4919057599533612802086497)
          ·
            refine ⟨3689293199650209601564873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4919057599533612802086497 3689293199650209601564873)
            ·
              refine ⟨2766969899737657201173655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3689293199650209601564873 2766969899737657201173655)
              ·
                refine ⟨4150454849606485801760483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2766969899737657201173655 4150454849606485801760483)
                ·
                  refine ⟨6225682274409728702640725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4150454849606485801760483 6225682274409728702640725)
                  ·
                    refine ⟨72957214153239008234071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6225682274409728702640725 72957214153239008234071)
                    ·
                      rfl

theorem cell23_426251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 8].length) (baseStart_426251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426251 prefixEnd_426251 := by exact prefixLift 426251
  have htrace : WordTrace (prefixWord ++ tailWord_426251) baseStart_426251 baseEnd_426251 := by
    simpa [prefixWord, tailWord_426251, baseEnd_426251] using wordTrace_append hprefix tailTrace_426251
  have hstable : (prefixWord ++ tailWord_426251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426251).length < 2 ^ (prefixWord ++ tailWord_426251).sum := by decide
  have hdescent : baseEnd_426251 < baseStart_426251 := by decide
  rcases family_descends (prefixWord ++ tailWord_426251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426275 : List Nat := [1, 1, 1, 4, 2, 2, 3, 2, 1, 4, 2]
def baseStart_426275 : Nat := 118140960795 + 426275 * 2 ^ 59
def prefixEnd_426275 : Nat := 4983230072969 + 3 ^ 40 * 426275 * 2
def baseEnd_426275 : Nat := 218883965995424930802103

theorem tailTrace_426275 : CollatzResearch.WordTrace tailWord_426275 prefixEnd_426275 218883965995424930802103 := by
  unfold tailWord_426275
  simp only [CollatzResearch.WordTrace]
  refine ⟨15547526530685951819048279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10365017687123967879365519 15547526530685951819048279)
  ·
    refine ⟨23321289796028927728572419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15547526530685951819048279 23321289796028927728572419)
    ·
      refine ⟨34981934694043391592858629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23321289796028927728572419 34981934694043391592858629)
      ·
        refine ⟨6559112755133135923660993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34981934694043391592858629 6559112755133135923660993)
        ·
          refine ⟨4919334566349851942745745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6559112755133135923660993 4919334566349851942745745)
          ·
            refine ⟨3689500924762388957059309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4919334566349851942745745 3689500924762388957059309)
            ·
              refine ⟨1383562846785895858897241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3689500924762388957059309 1383562846785895858897241)
              ·
                refine ⟨1037672135089421894172931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1383562846785895858897241 1037672135089421894172931)
                ·
                  refine ⟨1556508202634132841259397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1037672135089421894172931 1556508202634132841259397)
                  ·
                    refine ⟨291845287993899907736137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1556508202634132841259397 291845287993899907736137)
                    ·
                      refine ⟨218883965995424930802103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 291845287993899907736137 218883965995424930802103)
                      ·
                        rfl

theorem cell23_426275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 4, 2].length) (baseStart_426275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426275 prefixEnd_426275 := by exact prefixLift 426275
  have htrace : WordTrace (prefixWord ++ tailWord_426275) baseStart_426275 baseEnd_426275 := by
    simpa [prefixWord, tailWord_426275, baseEnd_426275] using wordTrace_append hprefix tailTrace_426275
  have hstable : (prefixWord ++ tailWord_426275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426275).length < 2 ^ (prefixWord ++ tailWord_426275).sum := by decide
  have hdescent : baseEnd_426275 < baseStart_426275 := by decide
  rcases family_descends (prefixWord ++ tailWord_426275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426286 : List Nat := [4, 1, 3, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_426286 : Nat := 118140960795 + 426286 * 2 ^ 59
def prefixEnd_426286 : Nat := 4983230072969 + 3 ^ 40 * 426286 * 2
def baseEnd_426286 : Nat := 218889614282624387764553

theorem tailTrace_426286 : CollatzResearch.WordTrace tailWord_426286 prefixEnd_426286 218889614282624387764553 := by
  unfold tailWord_426286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1943490966705762587212339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10365285155764067131799141 1943490966705762587212339)
  ·
    refine ⟨2915236450058643880818509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1943490966705762587212339 2915236450058643880818509)
    ·
      refine ⟨1093213668771991455306941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2915236450058643880818509 1093213668771991455306941)
      ·
        refine ⟨409955125789496795740103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1093213668771991455306941 409955125789496795740103)
        ·
          refine ⟨614932688684245193610155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409955125789496795740103 614932688684245193610155)
          ·
            refine ⟨922399033026367790415233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614932688684245193610155 922399033026367790415233)
            ·
              refine ⟨691799274769775842811425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 922399033026367790415233 691799274769775842811425)
              ·
                refine ⟨518849456077331882108569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 691799274769775842811425 518849456077331882108569)
                ·
                  refine ⟨389137092057998911581427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 518849456077331882108569 389137092057998911581427)
                  ·
                    refine ⟨583705638086998367372141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 389137092057998911581427 583705638086998367372141)
                    ·
                      refine ⟨218889614282624387764553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 583705638086998367372141 218889614282624387764553)
                      ·
                        rfl

theorem cell23_426286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_426286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426286 prefixEnd_426286 := by exact prefixLift 426286
  have htrace : WordTrace (prefixWord ++ tailWord_426286) baseStart_426286 baseEnd_426286 := by
    simpa [prefixWord, tailWord_426286, baseEnd_426286] using wordTrace_append hprefix tailTrace_426286
  have hstable : (prefixWord ++ tailWord_426286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426286).length < 2 ^ (prefixWord ++ tailWord_426286).sum := by decide
  have hdescent : baseEnd_426286 < baseStart_426286 := by decide
  rcases family_descends (prefixWord ++ tailWord_426286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426328 : List Nat := [2, 1, 2, 2, 1, 1, 2, 5, 2, 5]
def baseStart_426328 : Nat := 118140960795 + 426328 * 2 ^ 59
def prefixEnd_426328 : Nat := 4983230072969 + 3 ^ 40 * 426328 * 2
def baseEnd_426328 : Nat := 72970393490037741146453

theorem tailTrace_426328 : CollatzResearch.WordTrace tailWord_426328 prefixEnd_426328 72970393490037741146453 := by
  unfold tailWord_426328
  simp only [CollatzResearch.WordTrace]
  refine ⟨7774729799746970935363819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10366306399662627913818425 7774729799746970935363819)
  ·
    refine ⟨11662094699620456403045729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7774729799746970935363819 11662094699620456403045729)
    ·
      refine ⟨8746571024715342302284297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11662094699620456403045729 8746571024715342302284297)
      ·
        refine ⟨6559928268536506726713223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8746571024715342302284297 6559928268536506726713223)
        ·
          refine ⟨9839892402804760090069835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6559928268536506726713223 9839892402804760090069835)
          ·
            refine ⟨14759838604207140135104753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9839892402804760090069835 14759838604207140135104753)
            ·
              refine ⟨11069878953155355101328565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14759838604207140135104753 11069878953155355101328565)
              ·
                refine ⟨1037801151858314540749553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11069878953155355101328565 1037801151858314540749553)
                ·
                  refine ⟨778350863893735905562165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1037801151858314540749553 778350863893735905562165)
                  ·
                    refine ⟨72970393490037741146453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 778350863893735905562165 72970393490037741146453)
                    ·
                      rfl

theorem cell23_426328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_426328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426328 prefixEnd_426328 := by exact prefixLift 426328
  have htrace : WordTrace (prefixWord ++ tailWord_426328) baseStart_426328 baseEnd_426328 := by
    simpa [prefixWord, tailWord_426328, baseEnd_426328] using wordTrace_append hprefix tailTrace_426328
  have hstable : (prefixWord ++ tailWord_426328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426328).length < 2 ^ (prefixWord ++ tailWord_426328).sum := by decide
  have hdescent : baseEnd_426328 < baseStart_426328 := by decide
  rcases family_descends (prefixWord ++ tailWord_426328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426331 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 10]
def baseStart_426331 : Nat := 118140960795 + 426331 * 2 ^ 59
def prefixEnd_426331 : Nat := 4983230072969 + 3 ^ 40 * 426331 * 2
def baseEnd_426331 : Nat := 218912720912076711701845

theorem tailTrace_426331 : CollatzResearch.WordTrace tailWord_426331 prefixEnd_426331 218912720912076711701845 := by
  unfold tailWord_426331
  simp only [CollatzResearch.WordTrace]
  refine ⟨15549569018483073383086847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10366379345655382255391231 15549569018483073383086847)
  ·
    refine ⟨23324353527724610074630271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15549569018483073383086847 23324353527724610074630271)
    ·
      refine ⟨34986530291586915111945407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23324353527724610074630271 34986530291586915111945407)
      ·
        refine ⟨52479795437380372667918111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34986530291586915111945407 52479795437380372667918111)
        ·
          refine ⟨78719693156070559001877167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52479795437380372667918111 78719693156070559001877167)
          ·
            refine ⟨118079539734105838502815751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78719693156070559001877167 118079539734105838502815751)
            ·
              refine ⟨177119309601158757754223627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118079539734105838502815751 177119309601158757754223627)
              ·
                refine ⟨265678964401738136631335441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177119309601158757754223627 265678964401738136631335441)
                ·
                  refine ⟨199259223301303602473501581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265678964401738136631335441 199259223301303602473501581)
                  ·
                    refine ⟨74722208737988850927563093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 199259223301303602473501581 74722208737988850927563093)
                    ·
                      refine ⟨218912720912076711701845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 74722208737988850927563093 218912720912076711701845)
                      ·
                        rfl

theorem cell23_426331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 10].length) (baseStart_426331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426331 prefixEnd_426331 := by exact prefixLift 426331
  have htrace : WordTrace (prefixWord ++ tailWord_426331) baseStart_426331 baseEnd_426331 := by
    simpa [prefixWord, tailWord_426331, baseEnd_426331] using wordTrace_append hprefix tailTrace_426331
  have hstable : (prefixWord ++ tailWord_426331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426331).length < 2 ^ (prefixWord ++ tailWord_426331).sum := by decide
  have hdescent : baseEnd_426331 < baseStart_426331 := by decide
  rcases family_descends (prefixWord ++ tailWord_426331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426375 : List Nat := [1, 1, 4, 2, 2, 1, 1, 4, 3, 4]
def baseStart_426375 : Nat := 118140960795 + 426375 * 2 ^ 59
def prefixEnd_426375 : Nat := 4983230072969 + 3 ^ 40 * 426375 * 2
def baseEnd_426375 : Nat := 72978438020291513183881

theorem tailTrace_426375 : CollatzResearch.WordTrace tailWord_426375 prefixEnd_426375 72978438020291513183881 := by
  unfold tailWord_426375
  simp only [CollatzResearch.WordTrace]
  refine ⟨15551173830323668897688579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10367449220215779265125719 15551173830323668897688579)
  ·
    refine ⟨23326760745485503346532869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15551173830323668897688579 23326760745485503346532869)
    ·
      refine ⟨4373767639778531877474913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23326760745485503346532869 4373767639778531877474913)
      ·
        refine ⟨3280325729833898908106185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4373767639778531877474913 3280325729833898908106185)
        ·
          refine ⟨2460244297375424181079639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3280325729833898908106185 2460244297375424181079639)
          ·
            refine ⟨3690366446063136271619459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2460244297375424181079639 3690366446063136271619459)
            ·
              refine ⟨5535549669094704407429189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3690366446063136271619459 5535549669094704407429189)
              ·
                refine ⟨1037915562955257076392973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5535549669094704407429189 1037915562955257076392973)
                ·
                  refine ⟨389218336108221403647365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1037915562955257076392973 389218336108221403647365)
                  ·
                    refine ⟨72978438020291513183881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 389218336108221403647365 72978438020291513183881)
                    ·
                      rfl

theorem cell23_426375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_426375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426375 prefixEnd_426375 := by exact prefixLift 426375
  have htrace : WordTrace (prefixWord ++ tailWord_426375) baseStart_426375 baseEnd_426375 := by
    simpa [prefixWord, tailWord_426375, baseEnd_426375] using wordTrace_append hprefix tailTrace_426375
  have hstable : (prefixWord ++ tailWord_426375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426375).length < 2 ^ (prefixWord ++ tailWord_426375).sum := by decide
  have hdescent : baseEnd_426375 < baseStart_426375 := by decide
  rcases family_descends (prefixWord ++ tailWord_426375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426402 : List Nat := [3, 3, 1, 2, 1, 1, 3, 2, 2, 2, 3]
def baseStart_426402 : Nat := 118140960795 + 426402 * 2 ^ 59
def prefixEnd_426402 : Nat := 4983230072969 + 3 ^ 40 * 426402 * 2
def baseEnd_426402 : Nat := 218949178038545933914019

theorem tailTrace_426402 : CollatzResearch.WordTrace tailWord_426402 prefixEnd_426402 218949178038545933914019 := by
  unfold tailWord_426402
  simp only [CollatzResearch.WordTrace]
  refine ⟨3888039650306463127230365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10368105734150568339280973 3888039650306463127230365)
  ·
    refine ⟨1458014868864923672711387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3888039650306463127230365 1458014868864923672711387)
    ·
      refine ⟨2187022303297385509067081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1458014868864923672711387 2187022303297385509067081)
      ·
        refine ⟨1640266727473039131800311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2187022303297385509067081 1640266727473039131800311)
        ·
          refine ⟨2460400091209558697700467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1640266727473039131800311 2460400091209558697700467)
          ·
            refine ⟨3690600136814338046550701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2460400091209558697700467 3690600136814338046550701)
            ·
              refine ⟨1383975051305376767456513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3690600136814338046550701 1383975051305376767456513)
              ·
                refine ⟨1037981288479032575592385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1383975051305376767456513 1037981288479032575592385)
                ·
                  refine ⟨778485966359274431694289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1037981288479032575592385 778485966359274431694289)
                  ·
                    refine ⟨583864474769455823770717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 778485966359274431694289 583864474769455823770717)
                    ·
                      refine ⟨218949178038545933914019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 583864474769455823770717 218949178038545933914019)
                      ·
                        rfl

theorem cell23_426402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_426402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426402 prefixEnd_426402 := by exact prefixLift 426402
  have htrace : WordTrace (prefixWord ++ tailWord_426402) baseStart_426402 baseEnd_426402 := by
    simpa [prefixWord, tailWord_426402, baseEnd_426402] using wordTrace_append hprefix tailTrace_426402
  have hstable : (prefixWord ++ tailWord_426402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426402).length < 2 ^ (prefixWord ++ tailWord_426402).sum := by decide
  have hdescent : baseEnd_426402 < baseStart_426402 := by decide
  rcases family_descends (prefixWord ++ tailWord_426402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426475 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 3]
def baseStart_426475 : Nat := 118140960795 + 426475 * 2 ^ 59
def prefixEnd_426475 : Nat := 4983230072969 + 3 ^ 40 * 426475 * 2
def baseEnd_426475 : Nat := 218986662126324148301183

theorem tailTrace_426475 : CollatzResearch.WordTrace tailWord_426475 prefixEnd_426475 218986662126324148301183 := by
  unfold tailWord_426475
  simp only [CollatzResearch.WordTrace]
  refine ⟨15554821129961385976328879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10369880753307590650885919 15554821129961385976328879)
  ·
    refine ⟨23332231694942078964493319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15554821129961385976328879 23332231694942078964493319)
    ·
      refine ⟨34998347542413118446739979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23332231694942078964493319 34998347542413118446739979)
      ·
        refine ⟨52497521313619677670109969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34998347542413118446739979 52497521313619677670109969)
        ·
          refine ⟨39373140985214758252582477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52497521313619677670109969 39373140985214758252582477)
          ·
            refine ⟨14764927869455534344718429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39373140985214758252582477 14764927869455534344718429)
            ·
              refine ⟨5536847951045825379269411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14764927869455534344718429 5536847951045825379269411)
              ·
                refine ⟨8305271926568738068904117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5536847951045825379269411 8305271926568738068904117)
                ·
                  refine ⟨778619243115819193959761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8305271926568738068904117 778619243115819193959761)
                  ·
                    refine ⟨583964432336864395469821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 778619243115819193959761 583964432336864395469821)
                    ·
                      refine ⟨218986662126324148301183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 583964432336864395469821 218986662126324148301183)
                      ·
                        rfl

theorem cell23_426475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 3].length) (baseStart_426475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426475 prefixEnd_426475 := by exact prefixLift 426475
  have htrace : WordTrace (prefixWord ++ tailWord_426475) baseStart_426475 baseEnd_426475 := by
    simpa [prefixWord, tailWord_426475, baseEnd_426475] using wordTrace_append hprefix tailTrace_426475
  have hstable : (prefixWord ++ tailWord_426475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426475).length < 2 ^ (prefixWord ++ tailWord_426475).sum := by decide
  have hdescent : baseEnd_426475 < baseStart_426475 := by decide
  rcases family_descends (prefixWord ++ tailWord_426475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426492 : List Nat := [2, 2, 2, 1, 2, 1, 1, 6, 1, 2, 3]
def baseStart_426492 : Nat := 118140960795 + 426492 * 2 ^ 59
def prefixEnd_426492 : Nat := 4983230072969 + 3 ^ 40 * 426492 * 2
def baseEnd_426492 : Nat := 218995391297450581788605

theorem tailTrace_426492 : CollatzResearch.WordTrace tailWord_426492 prefixEnd_426492 218995391297450581788605 := by
  unfold tailWord_426492
  simp only [CollatzResearch.WordTrace]
  refine ⟨7777720585449898939848865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10370294113933198586465153 7777720585449898939848865)
  ·
    refine ⟨5833290439087424204886649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7777720585449898939848865 5833290439087424204886649)
    ·
      refine ⟨4374967829315568153664987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5833290439087424204886649 4374967829315568153664987)
      ·
        refine ⟨6562451743973352230497481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4374967829315568153664987 6562451743973352230497481)
        ·
          refine ⟨4921838807980014172873111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6562451743973352230497481 4921838807980014172873111)
          ·
            refine ⟨7382758211970021259309667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4921838807980014172873111 7382758211970021259309667)
            ·
              refine ⟨11074137317955031888964501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7382758211970021259309667 11074137317955031888964501)
              ·
                refine ⟨519100186779142119795211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11074137317955031888964501 519100186779142119795211)
                ·
                  refine ⟨778650280168713179692817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 519100186779142119795211 778650280168713179692817)
                  ·
                    refine ⟨583987710126534884769613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 778650280168713179692817 583987710126534884769613)
                    ·
                      refine ⟨218995391297450581788605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 583987710126534884769613 218995391297450581788605)
                      ·
                        rfl

theorem cell23_426492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_426492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426492 prefixEnd_426492 := by exact prefixLift 426492
  have htrace : WordTrace (prefixWord ++ tailWord_426492) baseStart_426492 baseEnd_426492 := by
    simpa [prefixWord, tailWord_426492, baseEnd_426492] using wordTrace_append hprefix tailTrace_426492
  have hstable : (prefixWord ++ tailWord_426492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426492).length < 2 ^ (prefixWord ++ tailWord_426492).sum := by decide
  have hdescent : baseEnd_426492 < baseStart_426492 := by decide
  rcases family_descends (prefixWord ++ tailWord_426492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426495 : List Nat := [1, 1, 2, 2, 1, 2, 7, 7]
def baseStart_426495 : Nat := 118140960795 + 426495 * 2 ^ 59
def prefixEnd_426495 : Nat := 4983230072969 + 3 ^ 40 * 426495 * 2
def baseEnd_426495 : Nat := 8110997471830150742633

theorem tailTrace_426495 : CollatzResearch.WordTrace tailWord_426495 prefixEnd_426495 8110997471830150742633 := by
  unfold tailWord_426495
  simp only [CollatzResearch.WordTrace]
  refine ⟨15555550589888929392056939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10370367059925952928037959 15555550589888929392056939)
  ·
    refine ⟨23333325884833394088085409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15555550589888929392056939 23333325884833394088085409)
    ·
      refine ⟨17499994413625045566064057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23333325884833394088085409 17499994413625045566064057)
      ·
        refine ⟨13124995810218784174548043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17499994413625045566064057 13124995810218784174548043)
        ·
          refine ⟨19687493715328176261822065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13124995810218784174548043 19687493715328176261822065)
          ·
            refine ⟨14765620286496132196366549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19687493715328176261822065 14765620286496132196366549)
            ·
              refine ⟨346069225464753098352341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 14765620286496132196366549 346069225464753098352341)
              ·
                refine ⟨8110997471830150742633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 346069225464753098352341 8110997471830150742633)
                ·
                  rfl

theorem cell23_426495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 7].length) (baseStart_426495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426495 prefixEnd_426495 := by exact prefixLift 426495
  have htrace : WordTrace (prefixWord ++ tailWord_426495) baseStart_426495 baseEnd_426495 := by
    simpa [prefixWord, tailWord_426495, baseEnd_426495] using wordTrace_append hprefix tailTrace_426495
  have hstable : (prefixWord ++ tailWord_426495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426495).length < 2 ^ (prefixWord ++ tailWord_426495).sum := by decide
  have hdescent : baseEnd_426495 < baseStart_426495 := by decide
  rcases family_descends (prefixWord ++ tailWord_426495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426505 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 3, 3, 3]
def baseStart_426505 : Nat := 118140960795 + 426505 * 2 ^ 59
def prefixEnd_426505 : Nat := 4983230072969 + 3 ^ 40 * 426505 * 2
def baseEnd_426505 : Nat := 219002066545959030926045

theorem tailTrace_426505 : CollatzResearch.WordTrace tailWord_426505 prefixEnd_426505 219002066545959030926045 := by
  unfold tailWord_426505
  simp only [CollatzResearch.WordTrace]
  refine ⟨15555915319852701099920969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10370610213235134066613979 15555915319852701099920969)
  ·
    refine ⟨11666936489889525824940727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15555915319852701099920969 11666936489889525824940727)
    ·
      refine ⟨17500404734834288737411091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11666936489889525824940727 17500404734834288737411091)
      ·
        refine ⟨26250607102251433106116637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17500404734834288737411091 26250607102251433106116637)
        ·
          refine ⟨9843977663344287414793739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26250607102251433106116637 9843977663344287414793739)
          ·
            refine ⟨14765966495016431122190609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9843977663344287414793739 14765966495016431122190609)
            ·
              refine ⟨11074474871262323341642957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14765966495016431122190609 11074474871262323341642957)
              ·
                refine ⟨4152928076723371253116109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11074474871262323341642957 4152928076723371253116109)
                ·
                  refine ⟨1557348028771264219918541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4152928076723371253116109 1557348028771264219918541)
                  ·
                    refine ⟨584005510789224082469453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1557348028771264219918541 584005510789224082469453)
                    ·
                      refine ⟨219002066545959030926045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 584005510789224082469453 219002066545959030926045)
                      ·
                        rfl

theorem cell23_426505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 3, 3].length) (baseStart_426505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426505 prefixEnd_426505 := by exact prefixLift 426505
  have htrace : WordTrace (prefixWord ++ tailWord_426505) baseStart_426505 baseEnd_426505 := by
    simpa [prefixWord, tailWord_426505, baseEnd_426505] using wordTrace_append hprefix tailTrace_426505
  have hstable : (prefixWord ++ tailWord_426505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426505).length < 2 ^ (prefixWord ++ tailWord_426505).sum := by decide
  have hdescent : baseEnd_426505 < baseStart_426505 := by decide
  rcases family_descends (prefixWord ++ tailWord_426505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426516 : List Nat := [2, 4, 3, 1, 1, 1, 3, 2, 2, 4]
def baseStart_426516 : Nat := 118140960795 + 426516 * 2 ^ 59
def prefixEnd_426516 : Nat := 4983230072969 + 3 ^ 40 * 426516 * 2
def baseEnd_426516 : Nat := 73002571611052829296165

theorem tailTrace_426516 : CollatzResearch.WordTrace tailWord_426516 prefixEnd_426516 73002571611052829296165 := by
  unfold tailWord_426516
  simp only [CollatzResearch.WordTrace]
  refine ⟨7778158261406424989285701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10370877681875233319047601 7778158261406424989285701)
  ·
    refine ⟨1458404674013704685491069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7778158261406424989285701 1458404674013704685491069)
    ·
      refine ⟨546901752755139257059151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1458404674013704685491069 546901752755139257059151)
      ·
        refine ⟨820352629132708885588727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546901752755139257059151 820352629132708885588727)
        ·
          refine ⟨1230528943699063328383091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 820352629132708885588727 1230528943699063328383091)
          ·
            refine ⟨1845793415548594992574637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1230528943699063328383091 1845793415548594992574637)
            ·
              refine ⟨692172530830723122215489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1845793415548594992574637 692172530830723122215489)
              ·
                refine ⟨519129398123042341661617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 692172530830723122215489 519129398123042341661617)
                ·
                  refine ⟨389347048592281756246213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519129398123042341661617 389347048592281756246213)
                  ·
                    refine ⟨73002571611052829296165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 389347048592281756246213 73002571611052829296165)
                    ·
                      rfl

theorem cell23_426516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_426516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426516 prefixEnd_426516 := by exact prefixLift 426516
  have htrace : WordTrace (prefixWord ++ tailWord_426516) baseStart_426516 baseEnd_426516 := by
    simpa [prefixWord, tailWord_426516, baseEnd_426516] using wordTrace_append hprefix tailTrace_426516
  have hstable : (prefixWord ++ tailWord_426516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426516).length < 2 ^ (prefixWord ++ tailWord_426516).sum := by decide
  have hdescent : baseEnd_426516 < baseStart_426516 := by decide
  rcases family_descends (prefixWord ++ tailWord_426516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426545 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 2, 3, 4]
def baseStart_426545 : Nat := 118140960795 + 426545 * 2 ^ 59
def prefixEnd_426545 : Nat := 4983230072969 + 3 ^ 40 * 426545 * 2
def baseEnd_426545 : Nat := 219022605772138874425861

theorem tailTrace_426545 : CollatzResearch.WordTrace tailWord_426545 prefixEnd_426545 219022605772138874425861 := by
  unfold tailWord_426545
  simp only [CollatzResearch.WordTrace]
  refine ⟨15557374239707787931377089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10371582826471858620918059 15557374239707787931377089)
  ·
    refine ⟨11668030679780840948532817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15557374239707787931377089 11668030679780840948532817)
    ·
      refine ⟨8751023009835630711399613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11668030679780840948532817 8751023009835630711399613)
      ·
        refine ⟨3281633628688361516774855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8751023009835630711399613 3281633628688361516774855)
        ·
          refine ⟨4922450443032542275162283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3281633628688361516774855 4922450443032542275162283)
          ·
            refine ⟨7383675664548813412743425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4922450443032542275162283 7383675664548813412743425)
            ·
              refine ⟨5537756748411610059557569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7383675664548813412743425 5537756748411610059557569)
              ·
                refine ⟨4153317561308707544668177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5537756748411610059557569 4153317561308707544668177)
                ·
                  refine ⟨3114988170981530658501133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4153317561308707544668177 3114988170981530658501133)
                  ·
                    refine ⟨1168120564118073996937925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3114988170981530658501133 1168120564118073996937925)
                    ·
                      refine ⟨219022605772138874425861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1168120564118073996937925 219022605772138874425861)
                      ·
                        rfl

theorem cell23_426545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_426545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426545 prefixEnd_426545 := by exact prefixLift 426545
  have htrace : WordTrace (prefixWord ++ tailWord_426545) baseStart_426545 baseEnd_426545 := by
    simpa [prefixWord, tailWord_426545, baseEnd_426545] using wordTrace_append hprefix tailTrace_426545
  have hstable : (prefixWord ++ tailWord_426545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426545).length < 2 ^ (prefixWord ++ tailWord_426545).sum := by decide
  have hdescent : baseEnd_426545 < baseStart_426545 := by decide
  rcases family_descends (prefixWord ++ tailWord_426545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426565 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 1, 3, 5]
def baseStart_426565 : Nat := 118140960795 + 426565 * 2 ^ 59
def prefixEnd_426565 : Nat := 4983230072969 + 3 ^ 40 * 426565 * 2
def baseEnd_426565 : Nat := 219032875385228796175769

theorem tailTrace_426565 : CollatzResearch.WordTrace tailWord_426565 prefixEnd_426565 219032875385228796175769 := by
  unfold tailWord_426565
  simp only [CollatzResearch.WordTrace]
  refine ⟨15558103699635331347105149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10372069133090220898070099 15558103699635331347105149)
  ·
    refine ⟨5834288887363249255164431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15558103699635331347105149 5834288887363249255164431)
    ·
      refine ⟨8751433331044873882746647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5834288887363249255164431 8751433331044873882746647)
      ·
        refine ⟨13127149996567310824119971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8751433331044873882746647 13127149996567310824119971)
        ·
          refine ⟨19690724994850966236179957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13127149996567310824119971 19690724994850966236179957)
          ·
            refine ⟨1846005468267278084641871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19690724994850966236179957 1846005468267278084641871)
            ·
              refine ⟨2769008202400917126962807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1846005468267278084641871 2769008202400917126962807)
              ·
                refine ⟨4153512303601375690444211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2769008202400917126962807 4153512303601375690444211)
                ·
                  refine ⟨6230268455402063535666317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4153512303601375690444211 6230268455402063535666317)
                  ·
                    refine ⟨2336350670775773825874869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6230268455402063535666317 2336350670775773825874869)
                    ·
                      refine ⟨219032875385228796175769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2336350670775773825874869 219032875385228796175769)
                      ·
                        rfl

theorem cell23_426565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_426565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426565 prefixEnd_426565 := by exact prefixLift 426565
  have htrace : WordTrace (prefixWord ++ tailWord_426565) baseStart_426565 baseEnd_426565 := by
    simpa [prefixWord, tailWord_426565, baseEnd_426565] using wordTrace_append hprefix tailTrace_426565
  have hstable : (prefixWord ++ tailWord_426565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426565).length < 2 ^ (prefixWord ++ tailWord_426565).sum := by decide
  have hdescent : baseEnd_426565 < baseStart_426565 := by decide
  rcases family_descends (prefixWord ++ tailWord_426565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426575 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 4]
def baseStart_426575 : Nat := 118140960795 + 426575 * 2 ^ 59
def prefixEnd_426575 : Nat := 4983230072969 + 3 ^ 40 * 426575 * 2
def baseEnd_426575 : Nat := 219038010191773757050723

theorem tailTrace_426575 : CollatzResearch.WordTrace tailWord_426575 prefixEnd_426575 219038010191773757050723 := by
  unfold tailWord_426575
  simp only [CollatzResearch.WordTrace]
  refine ⟨15558468429599103054969179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10372312286399402036646119 15558468429599103054969179)
  ·
    refine ⟨23337702644398654582453769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15558468429599103054969179 23337702644398654582453769)
    ·
      refine ⟨17503276983298990936840327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23337702644398654582453769 17503276983298990936840327)
      ·
        refine ⟨26254915474948486405260491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17503276983298990936840327 26254915474948486405260491)
        ·
          refine ⟨39382373212422729607890737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26254915474948486405260491 39382373212422729607890737)
          ·
            refine ⟨29536779909317047205918053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39382373212422729607890737 29536779909317047205918053)
            ·
              refine ⟨5538146232996946351109635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29536779909317047205918053 5538146232996946351109635)
              ·
                refine ⟨8307219349495419526664453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5538146232996946351109635 8307219349495419526664453)
                ·
                  refine ⟨1557603628030391161249585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8307219349495419526664453 1557603628030391161249585)
                  ·
                    refine ⟨1168202721022793370937189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1557603628030391161249585 1168202721022793370937189)
                    ·
                      refine ⟨219038010191773757050723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1168202721022793370937189 219038010191773757050723)
                      ·
                        rfl

theorem cell23_426575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 4].length) (baseStart_426575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426575 prefixEnd_426575 := by exact prefixLift 426575
  have htrace : WordTrace (prefixWord ++ tailWord_426575) baseStart_426575 baseEnd_426575 := by
    simpa [prefixWord, tailWord_426575, baseEnd_426575] using wordTrace_append hprefix tailTrace_426575
  have hstable : (prefixWord ++ tailWord_426575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426575).length < 2 ^ (prefixWord ++ tailWord_426575).sum := by decide
  have hdescent : baseEnd_426575 < baseStart_426575 := by decide
  rcases family_descends (prefixWord ++ tailWord_426575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426596 : List Nat := [2, 3, 1, 1, 2, 2, 3, 3, 2, 2, 2]
def baseStart_426596 : Nat := 118140960795 + 426596 * 2 ^ 59
def prefixEnd_426596 : Nat := 4983230072969 + 3 ^ 40 * 426596 * 2
def baseEnd_426596 : Nat := 219048793285518174888127

theorem tailTrace_426596 : CollatzResearch.WordTrace tailWord_426596 prefixEnd_426596 219048793285518174888127 := by
  unfold tailWord_426596
  simp only [CollatzResearch.WordTrace]
  refine ⟨7779617181261511820741821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10372822908348682427655761 7779617181261511820741821)
  ·
    refine ⟨2917356442973066932778183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7779617181261511820741821 2917356442973066932778183)
    ·
      refine ⟨4376034664459600399167275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2917356442973066932778183 4376034664459600399167275)
      ·
        refine ⟨6564051996689400598750913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4376034664459600399167275 6564051996689400598750913)
        ·
          refine ⟨4923038997517050449063185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6564051996689400598750913 4923038997517050449063185)
          ·
            refine ⟨3692279248137787836797389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4923038997517050449063185 3692279248137787836797389)
            ·
              refine ⟨1384604718051670438799021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3692279248137787836797389 1384604718051670438799021)
              ·
                refine ⟨519226769269376414549633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1384604718051670438799021 519226769269376414549633)
                ·
                  refine ⟨389420076952032310912225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519226769269376414549633 389420076952032310912225)
                  ·
                    refine ⟨292065057714024233184169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 389420076952032310912225 292065057714024233184169)
                    ·
                      refine ⟨219048793285518174888127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 292065057714024233184169 219048793285518174888127)
                      ·
                        rfl

theorem cell23_426596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 2, 2, 2].length) (baseStart_426596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426596 prefixEnd_426596 := by exact prefixLift 426596
  have htrace : WordTrace (prefixWord ++ tailWord_426596) baseStart_426596 baseEnd_426596 := by
    simpa [prefixWord, tailWord_426596, baseEnd_426596] using wordTrace_append hprefix tailTrace_426596
  have hstable : (prefixWord ++ tailWord_426596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426596).length < 2 ^ (prefixWord ++ tailWord_426596).sum := by decide
  have hdescent : baseEnd_426596 < baseStart_426596 := by decide
  rcases family_descends (prefixWord ++ tailWord_426596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426600 : List Nat := [2, 1, 4, 3, 3, 1, 1, 2, 1, 3, 2]
def baseStart_426600 : Nat := 118140960795 + 426600 * 2 ^ 59
def prefixEnd_426600 : Nat := 4983230072969 + 3 ^ 40 * 426600 * 2
def baseEnd_426600 : Nat := 219050847208136159238109

theorem tailTrace_426600 : CollatzResearch.WordTrace tailWord_426600 prefixEnd_426600 219050847208136159238109 := by
  unfold tailWord_426600
  simp only [CollatzResearch.WordTrace]
  refine ⟨7779690127254266162314627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10372920169672354883086169 7779690127254266162314627)
  ·
    refine ⟨11669535190881399243471941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7779690127254266162314627 11669535190881399243471941)
    ·
      refine ⟨2188037848290262358150989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11669535190881399243471941 2188037848290262358150989)
      ·
        refine ⟨820514193108848384306621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2188037848290262358150989 820514193108848384306621)
        ·
          refine ⟨307692822415818144114983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 820514193108848384306621 307692822415818144114983)
          ·
            refine ⟨461539233623727216172475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307692822415818144114983 461539233623727216172475)
            ·
              refine ⟨692308850435590824258713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461539233623727216172475 692308850435590824258713)
              ·
                refine ⟨519231637826693118194035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 692308850435590824258713 519231637826693118194035)
                ·
                  refine ⟨778847456740039677291053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 519231637826693118194035 778847456740039677291053)
                  ·
                    refine ⟨292067796277514878984145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 778847456740039677291053 292067796277514878984145)
                    ·
                      refine ⟨219050847208136159238109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 292067796277514878984145 219050847208136159238109)
                      ·
                        rfl

theorem cell23_426600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_426600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426600 prefixEnd_426600 := by exact prefixLift 426600
  have htrace : WordTrace (prefixWord ++ tailWord_426600) baseStart_426600 baseEnd_426600 := by
    simpa [prefixWord, tailWord_426600, baseEnd_426600] using wordTrace_append hprefix tailTrace_426600
  have hstable : (prefixWord ++ tailWord_426600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426600).length < 2 ^ (prefixWord ++ tailWord_426600).sum := by decide
  have hdescent : baseEnd_426600 < baseStart_426600 := by decide
  rcases family_descends (prefixWord ++ tailWord_426600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426615 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 1, 7]
def baseStart_426615 : Nat := 118140960795 + 426615 * 2 ^ 59
def prefixEnd_426615 : Nat := 4983230072969 + 3 ^ 40 * 426615 * 2
def baseEnd_426615 : Nat := 73019516472651200183513

theorem tailTrace_426615 : CollatzResearch.WordTrace tailWord_426615 prefixEnd_426615 73019516472651200183513 := by
  unfold tailWord_426615
  simp only [CollatzResearch.WordTrace]
  refine ⟨15559927349454189886425299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10373284899636126590950199 15559927349454189886425299)
  ·
    refine ⟨23339891024181284829637949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15559927349454189886425299 23339891024181284829637949)
    ·
      refine ⟨8752459134067981811114231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23339891024181284829637949 8752459134067981811114231)
      ·
        refine ⟨13128688701101972716671347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8752459134067981811114231 13128688701101972716671347)
        ·
          refine ⟨19693033051652959075007021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13128688701101972716671347 19693033051652959075007021)
          ·
            refine ⟨7384887394369859653127633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19693033051652959075007021 7384887394369859653127633)
            ·
              refine ⟨5538665545777394739845725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7384887394369859653127633 5538665545777394739845725)
              ·
                refine ⟨2076999579666523027442147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5538665545777394739845725 2076999579666523027442147)
                ·
                  refine ⟨3115499369499784541163221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2076999579666523027442147 3115499369499784541163221)
                  ·
                    refine ⟨73019516472651200183513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3115499369499784541163221 73019516472651200183513)
                    ·
                      rfl

theorem cell23_426615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_426615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426615 prefixEnd_426615 := by exact prefixLift 426615
  have htrace : WordTrace (prefixWord ++ tailWord_426615) baseStart_426615 baseEnd_426615 := by
    simpa [prefixWord, tailWord_426615, baseEnd_426615] using wordTrace_append hprefix tailTrace_426615
  have hstable : (prefixWord ++ tailWord_426615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426615).length < 2 ^ (prefixWord ++ tailWord_426615).sum := by decide
  have hdescent : baseEnd_426615 < baseStart_426615 := by decide
  rcases family_descends (prefixWord ++ tailWord_426615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426645 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 4, 8]
def baseStart_426645 : Nat := 118140960795 + 426645 * 2 ^ 59
def prefixEnd_426645 : Nat := 4983230072969 + 3 ^ 40 * 426645 * 2
def baseEnd_426645 : Nat := 73024651279196161058467

theorem tailTrace_426645 : CollatzResearch.WordTrace tailWord_426645 prefixEnd_426645 73024651279196161058467 := by
  unfold tailWord_426645
  simp only [CollatzResearch.WordTrace]
  refine ⟨15561021539345505010017389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10374014359563670006678259 15561021539345505010017389)
  ·
    refine ⟨5835383077254564378756521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15561021539345505010017389 5835383077254564378756521)
    ·
      refine ⟨4376537307940923284067391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5835383077254564378756521 4376537307940923284067391)
      ·
        refine ⟨6564805961911384926101087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4376537307940923284067391 6564805961911384926101087)
        ·
          refine ⟨9847208942867077389151631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6564805961911384926101087 9847208942867077389151631)
          ·
            refine ⟨14770813414300616083727447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9847208942867077389151631 14770813414300616083727447)
            ·
              refine ⟨22156220121450924125591171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14770813414300616083727447 22156220121450924125591171)
              ·
                refine ⟨33234330182176386188386757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22156220121450924125591171 33234330182176386188386757)
                ·
                  refine ⟨6231436909158072410322517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33234330182176386188386757 6231436909158072410322517)
                  ·
                    refine ⟨73024651279196161058467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6231436909158072410322517 73024651279196161058467)
                    ·
                      rfl

theorem cell23_426645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_426645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426645 prefixEnd_426645 := by exact prefixLift 426645
  have htrace : WordTrace (prefixWord ++ tailWord_426645) baseStart_426645 baseEnd_426645 := by
    simpa [prefixWord, tailWord_426645, baseEnd_426645] using wordTrace_append hprefix tailTrace_426645
  have hstable : (prefixWord ++ tailWord_426645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426645).length < 2 ^ (prefixWord ++ tailWord_426645).sum := by decide
  have hdescent : baseEnd_426645 < baseStart_426645 := by decide
  rcases family_descends (prefixWord ++ tailWord_426645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426665 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 1, 3, 6]
def baseStart_426665 : Nat := 118140960795 + 426665 * 2 ^ 59
def prefixEnd_426665 : Nat := 4983230072969 + 3 ^ 40 * 426665 * 2
def baseEnd_426665 : Nat := 219084223450678404925309

theorem tailTrace_426665 : CollatzResearch.WordTrace tailWord_426665 prefixEnd_426665 219084223450678404925309 := by
  unfold tailWord_426665
  simp only [CollatzResearch.WordTrace]
  refine ⟨15561750999273048425745449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10374500666182032283830299 15561750999273048425745449)
  ·
    refine ⟨11671313249454786319309087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15561750999273048425745449 11671313249454786319309087)
    ·
      refine ⟨17506969874182179478963631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11671313249454786319309087 17506969874182179478963631)
      ·
        refine ⟨26260454811273269218445447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17506969874182179478963631 26260454811273269218445447)
        ·
          refine ⟨39390682216909903827668171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26260454811273269218445447 39390682216909903827668171)
          ·
            refine ⟨59086023325364855741502257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39390682216909903827668171 59086023325364855741502257)
            ·
              refine ⟨44314517494023641806126693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59086023325364855741502257 44314517494023641806126693)
              ·
                refine ⟨8308972030129432838648755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44314517494023641806126693 8308972030129432838648755)
                ·
                  refine ⟨12463458045194149257973133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8308972030129432838648755 12463458045194149257973133)
                  ·
                    refine ⟨4673796766947805971739925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12463458045194149257973133 4673796766947805971739925)
                    ·
                      refine ⟨219084223450678404925309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4673796766947805971739925 219084223450678404925309)
                      ·
                        rfl

theorem cell23_426665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_426665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426665 prefixEnd_426665 := by exact prefixLift 426665
  have htrace : WordTrace (prefixWord ++ tailWord_426665) baseStart_426665 baseEnd_426665 := by
    simpa [prefixWord, tailWord_426665, baseEnd_426665] using wordTrace_append hprefix tailTrace_426665
  have hstable : (prefixWord ++ tailWord_426665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426665).length < 2 ^ (prefixWord ++ tailWord_426665).sum := by decide
  have hdescent : baseEnd_426665 < baseStart_426665 := by decide
  rcases family_descends (prefixWord ++ tailWord_426665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426666 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 1, 7]
def baseStart_426666 : Nat := 118140960795 + 426666 * 2 ^ 59
def prefixEnd_426666 : Nat := 4983230072969 + 3 ^ 40 * 426666 * 2
def baseEnd_426666 : Nat := 73028245643777633670935

theorem tailTrace_426666 : CollatzResearch.WordTrace tailWord_426666 prefixEnd_426666 73028245643777633670935 := by
  unfold tailWord_426666
  simp only [CollatzResearch.WordTrace]
  refine ⟨3890446868067356399132963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10374524981512950397687901 3890446868067356399132963)
  ·
    refine ⟨5835670302101034598699445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3890446868067356399132963 5835670302101034598699445)
    ·
      refine ⟨547094090821971993628073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5835670302101034598699445 547094090821971993628073)
      ·
        refine ⟨410320568116478995221055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 547094090821971993628073 410320568116478995221055)
        ·
          refine ⟨615480852174718492831583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410320568116478995221055 615480852174718492831583)
          ·
            refine ⟨923221278262077739247375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615480852174718492831583 923221278262077739247375)
            ·
              refine ⟨1384831917393116608871063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 923221278262077739247375 1384831917393116608871063)
              ·
                refine ⟨2077247876089674913306595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1384831917393116608871063 2077247876089674913306595)
                ·
                  refine ⟨3115871814134512369959893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2077247876089674913306595 3115871814134512369959893)
                  ·
                    refine ⟨73028245643777633670935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3115871814134512369959893 73028245643777633670935)
                    ·
                      rfl

theorem cell23_426666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_426666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426666 prefixEnd_426666 := by exact prefixLift 426666
  have htrace : WordTrace (prefixWord ++ tailWord_426666) baseStart_426666 baseEnd_426666 := by
    simpa [prefixWord, tailWord_426666, baseEnd_426666] using wordTrace_append hprefix tailTrace_426666
  have hstable : (prefixWord ++ tailWord_426666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426666).length < 2 ^ (prefixWord ++ tailWord_426666).sum := by decide
  have hdescent : baseEnd_426666 < baseStart_426666 := by decide
  rcases family_descends (prefixWord ++ tailWord_426666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426669 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_426669 : Nat := 118140960795 + 426669 * 2 ^ 59
def prefixEnd_426669 : Nat := 4983230072969 + 3 ^ 40 * 426669 * 2
def baseEnd_426669 : Nat := 219086277373296389275291

theorem tailTrace_426669 : CollatzResearch.WordTrace tailWord_426669 prefixEnd_426669 219086277373296389275291 := by
  unfold tailWord_426669
  simp only [CollatzResearch.WordTrace]
  refine ⟨15561896891258557108891061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10374597927505704739260707 15561896891258557108891061)
  ·
    refine ⟨1458927833555489728958537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15561896891258557108891061 1458927833555489728958537)
    ·
      refine ⟨1094195875166617296718903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1458927833555489728958537 1094195875166617296718903)
      ·
        refine ⟨1641293812749925945078355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1094195875166617296718903 1641293812749925945078355)
        ·
          refine ⟨2461940719124888917617533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1641293812749925945078355 2461940719124888917617533)
          ·
            refine ⟨923227769671833344106575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2461940719124888917617533 923227769671833344106575)
            ·
              refine ⟨1384841654507750016159863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 923227769671833344106575 1384841654507750016159863)
              ·
                refine ⟨2077262481761625024239795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1384841654507750016159863 2077262481761625024239795)
                ·
                  refine ⟨3115893722642437536359693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2077262481761625024239795 3115893722642437536359693)
                  ·
                    refine ⟨1168460145990914076134885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3115893722642437536359693 1168460145990914076134885)
                    ·
                      refine ⟨219086277373296389275291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1168460145990914076134885 219086277373296389275291)
                      ·
                        rfl

theorem cell23_426669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_426669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426669 prefixEnd_426669 := by exact prefixLift 426669
  have htrace : WordTrace (prefixWord ++ tailWord_426669) baseStart_426669 baseEnd_426669 := by
    simpa [prefixWord, tailWord_426669, baseEnd_426669] using wordTrace_append hprefix tailTrace_426669
  have hstable : (prefixWord ++ tailWord_426669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426669).length < 2 ^ (prefixWord ++ tailWord_426669).sum := by decide
  have hdescent : baseEnd_426669 < baseStart_426669 := by decide
  rcases family_descends (prefixWord ++ tailWord_426669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426696 : List Nat := [2, 1, 3, 1, 2, 3, 2, 4, 1, 4]
def baseStart_426696 : Nat := 118140960795 + 426696 * 2 ^ 59
def prefixEnd_426696 : Nat := 4983230072969 + 3 ^ 40 * 426696 * 2
def baseEnd_426696 : Nat := 73033380450322594545889

theorem tailTrace_426696 : CollatzResearch.WordTrace tailWord_426696 prefixEnd_426696 73033380450322594545889 := by
  unfold tailWord_426696
  simp only [CollatzResearch.WordTrace]
  refine ⟨7781440831080370360061971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10375254441440493813415961 7781440831080370360061971)
  ·
    refine ⟨11672161246620555540092957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7781440831080370360061971 11672161246620555540092957)
    ·
      refine ⟨4377060467482708327534859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11672161246620555540092957 4377060467482708327534859)
      ·
        refine ⟨6565590701224062491302289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4377060467482708327534859 6565590701224062491302289)
        ·
          refine ⟨4924193025918046868476717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6565590701224062491302289 4924193025918046868476717)
          ·
            refine ⟨1846572384719267575678769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4924193025918046868476717 1846572384719267575678769)
            ·
              refine ⟨1384929288539450681759077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1846572384719267575678769 1384929288539450681759077)
              ·
                refine ⟨259674241601147002829827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1384929288539450681759077 259674241601147002829827)
                ·
                  refine ⟨389511362401720504244741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259674241601147002829827 389511362401720504244741)
                  ·
                    refine ⟨73033380450322594545889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 389511362401720504244741 73033380450322594545889)
                    ·
                      rfl

theorem cell23_426696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_426696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426696 prefixEnd_426696 := by exact prefixLift 426696
  have htrace : WordTrace (prefixWord ++ tailWord_426696) baseStart_426696 baseEnd_426696 := by
    simpa [prefixWord, tailWord_426696, baseEnd_426696] using wordTrace_append hprefix tailTrace_426696
  have hstable : (prefixWord ++ tailWord_426696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426696).length < 2 ^ (prefixWord ++ tailWord_426696).sum := by decide
  have hdescent : baseEnd_426696 < baseStart_426696 := by decide
  rcases family_descends (prefixWord ++ tailWord_426696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426729 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 1, 5, 2]
def baseStart_426729 : Nat := 118140960795 + 426729 * 2 ^ 59
def prefixEnd_426729 : Nat := 4983230072969 + 3 ^ 40 * 426729 * 2
def baseEnd_426729 : Nat := 219117086212566154525015

theorem tailTrace_426729 : CollatzResearch.WordTrace tailWord_426729 prefixEnd_426729 219117086212566154525015 := by
  unfold tailWord_426729
  simp only [CollatzResearch.WordTrace]
  refine ⟨15564085271041187356075241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10376056847360791570716827 15564085271041187356075241)
  ·
    refine ⟨11673063953280890517056431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15564085271041187356075241 11673063953280890517056431)
    ·
      refine ⟨17509595929921335775584647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11673063953280890517056431 17509595929921335775584647)
      ·
        refine ⟨26264393894882003663376971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17509595929921335775584647 26264393894882003663376971)
        ·
          refine ⟨39396590842323005495065457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26264393894882003663376971 39396590842323005495065457)
          ·
            refine ⟨29547443131742254121299093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39396590842323005495065457 29547443131742254121299093)
            ·
              refine ⟨1385036396800418161935895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29547443131742254121299093 1385036396800418161935895)
              ·
                refine ⟨2077554595200627242903843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1385036396800418161935895 2077554595200627242903843)
                ·
                  refine ⟨3116331892800940864355765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2077554595200627242903843 3116331892800940864355765)
                  ·
                    refine ⟨292156114950088206033353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3116331892800940864355765 292156114950088206033353)
                    ·
                      refine ⟨219117086212566154525015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 292156114950088206033353 219117086212566154525015)
                      ·
                        rfl

theorem cell23_426729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 5, 2].length) (baseStart_426729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426729 prefixEnd_426729 := by exact prefixLift 426729
  have htrace : WordTrace (prefixWord ++ tailWord_426729) baseStart_426729 baseEnd_426729 := by
    simpa [prefixWord, tailWord_426729, baseEnd_426729] using wordTrace_append hprefix tailTrace_426729
  have hstable : (prefixWord ++ tailWord_426729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426729).length < 2 ^ (prefixWord ++ tailWord_426729).sum := by decide
  have hdescent : baseEnd_426729 < baseStart_426729 := by decide
  rcases family_descends (prefixWord ++ tailWord_426729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426740 : List Nat := [2, 6, 1, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_426740 : Nat := 118140960795 + 426740 * 2 ^ 59
def prefixEnd_426740 : Nat := 4983230072969 + 3 ^ 40 * 426740 * 2
def baseEnd_426740 : Nat := 219122734499765611487465

theorem tailTrace_426740 : CollatzResearch.WordTrace tailWord_426740 prefixEnd_426740 219122734499765611487465 := by
  unfold tailWord_426740
  simp only [CollatzResearch.WordTrace]
  refine ⟨7782243237000668117362837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10376324316000890823150449 7782243237000668117362837)
  ·
    refine ⟨364792651734406318001383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7782243237000668117362837 364792651734406318001383)
    ·
      refine ⟨547188977601609477002075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364792651734406318001383 547188977601609477002075)
      ·
        refine ⟨820783466402414215503113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547188977601609477002075 820783466402414215503113)
        ·
          refine ⟨615587599801810661627335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 820783466402414215503113 615587599801810661627335)
          ·
            refine ⟨923381399702715992441003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615587599801810661627335 923381399702715992441003)
            ·
              refine ⟨1385072099554073988661505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 923381399702715992441003 1385072099554073988661505)
              ·
                refine ⟨1038804074665555491496129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1385072099554073988661505 1038804074665555491496129)
                ·
                  refine ⟨779103055999166618622097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1038804074665555491496129 779103055999166618622097)
                  ·
                    refine ⟨584327291999374963966573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 779103055999166618622097 584327291999374963966573)
                    ·
                      refine ⟨219122734499765611487465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 584327291999374963966573 219122734499765611487465)
                      ·
                        rfl

theorem cell23_426740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_426740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426740 prefixEnd_426740 := by exact prefixLift 426740
  have htrace : WordTrace (prefixWord ++ tailWord_426740) baseStart_426740 baseEnd_426740 := by
    simpa [prefixWord, tailWord_426740, baseEnd_426740] using wordTrace_append hprefix tailTrace_426740
  have hstable : (prefixWord ++ tailWord_426740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426740).length < 2 ^ (prefixWord ++ tailWord_426740).sum := by decide
  have hdescent : baseEnd_426740 < baseStart_426740 := by decide
  rcases family_descends (prefixWord ++ tailWord_426740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426776 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 5, 2, 2]
def baseStart_426776 : Nat := 118140960795 + 426776 * 2 ^ 59
def prefixEnd_426776 : Nat := 4983230072969 + 3 ^ 40 * 426776 * 2
def baseEnd_426776 : Nat := 219141219803327470637299

theorem tailTrace_426776 : CollatzResearch.WordTrace tailWord_426776 prefixEnd_426776 219141219803327470637299 := by
  unfold tailWord_426776
  simp only [CollatzResearch.WordTrace]
  refine ⟨7782899750935457191518091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10377199667913942922024121 7782899750935457191518091)
  ·
    refine ⟨11674349626403185787277137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7782899750935457191518091 11674349626403185787277137)
    ·
      refine ⟨8755762219802389340457853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11674349626403185787277137 8755762219802389340457853)
      ·
        refine ⟨3283410832425896002671695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8755762219802389340457853 3283410832425896002671695)
        ·
          refine ⟨4925116248638844004007543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3283410832425896002671695 4925116248638844004007543)
          ·
            refine ⟨7387674372958266006011315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4925116248638844004007543 7387674372958266006011315)
            ·
              refine ⟨11081511559437399009016973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7387674372958266006011315 11081511559437399009016973)
              ·
                refine ⟨4155566834789024628381365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11081511559437399009016973 4155566834789024628381365)
                ·
                  refine ⟨389584390761471058910753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4155566834789024628381365 389584390761471058910753)
                  ·
                    refine ⟨292188293071103294183065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 389584390761471058910753 292188293071103294183065)
                    ·
                      refine ⟨219141219803327470637299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 292188293071103294183065 219141219803327470637299)
                      ·
                        rfl

theorem cell23_426776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_426776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426776 prefixEnd_426776 := by exact prefixLift 426776
  have htrace : WordTrace (prefixWord ++ tailWord_426776) baseStart_426776 baseEnd_426776 := by
    simpa [prefixWord, tailWord_426776, baseEnd_426776] using wordTrace_append hprefix tailTrace_426776
  have hstable : (prefixWord ++ tailWord_426776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426776).length < 2 ^ (prefixWord ++ tailWord_426776).sum := by decide
  have hdescent : baseEnd_426776 < baseStart_426776 := by decide
  rcases family_descends (prefixWord ++ tailWord_426776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426789 : List Nat := [1, 3, 1, 2, 3, 1, 3, 2, 1, 2, 4]
def baseStart_426789 : Nat := 118140960795 + 426789 * 2 ^ 59
def prefixEnd_426789 : Nat := 4983230072969 + 3 ^ 40 * 426789 * 2
def baseEnd_426789 : Nat := 219147895051835919774739

theorem tailTrace_426789 : CollatzResearch.WordTrace tailWord_426789 prefixEnd_426789 219147895051835919774739 := by
  unfold tailWord_426789
  simp only [CollatzResearch.WordTrace]
  refine ⟨15566273650823817603259421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10377515767215878402172947 15566273650823817603259421)
  ·
    refine ⟨5837352619058931601222283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15566273650823817603259421 5837352619058931601222283)
    ·
      refine ⟨8756028928588397401833425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5837352619058931601222283 8756028928588397401833425)
      ·
        refine ⟨6567021696441298051375069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8756028928588397401833425 6567021696441298051375069)
        ·
          refine ⟨2462633136165486769265651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6567021696441298051375069 2462633136165486769265651)
          ·
            refine ⟨3693949704248230153898477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2462633136165486769265651 3693949704248230153898477)
            ·
              refine ⟨1385231139093086307711929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3693949704248230153898477 1385231139093086307711929)
              ·
                refine ⟨1038923354319814730783947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1385231139093086307711929 1038923354319814730783947)
                ·
                  refine ⟨1558385031479722096175921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1038923354319814730783947 1558385031479722096175921)
                  ·
                    refine ⟨1168788773609791572131941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1558385031479722096175921 1168788773609791572131941)
                    ·
                      refine ⟨219147895051835919774739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1168788773609791572131941 219147895051835919774739)
                      ·
                        rfl

theorem cell23_426789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_426789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426789 prefixEnd_426789 := by exact prefixLift 426789
  have htrace : WordTrace (prefixWord ++ tailWord_426789) baseStart_426789 baseEnd_426789 := by
    simpa [prefixWord, tailWord_426789, baseEnd_426789] using wordTrace_append hprefix tailTrace_426789
  have hstable : (prefixWord ++ tailWord_426789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426789).length < 2 ^ (prefixWord ++ tailWord_426789).sum := by decide
  have hdescent : baseEnd_426789 < baseStart_426789 := by decide
  rcases family_descends (prefixWord ++ tailWord_426789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426804 : List Nat := [2, 5, 1, 1, 3, 2, 2, 2, 1, 1, 3]
def baseStart_426804 : Nat := 118140960795 + 426804 * 2 ^ 59
def prefixEnd_426804 : Nat := 4983230072969 + 3 ^ 40 * 426804 * 2
def baseEnd_426804 : Nat := 219155597261653361087171

theorem tailTrace_426804 : CollatzResearch.WordTrace tailWord_426804 prefixEnd_426804 219155597261653361087171 := by
  unfold tailWord_426804
  simp only [CollatzResearch.WordTrace]
  refine ⟨7783410372884737582527733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10377880497179650110036977 7783410372884737582527733)
  ·
    refine ⟨729694722457944148361975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7783410372884737582527733 729694722457944148361975)
    ·
      refine ⟨1094542083686916222542963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 729694722457944148361975 1094542083686916222542963)
      ·
        refine ⟨1641813125530374333814445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1094542083686916222542963 1641813125530374333814445)
        ·
          refine ⟨615679922073890375180417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1641813125530374333814445 615679922073890375180417)
          ·
            refine ⟨461759941555417781385313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 615679922073890375180417 461759941555417781385313)
            ·
              refine ⟨346319956166563336038985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461759941555417781385313 346319956166563336038985)
              ·
                refine ⟨259739967124922502029239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 346319956166563336038985 259739967124922502029239)
                ·
                  refine ⟨389609950687383753043859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259739967124922502029239 389609950687383753043859)
                  ·
                    refine ⟨584414926031075629565789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 389609950687383753043859 584414926031075629565789)
                    ·
                      refine ⟨219155597261653361087171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 584414926031075629565789 219155597261653361087171)
                      ·
                        rfl

theorem cell23_426804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_426804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426804 prefixEnd_426804 := by exact prefixLift 426804
  have htrace : WordTrace (prefixWord ++ tailWord_426804) baseStart_426804 baseEnd_426804 := by
    simpa [prefixWord, tailWord_426804, baseEnd_426804] using wordTrace_append hprefix tailTrace_426804
  have hstable : (prefixWord ++ tailWord_426804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426804).length < 2 ^ (prefixWord ++ tailWord_426804).sum := by decide
  have hdescent : baseEnd_426804 < baseStart_426804 := by decide
  rcases family_descends (prefixWord ++ tailWord_426804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426866 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 3, 4, 2]
def baseStart_426866 : Nat := 118140960795 + 426866 * 2 ^ 59
def prefixEnd_426866 : Nat := 4983230072969 + 3 ^ 40 * 426866 * 2
def baseEnd_426866 : Nat := 219187433062232118511885

theorem tailTrace_426866 : CollatzResearch.WordTrace tailWord_426866 prefixEnd_426866 219187433062232118511885 := by
  unfold tailWord_426866
  simp only [CollatzResearch.WordTrace]
  refine ⟨3892270517886214938453113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10379388047696573169208301 3892270517886214938453113)
  ·
    refine ⟨2919202888414661203839835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3892270517886214938453113 2919202888414661203839835)
    ·
      refine ⟨4378804332621991805759753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2919202888414661203839835 4378804332621991805759753)
      ·
        refine ⟨3284103249466493854319815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4378804332621991805759753 3284103249466493854319815)
        ·
          refine ⟨4926154874199740781479723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3284103249466493854319815 4926154874199740781479723)
          ·
            refine ⟨7389232311299611172219585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4926154874199740781479723 7389232311299611172219585)
            ·
              refine ⟨5541924233474708379164689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7389232311299611172219585 5541924233474708379164689)
              ·
                refine ⟨4156443175106031284373517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5541924233474708379164689 4156443175106031284373517)
                ·
                  refine ⟨1558666190664761731640069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4156443175106031284373517 1558666190664761731640069)
                  ·
                    refine ⟨292249910749642824682513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1558666190664761731640069 292249910749642824682513)
                    ·
                      refine ⟨219187433062232118511885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 292249910749642824682513 219187433062232118511885)
                      ·
                        rfl

theorem cell23_426866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_426866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426866 prefixEnd_426866 := by exact prefixLift 426866
  have htrace : WordTrace (prefixWord ++ tailWord_426866) baseStart_426866 baseEnd_426866 := by
    simpa [prefixWord, tailWord_426866, baseEnd_426866] using wordTrace_append hprefix tailTrace_426866
  have hstable : (prefixWord ++ tailWord_426866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426866).length < 2 ^ (prefixWord ++ tailWord_426866).sum := by decide
  have hdescent : baseEnd_426866 < baseStart_426866 := by decide
  rcases family_descends (prefixWord ++ tailWord_426866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426879 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 4]
def baseStart_426879 : Nat := 118140960795 + 426879 * 2 ^ 59
def prefixEnd_426879 : Nat := 4983230072969 + 3 ^ 40 * 426879 * 2
def baseEnd_426879 : Nat := 219194108310740567649325

theorem tailTrace_426879 : CollatzResearch.WordTrace tailWord_426879 prefixEnd_426879 219194108310740567649325 := by
  unfold tailWord_426879
  simp only [CollatzResearch.WordTrace]
  refine ⟨15569556220497762974035691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10379704146998508649357127 15569556220497762974035691)
  ·
    refine ⟨23354334330746644461053537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15569556220497762974035691 23354334330746644461053537)
    ·
      refine ⟨17515750748059983345790153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23354334330746644461053537 17515750748059983345790153)
      ·
        refine ⟨13136813061044987509342615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17515750748059983345790153 13136813061044987509342615)
        ·
          refine ⟨19705219591567481264013923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13136813061044987509342615 19705219591567481264013923)
          ·
            refine ⟨29557829387351221896020885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19705219591567481264013923 29557829387351221896020885)
            ·
              refine ⟨1385523252532088526375979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29557829387351221896020885 1385523252532088526375979)
              ·
                refine ⟨2078284878798132789563969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1385523252532088526375979 2078284878798132789563969)
                ·
                  refine ⟨1558713659098599592172977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2078284878798132789563969 1558713659098599592172977)
                  ·
                    refine ⟨1169035244323949694129733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1558713659098599592172977 1169035244323949694129733)
                    ·
                      refine ⟨219194108310740567649325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1169035244323949694129733 219194108310740567649325)
                      ·
                        rfl

theorem cell23_426879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_426879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426879 prefixEnd_426879 := by exact prefixLift 426879
  have htrace : WordTrace (prefixWord ++ tailWord_426879) baseStart_426879 baseEnd_426879 := by
    simpa [prefixWord, tailWord_426879, baseEnd_426879] using wordTrace_append hprefix tailTrace_426879
  have hstable : (prefixWord ++ tailWord_426879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426879).length < 2 ^ (prefixWord ++ tailWord_426879).sum := by decide
  have hdescent : baseEnd_426879 < baseStart_426879 := by decide
  rcases family_descends (prefixWord ++ tailWord_426879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426889 : List Nat := [1, 2, 1, 1, 5, 2, 2, 2, 7]
def baseStart_426889 : Nat := 118140960795 + 426889 * 2 ^ 59
def prefixEnd_426889 : Nat := 4983230072969 + 3 ^ 40 * 426889 * 2
def baseEnd_426889 : Nat := 24355471457476169836031

theorem tailTrace_426889 : CollatzResearch.WordTrace tailWord_426889 prefixEnd_426889 24355471457476169836031 := by
  unfold tailWord_426889
  simp only [CollatzResearch.WordTrace]
  refine ⟨15569920950461534681899721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10379947300307689787933147 15569920950461534681899721)
  ·
    refine ⟨11677440712846151011424791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15569920950461534681899721 11677440712846151011424791)
    ·
      refine ⟨17516161069269226517137187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11677440712846151011424791 17516161069269226517137187)
      ·
        refine ⟨26274241603903839775705781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17516161069269226517137187 26274241603903839775705781)
        ·
          refine ⟨2463210150365984978972417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26274241603903839775705781 2463210150365984978972417)
          ·
            refine ⟨1847407612774488734229313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2463210150365984978972417 1847407612774488734229313)
            ·
              refine ⟨1385555709580866550671985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1847407612774488734229313 1385555709580866550671985)
              ·
                refine ⟨1039166782185649913003989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1385555709580866550671985 1039166782185649913003989)
                ·
                  refine ⟨24355471457476169836031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1039166782185649913003989 24355471457476169836031)
                  ·
                    rfl

theorem cell23_426889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 7].length) (baseStart_426889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426889 prefixEnd_426889 := by exact prefixLift 426889
  have htrace : WordTrace (prefixWord ++ tailWord_426889) baseStart_426889 baseEnd_426889 := by
    simpa [prefixWord, tailWord_426889, baseEnd_426889] using wordTrace_append hprefix tailTrace_426889
  have hstable : (prefixWord ++ tailWord_426889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426889).length < 2 ^ (prefixWord ++ tailWord_426889).sum := by decide
  have hdescent : baseEnd_426889 < baseStart_426889 := by decide
  rcases family_descends (prefixWord ++ tailWord_426889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426899 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 3]
def baseStart_426899 : Nat := 118140960795 + 426899 * 2 ^ 59
def prefixEnd_426899 : Nat := 4983230072969 + 3 ^ 40 * 426899 * 2
def baseEnd_426899 : Nat := 219204377923830489399233

theorem tailTrace_426899 : CollatzResearch.WordTrace tailWord_426899 prefixEnd_426899 219204377923830489399233 := by
  unfold tailWord_426899
  simp only [CollatzResearch.WordTrace]
  refine ⟨15570285680425306389763751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10380190453616870926509167 15570285680425306389763751)
  ·
    refine ⟨23355428520637959584645627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15570285680425306389763751 23355428520637959584645627)
    ·
      refine ⟨35033142780956939376968441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23355428520637959584645627 35033142780956939376968441)
      ·
        refine ⟨26274857085717704532726331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35033142780956939376968441 26274857085717704532726331)
        ·
          refine ⟨39412285628576556799089497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26274857085717704532726331 39412285628576556799089497)
          ·
            refine ⟨29559214221432417599317123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39412285628576556799089497 29559214221432417599317123)
            ·
              refine ⟨44338821332148626398975685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29559214221432417599317123 44338821332148626398975685)
              ·
                refine ⟨8313528999777867449807941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44338821332148626398975685 8313528999777867449807941)
                ·
                  refine ⟨1558786687458350146838989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8313528999777867449807941 1558786687458350146838989)
                  ·
                    refine ⟨584545007796881305064621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1558786687458350146838989 584545007796881305064621)
                    ·
                      refine ⟨219204377923830489399233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 584545007796881305064621 219204377923830489399233)
                      ·
                        rfl

theorem cell23_426899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 3].length) (baseStart_426899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426899 prefixEnd_426899 := by exact prefixLift 426899
  have htrace : WordTrace (prefixWord ++ tailWord_426899) baseStart_426899 baseEnd_426899 := by
    simpa [prefixWord, tailWord_426899, baseEnd_426899] using wordTrace_append hprefix tailTrace_426899
  have hstable : (prefixWord ++ tailWord_426899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426899).length < 2 ^ (prefixWord ++ tailWord_426899).sum := by decide
  have hdescent : baseEnd_426899 < baseStart_426899 := by decide
  rcases family_descends (prefixWord ++ tailWord_426899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426973 : List Nat := [1, 4, 3, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_426973 : Nat := 118140960795 + 426973 * 2 ^ 59
def prefixEnd_426973 : Nat := 4983230072969 + 3 ^ 40 * 426973 * 2
def baseEnd_426973 : Nat := 219242375492263199873893

theorem tailTrace_426973 : CollatzResearch.WordTrace tailWord_426973 prefixEnd_426973 219242375492263199873893 := by
  unfold tailWord_426973
  simp only [CollatzResearch.WordTrace]
  refine ⟨15572984682157217027957573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10381989788104811351971715 15572984682157217027957573)
  ·
    refine ⟨2919934627904478192742045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15572984682157217027957573 2919934627904478192742045)
    ·
      refine ⟨1094975485464179322278267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2919934627904478192742045 1094975485464179322278267)
      ·
        refine ⟨1642463228196268983417401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1094975485464179322278267 1642463228196268983417401)
        ·
          refine ⟨1231847421147201737563051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1642463228196268983417401 1231847421147201737563051)
          ·
            refine ⟨1847771131720802606344577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1231847421147201737563051 1847771131720802606344577)
            ·
              refine ⟨1385828348790601954758433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1847771131720802606344577 1385828348790601954758433)
              ·
                refine ⟨1039371261592951466068825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1385828348790601954758433 1039371261592951466068825)
                ·
                  refine ⟨779528446194713599551619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1039371261592951466068825 779528446194713599551619)
                  ·
                    refine ⟨1169292669292070399327429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 779528446194713599551619 1169292669292070399327429)
                    ·
                      refine ⟨219242375492263199873893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1169292669292070399327429 219242375492263199873893)
                      ·
                        rfl

theorem cell23_426973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_426973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426973 prefixEnd_426973 := by exact prefixLift 426973
  have htrace : WordTrace (prefixWord ++ tailWord_426973) baseStart_426973 baseEnd_426973 := by
    simpa [prefixWord, tailWord_426973, baseEnd_426973] using wordTrace_append hprefix tailTrace_426973
  have hstable : (prefixWord ++ tailWord_426973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426973).length < 2 ^ (prefixWord ++ tailWord_426973).sum := by decide
  have hdescent : baseEnd_426973 < baseStart_426973 := by decide
  rcases family_descends (prefixWord ++ tailWord_426973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426990 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 2, 4, 2]
def baseStart_426990 : Nat := 118140960795 + 426990 * 2 ^ 59
def prefixEnd_426990 : Nat := 4983230072969 + 3 ^ 40 * 426990 * 2
def baseEnd_426990 : Nat := 219251104663389633361315

theorem tailTrace_426990 : CollatzResearch.WordTrace tailWord_426990 prefixEnd_426990 219251104663389633361315 := by
  unfold tailWord_426990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1946700590386953616415803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10382403148730419287550949 1946700590386953616415803)
  ·
    refine ⟨2920050885580430424623705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1946700590386953616415803 2920050885580430424623705)
    ·
      refine ⟨2190038164185322818467779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2920050885580430424623705 2190038164185322818467779)
      ·
        refine ⟨3285057246277984227701669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2190038164185322818467779 3285057246277984227701669)
        ·
          refine ⟨615948233677122042694063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3285057246277984227701669 615948233677122042694063)
          ·
            refine ⟨923922350515683064041095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615948233677122042694063 923922350515683064041095)
            ·
              refine ⟨1385883525773524596061643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 923922350515683064041095 1385883525773524596061643)
              ·
                refine ⟨2078825288660286894092465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1385883525773524596061643 2078825288660286894092465)
                ·
                  refine ⟨1559118966495215170569349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2078825288660286894092465 1559118966495215170569349)
                  ·
                    refine ⟨292334806217852844481753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1559118966495215170569349 292334806217852844481753)
                    ·
                      refine ⟨219251104663389633361315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 292334806217852844481753 219251104663389633361315)
                      ·
                        rfl

theorem cell23_426990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_426990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_426990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_426990 prefixEnd_426990 := by exact prefixLift 426990
  have htrace : WordTrace (prefixWord ++ tailWord_426990) baseStart_426990 baseEnd_426990 := by
    simpa [prefixWord, tailWord_426990, baseEnd_426990] using wordTrace_append hprefix tailTrace_426990
  have hstable : (prefixWord ++ tailWord_426990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426990).length < 2 ^ (prefixWord ++ tailWord_426990).sum := by decide
  have hdescent : baseEnd_426990 < baseStart_426990 := by decide
  rcases family_descends (prefixWord ++ tailWord_426990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427033 : List Nat := [1, 2, 1, 2, 1, 1, 4, 4, 2, 3, 2]
def baseStart_427033 : Nat := 118140960795 + 427033 * 2 ^ 59
def prefixEnd_427033 : Nat := 4983230072969 + 3 ^ 40 * 427033 * 2
def baseEnd_427033 : Nat := 219273184331532965123617

theorem tailTrace_427033 : CollatzResearch.WordTrace tailWord_427033 prefixEnd_427033 219273184331532965123617 := by
  unfold tailWord_427033
  simp only [CollatzResearch.WordTrace]
  refine ⟨15575173061939847275141753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10383448707959898183427835 15575173061939847275141753)
  ·
    refine ⟨11681379796454885456356315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15575173061939847275141753 11681379796454885456356315)
    ·
      refine ⟨17522069694682328184534473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11681379796454885456356315 17522069694682328184534473)
      ·
        refine ⟨13141552271011746138400855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17522069694682328184534473 13141552271011746138400855)
        ·
          refine ⟨19712328406517619207601283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13141552271011746138400855 19712328406517619207601283)
          ·
            refine ⟨29568492609776428811401925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19712328406517619207601283 29568492609776428811401925)
            ·
              refine ⟨5544092364333080402137861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29568492609776428811401925 5544092364333080402137861)
              ·
                refine ⟨1039517318312452575400849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5544092364333080402137861 1039517318312452575400849)
                ·
                  refine ⟨779637988734339431550637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1039517318312452575400849 779637988734339431550637)
                  ·
                    refine ⟨292364245775377286831489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 779637988734339431550637 292364245775377286831489)
                    ·
                      refine ⟨219273184331532965123617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 292364245775377286831489 219273184331532965123617)
                      ·
                        rfl

theorem cell23_427033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 3, 2].length) (baseStart_427033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427033 prefixEnd_427033 := by exact prefixLift 427033
  have htrace : WordTrace (prefixWord ++ tailWord_427033) baseStart_427033 baseEnd_427033 := by
    simpa [prefixWord, tailWord_427033, baseEnd_427033] using wordTrace_append hprefix tailTrace_427033
  have hstable : (prefixWord ++ tailWord_427033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427033).length < 2 ^ (prefixWord ++ tailWord_427033).sum := by decide
  have hdescent : baseEnd_427033 < baseStart_427033 := by decide
  rcases family_descends (prefixWord ++ tailWord_427033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427060 : List Nat := [2, 5, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_427060 : Nat := 118140960795 + 427060 * 2 ^ 59
def prefixEnd_427060 : Nat := 4983230072969 + 3 ^ 40 * 427060 * 2
def baseEnd_427060 : Nat := 73095682769734786495331

theorem tailTrace_427060 : CollatzResearch.WordTrace tailWord_427060 prefixEnd_427060 73095682769734786495331 := by
  unfold tailWord_427060
  simp only [CollatzResearch.WordTrace]
  refine ⟨7788078916421015443187317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10384105221894687257583089 7788078916421015443187317)
  ·
    refine ⟨730132398414470197798811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7788078916421015443187317 730132398414470197798811)
    ·
      refine ⟨1095198597621705296698217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 730132398414470197798811 1095198597621705296698217)
      ·
        refine ⟨821398948216278972523663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1095198597621705296698217 821398948216278972523663)
        ·
          refine ⟨1232098422324418458785495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 821398948216278972523663 1232098422324418458785495)
          ·
            refine ⟨1848147633486627688178243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232098422324418458785495 1848147633486627688178243)
            ·
              refine ⟨2772221450229941532267365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1848147633486627688178243 2772221450229941532267365)
              ·
                refine ⟨519791521918114037300131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2772221450229941532267365 519791521918114037300131)
                ·
                  refine ⟨779687282877171055950197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 519791521918114037300131 779687282877171055950197)
                  ·
                    refine ⟨73095682769734786495331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 779687282877171055950197 73095682769734786495331)
                    ·
                      rfl

theorem cell23_427060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_427060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427060 prefixEnd_427060 := by exact prefixLift 427060
  have htrace : WordTrace (prefixWord ++ tailWord_427060) baseStart_427060 baseEnd_427060 := by
    simpa [prefixWord, tailWord_427060, baseEnd_427060] using wordTrace_append hprefix tailTrace_427060
  have hstable : (prefixWord ++ tailWord_427060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427060).length < 2 ^ (prefixWord ++ tailWord_427060).sum := by decide
  have hdescent : baseEnd_427060 < baseStart_427060 := by decide
  rcases family_descends (prefixWord ++ tailWord_427060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427117 : List Nat := [1, 5, 1, 1, 2, 4, 1, 2, 1, 2, 3]
def baseStart_427117 : Nat := 118140960795 + 427117 * 2 ^ 59
def prefixEnd_427117 : Nat := 4983230072969 + 3 ^ 40 * 427117 * 2
def baseEnd_427117 : Nat := 219316316706510636473231

theorem tailTrace_427117 : CollatzResearch.WordTrace tailWord_427117 prefixEnd_427117 219316316706510636473231 := by
  unfold tailWord_427117
  simp only [CollatzResearch.WordTrace]
  refine ⟨15578236793635529621199605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10385491195757019747466403 15578236793635529621199605)
  ·
    refine ⟨1460459699403330901987463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15578236793635529621199605 1460459699403330901987463)
    ·
      refine ⟨2190689549104996352981195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1460459699403330901987463 2190689549104996352981195)
      ·
        refine ⟨3286034323657494529471793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2190689549104996352981195 3286034323657494529471793)
        ·
          refine ⟨2464525742743120897103845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3286034323657494529471793 2464525742743120897103845)
          ·
            refine ⟨462098576764335168206971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2464525742743120897103845 462098576764335168206971)
            ·
              refine ⟨693147865146502752310457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462098576764335168206971 693147865146502752310457)
              ·
                refine ⟨519860898859877064232843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 693147865146502752310457 519860898859877064232843)
                ·
                  refine ⟨779791348289815596349265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 519860898859877064232843 779791348289815596349265)
                  ·
                    refine ⟨584843511217361697261949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 779791348289815596349265 584843511217361697261949)
                    ·
                      refine ⟨219316316706510636473231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 584843511217361697261949 219316316706510636473231)
                      ·
                        rfl

theorem cell23_427117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_427117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427117 prefixEnd_427117 := by exact prefixLift 427117
  have htrace : WordTrace (prefixWord ++ tailWord_427117) baseStart_427117 baseEnd_427117 := by
    simpa [prefixWord, tailWord_427117, baseEnd_427117] using wordTrace_append hprefix tailTrace_427117
  have hstable : (prefixWord ++ tailWord_427117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427117).length < 2 ^ (prefixWord ++ tailWord_427117).sum := by decide
  have hdescent : baseEnd_427117 < baseStart_427117 := by decide
  rcases family_descends (prefixWord ++ tailWord_427117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427204 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 4, 2, 2]
def baseStart_427204 : Nat := 118140960795 + 427204 * 2 ^ 59
def prefixEnd_427204 : Nat := 4983230072969 + 3 ^ 40 * 427204 * 2
def baseEnd_427204 : Nat := 219360989523451796085331

theorem tailTrace_427204 : CollatzResearch.WordTrace tailWord_427204 prefixEnd_427204 219360989523451796085331 := by
  unfold tailWord_427204
  simp only [CollatzResearch.WordTrace]
  refine ⟨7790704972160171739808333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10387606629546895653077777 7790704972160171739808333)
  ·
    refine ⟨2921514364560064402428125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7790704972160171739808333 2921514364560064402428125)
    ·
      refine ⟨1095567886710024150910547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2921514364560064402428125 1095567886710024150910547)
      ·
        refine ⟨1643351830065036226365821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1095567886710024150910547 1643351830065036226365821)
        ·
          refine ⟨616256936274388584887183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1643351830065036226365821 616256936274388584887183)
          ·
            refine ⟨924385404411582877330775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616256936274388584887183 924385404411582877330775)
            ·
              refine ⟨1386578106617374315996163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 924385404411582877330775 1386578106617374315996163)
              ·
                refine ⟨2079867159926061473994245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386578106617374315996163 2079867159926061473994245)
                ·
                  refine ⟨389975092486136526373921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2079867159926061473994245 389975092486136526373921)
                  ·
                    refine ⟨292481319364602394780441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 389975092486136526373921 292481319364602394780441)
                    ·
                      refine ⟨219360989523451796085331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 292481319364602394780441 219360989523451796085331)
                      ·
                        rfl

theorem cell23_427204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_427204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427204 prefixEnd_427204 := by exact prefixLift 427204
  have htrace : WordTrace (prefixWord ++ tailWord_427204) baseStart_427204 baseEnd_427204 := by
    simpa [prefixWord, tailWord_427204, baseEnd_427204] using wordTrace_append hprefix tailTrace_427204
  have hstable : (prefixWord ++ tailWord_427204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427204).length < 2 ^ (prefixWord ++ tailWord_427204).sum := by decide
  have hdescent : baseEnd_427204 < baseStart_427204 := by decide
  rcases family_descends (prefixWord ++ tailWord_427204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427210 : List Nat := [3, 1, 2, 1, 3, 2, 2, 4, 5]
def baseStart_427210 : Nat := 118140960795 + 427210 * 2 ^ 59
def prefixEnd_427210 : Nat := 4983230072969 + 3 ^ 40 * 427210 * 2
def baseEnd_427210 : Nat := 24373785600819863623367

theorem tailTrace_427210 : CollatzResearch.WordTrace tailWord_427210 prefixEnd_427210 24373785600819863623367 := by
  unfold tailWord_427210
  simp only [CollatzResearch.WordTrace]
  refine ⟨3895407195574651626083771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10387752521532404336223389 3895407195574651626083771)
  ·
    refine ⟨5843110793361977439125657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3895407195574651626083771 5843110793361977439125657)
    ·
      refine ⟨4382333095021483079344243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5843110793361977439125657 4382333095021483079344243)
      ·
        refine ⟨6573499642532224619016365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4382333095021483079344243 6573499642532224619016365)
        ·
          refine ⟨2465062365949584232131137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6573499642532224619016365 2465062365949584232131137)
          ·
            refine ⟨1848796774462188174098353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2465062365949584232131137 1848796774462188174098353)
            ·
              refine ⟨1386597580846641130573765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1848796774462188174098353 1386597580846641130573765)
              ·
                refine ⟨259987046408745211982581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1386597580846641130573765 259987046408745211982581)
                ·
                  refine ⟨24373785600819863623367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 259987046408745211982581 24373785600819863623367)
                  ·
                    rfl

theorem cell23_427210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 5].length) (baseStart_427210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427210 prefixEnd_427210 := by exact prefixLift 427210
  have htrace : WordTrace (prefixWord ++ tailWord_427210) baseStart_427210 baseEnd_427210 := by
    simpa [prefixWord, tailWord_427210, baseEnd_427210] using wordTrace_append hprefix tailTrace_427210
  have hstable : (prefixWord ++ tailWord_427210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427210).length < 2 ^ (prefixWord ++ tailWord_427210).sum := by decide
  have hdescent : baseEnd_427210 < baseStart_427210 := by decide
  rcases family_descends (prefixWord ++ tailWord_427210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427221 : List Nat := [1, 3, 2, 4, 1, 2, 3, 1, 2, 2, 2]
def baseStart_427221 : Nat := 118140960795 + 427221 * 2 ^ 59
def prefixEnd_427221 : Nat := 4983230072969 + 3 ^ 40 * 427221 * 2
def baseEnd_427221 : Nat := 219369718694578229572753

theorem tailTrace_427221 : CollatzResearch.WordTrace tailWord_427221 prefixEnd_427221 219369718694578229572753 := by
  unfold tailWord_427221
  simp only [CollatzResearch.WordTrace]
  refine ⟨15582029985258755382985517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10388019990172503588657011 15582029985258755382985517)
  ·
    refine ⟨5843261244472033268619569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15582029985258755382985517 5843261244472033268619569)
    ·
      refine ⟨4382445933354024951464677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5843261244472033268619569 4382445933354024951464677)
      ·
        refine ⟨821708612503879678399627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4382445933354024951464677 821708612503879678399627)
        ·
          refine ⟨1232562918755819517599441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 821708612503879678399627 1232562918755819517599441)
          ·
            refine ⟨924422189066864638199581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1232562918755819517599441 924422189066864638199581)
            ·
              refine ⟨346658320900074239324843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 924422189066864638199581 346658320900074239324843)
              ·
                refine ⟨519987481350111358987265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346658320900074239324843 519987481350111358987265)
                ·
                  refine ⟨389990611012583519240449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519987481350111358987265 389990611012583519240449)
                  ·
                    refine ⟨292492958259437639430337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 389990611012583519240449 292492958259437639430337)
                    ·
                      refine ⟨219369718694578229572753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 292492958259437639430337 219369718694578229572753)
                      ·
                        rfl

theorem cell23_427221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_427221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427221 prefixEnd_427221 := by exact prefixLift 427221
  have htrace : WordTrace (prefixWord ++ tailWord_427221) baseStart_427221 baseEnd_427221 := by
    simpa [prefixWord, tailWord_427221, baseEnd_427221] using wordTrace_append hprefix tailTrace_427221
  have hstable : (prefixWord ++ tailWord_427221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427221).length < 2 ^ (prefixWord ++ tailWord_427221).sum := by decide
  have hdescent : baseEnd_427221 < baseStart_427221 := by decide
  rcases family_descends (prefixWord ++ tailWord_427221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427243 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 4]
def baseStart_427243 : Nat := 118140960795 + 427243 * 2 ^ 59
def prefixEnd_427243 : Nat := 4983230072969 + 3 ^ 40 * 427243 * 2
def baseEnd_427243 : Nat := 219381015268977143497651

theorem tailTrace_427243 : CollatzResearch.WordTrace tailWord_427243 prefixEnd_427243 219381015268977143497651 := by
  unfold tailWord_427243
  simp only [CollatzResearch.WordTrace]
  refine ⟨15582832391179053140286383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10388554927452702093524255 15582832391179053140286383)
  ·
    refine ⟨23374248586768579710429575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15582832391179053140286383 23374248586768579710429575)
    ·
      refine ⟨35061372880152869565644363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23374248586768579710429575 35061372880152869565644363)
      ·
        refine ⟨52592059320229304348466545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35061372880152869565644363 52592059320229304348466545)
        ·
          refine ⟨39444044490171978261349909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52592059320229304348466545 39444044490171978261349909)
          ·
            refine ⟨1848939585476811481000777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39444044490171978261349909 1848939585476811481000777)
            ·
              refine ⟨1386704689107608610750583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1848939585476811481000777 1386704689107608610750583)
              ·
                refine ⟨2080057033661412916125875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386704689107608610750583 2080057033661412916125875)
                ·
                  refine ⟨3120085550492119374188813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2080057033661412916125875 3120085550492119374188813)
                  ·
                    refine ⟨1170032081434544765320805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3120085550492119374188813 1170032081434544765320805)
                    ·
                      refine ⟨219381015268977143497651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1170032081434544765320805 219381015268977143497651)
                      ·
                        rfl

theorem cell23_427243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 4].length) (baseStart_427243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427243 prefixEnd_427243 := by exact prefixLift 427243
  have htrace : WordTrace (prefixWord ++ tailWord_427243) baseStart_427243 baseEnd_427243 := by
    simpa [prefixWord, tailWord_427243, baseEnd_427243] using wordTrace_append hprefix tailTrace_427243
  have hstable : (prefixWord ++ tailWord_427243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427243).length < 2 ^ (prefixWord ++ tailWord_427243).sum := by decide
  have hdescent : baseEnd_427243 < baseStart_427243 := by decide
  rcases family_descends (prefixWord ++ tailWord_427243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427320 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 3, 5, 2]
def baseStart_427320 : Nat := 118140960795 + 427320 * 2 ^ 59
def prefixEnd_427320 : Nat := 4983230072969 + 3 ^ 40 * 427320 * 2
def baseEnd_427320 : Nat := 219420553279373342234797

theorem tailTrace_427320 : CollatzResearch.WordTrace tailWord_427320 prefixEnd_427320 219420553279373342234797 := by
  unfold tailWord_427320
  simp only [CollatzResearch.WordTrace]
  refine ⟨7792820405950047645419707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10390427207933396860559609 7792820405950047645419707)
  ·
    refine ⟨11689230608925071468129561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7792820405950047645419707 11689230608925071468129561)
    ·
      refine ⟨8766922956693803601097171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11689230608925071468129561 8766922956693803601097171)
      ·
        refine ⟨13150384435040705401645757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8766922956693803601097171 13150384435040705401645757)
        ·
          refine ⟨4931394163140264525617159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13150384435040705401645757 4931394163140264525617159)
          ·
            refine ⟨7397091244710396788425739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4931394163140264525617159 7397091244710396788425739)
            ·
              refine ⟨11095636867065595182638609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7397091244710396788425739 11095636867065595182638609)
              ·
                refine ⟨8321727650299196386978957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11095636867065595182638609 8321727650299196386978957)
                ·
                  refine ⟨3120647868862198645117109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8321727650299196386978957 3120647868862198645117109)
                  ·
                    refine ⟨292560737705831122979729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3120647868862198645117109 292560737705831122979729)
                    ·
                      refine ⟨219420553279373342234797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 292560737705831122979729 219420553279373342234797)
                      ·
                        rfl

theorem cell23_427320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 3, 5, 2].length) (baseStart_427320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427320 prefixEnd_427320 := by exact prefixLift 427320
  have htrace : WordTrace (prefixWord ++ tailWord_427320) baseStart_427320 baseEnd_427320 := by
    simpa [prefixWord, tailWord_427320, baseEnd_427320] using wordTrace_append hprefix tailTrace_427320
  have hstable : (prefixWord ++ tailWord_427320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427320).length < 2 ^ (prefixWord ++ tailWord_427320).sum := by decide
  have hdescent : baseEnd_427320 < baseStart_427320 := by decide
  rcases family_descends (prefixWord ++ tailWord_427320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427360 : List Nat := [2, 1, 1, 3, 4, 1, 2, 2, 1, 6]
def baseStart_427360 : Nat := 118140960795 + 427360 * 2 ^ 59
def prefixEnd_427360 : Nat := 4983230072969 + 3 ^ 40 * 427360 * 2
def baseEnd_427360 : Nat := 73147030835184395244871

theorem tailTrace_427360 : CollatzResearch.WordTrace tailWord_427360 prefixEnd_427360 73147030835184395244871 := by
  unfold tailWord_427360
  simp only [CollatzResearch.WordTrace]
  refine ⟨7793549865877591061147767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10391399821170121414863689 7793549865877591061147767)
  ·
    refine ⟨11690324798816386591721651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7793549865877591061147767 11690324798816386591721651)
    ·
      refine ⟨17535487198224579887582477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11690324798816386591721651 17535487198224579887582477)
      ·
        refine ⟨6575807699334217457843429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17535487198224579887582477 6575807699334217457843429)
        ·
          refine ⟨1232963943625165773345643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6575807699334217457843429 1232963943625165773345643)
          ·
            refine ⟨1849445915437748660018465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232963943625165773345643 1849445915437748660018465)
            ·
              refine ⟨1387084436578311495013849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1849445915437748660018465 1387084436578311495013849)
              ·
                refine ⟨1040313327433733621260387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1387084436578311495013849 1040313327433733621260387)
                ·
                  refine ⟨1560469991150600431890581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1040313327433733621260387 1560469991150600431890581)
                  ·
                    refine ⟨73147030835184395244871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1560469991150600431890581 73147030835184395244871)
                    ·
                      rfl

theorem cell23_427360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 1, 6].length) (baseStart_427360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427360 prefixEnd_427360 := by exact prefixLift 427360
  have htrace : WordTrace (prefixWord ++ tailWord_427360) baseStart_427360 baseEnd_427360 := by
    simpa [prefixWord, tailWord_427360, baseEnd_427360] using wordTrace_append hprefix tailTrace_427360
  have hstable : (prefixWord ++ tailWord_427360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427360).length < 2 ^ (prefixWord ++ tailWord_427360).sum := by decide
  have hdescent : baseEnd_427360 < baseStart_427360 := by decide
  rcases family_descends (prefixWord ++ tailWord_427360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427364 : List Nat := [2, 3, 1, 1, 3, 4, 2, 1, 1, 5]
def baseStart_427364 : Nat := 118140960795 + 427364 * 2 ^ 59
def prefixEnd_427364 : Nat := 4983230072969 + 3 ^ 40 * 427364 * 2
def baseEnd_427364 : Nat := 73147715476057056694865

theorem tailTrace_427364 : CollatzResearch.WordTrace tailWord_427364 prefixEnd_427364 73147715476057056694865 := by
  unfold tailWord_427364
  simp only [CollatzResearch.WordTrace]
  refine ⟨7793622811870345402720573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10391497082493793870294097 7793622811870345402720573)
  ·
    refine ⟨2922608554451379526020215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7793622811870345402720573 2922608554451379526020215)
    ·
      refine ⟨4383912831677069289030323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2922608554451379526020215 4383912831677069289030323)
      ·
        refine ⟨6575869247515603933545485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4383912831677069289030323 6575869247515603933545485)
        ·
          refine ⟨2465950967818351475079557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6575869247515603933545485 2465950967818351475079557)
          ·
            refine ⟨462365806465940901577417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2465950967818351475079557 462365806465940901577417)
            ·
              refine ⟨346774354849455676183063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462365806465940901577417 346774354849455676183063)
              ·
                refine ⟨520161532274183514274595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346774354849455676183063 520161532274183514274595)
                ·
                  refine ⟨780242298411275271411893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 520161532274183514274595 780242298411275271411893)
                  ·
                    refine ⟨73147715476057056694865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 780242298411275271411893 73147715476057056694865)
                    ·
                      rfl

theorem cell23_427364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_427364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427364 prefixEnd_427364 := by exact prefixLift 427364
  have htrace : WordTrace (prefixWord ++ tailWord_427364) baseStart_427364 baseEnd_427364 := by
    simpa [prefixWord, tailWord_427364, baseEnd_427364] using wordTrace_append hprefix tailTrace_427364
  have hstable : (prefixWord ++ tailWord_427364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427364).length < 2 ^ (prefixWord ++ tailWord_427364).sum := by decide
  have hdescent : baseEnd_427364 < baseStart_427364 := by decide
  rcases family_descends (prefixWord ++ tailWord_427364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427377 : List Nat := [1, 2, 2, 2, 1, 2, 5, 2, 2, 4]
def baseStart_427377 : Nat := 118140960795 + 427377 * 2 ^ 59
def prefixEnd_427377 : Nat := 4983230072969 + 3 ^ 40 * 427377 * 2
def baseEnd_427377 : Nat := 73149940558893206407345

theorem tailTrace_427377 : CollatzResearch.WordTrace tailWord_427377 prefixEnd_427377 73149940558893206407345 := by
  unfold tailWord_427377
  simp only [CollatzResearch.WordTrace]
  refine ⟨15587719772693594025664385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10391813181795729350442923 15587719772693594025664385)
  ·
    refine ⟨11690789829520195519248289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15587719772693594025664385 11690789829520195519248289)
    ·
      refine ⟨8768092372140146639436217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11690789829520195519248289 8768092372140146639436217)
      ·
        refine ⟨6576069279105109979577163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8768092372140146639436217 6576069279105109979577163)
        ·
          refine ⟨9864103918657664969365745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6576069279105109979577163 9864103918657664969365745)
          ·
            refine ⟨7398077938993248727024309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9864103918657664969365745 7398077938993248727024309)
            ·
              refine ⟨693569806780617068158529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7398077938993248727024309 693569806780617068158529)
              ·
                refine ⟨520177355085462801118897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 693569806780617068158529 520177355085462801118897)
                ·
                  refine ⟨390133016314097100839173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 520177355085462801118897 390133016314097100839173)
                  ·
                    refine ⟨73149940558893206407345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 390133016314097100839173 73149940558893206407345)
                    ·
                      rfl

theorem cell23_427377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 4].length) (baseStart_427377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427377 prefixEnd_427377 := by exact prefixLift 427377
  have htrace : WordTrace (prefixWord ++ tailWord_427377) baseStart_427377 baseEnd_427377 := by
    simpa [prefixWord, tailWord_427377, baseEnd_427377] using wordTrace_append hprefix tailTrace_427377
  have hstable : (prefixWord ++ tailWord_427377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427377).length < 2 ^ (prefixWord ++ tailWord_427377).sum := by decide
  have hdescent : baseEnd_427377 < baseStart_427377 := by decide
  rcases family_descends (prefixWord ++ tailWord_427377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427394 : List Nat := [3, 4, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_427394 : Nat := 118140960795 + 427394 * 2 ^ 59
def prefixEnd_427394 : Nat := 4983230072969 + 3 ^ 40 * 427394 * 2
def baseEnd_427394 : Nat := 73152850282602017569819

theorem tailTrace_427394 : CollatzResearch.WordTrace tailWord_427394 prefixEnd_427394 73152850282602017569819 := by
  unfold tailWord_427394
  simp only [CollatzResearch.WordTrace]
  refine ⟨3897084953408001482258309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10392226542421337286022157 3897084953408001482258309)
  ·
    refine ⟨730703428764000277923433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3897084953408001482258309 730703428764000277923433)
    ·
      refine ⟨548027571573000208442575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 730703428764000277923433 548027571573000208442575)
      ·
        refine ⟨822041357359500312663863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548027571573000208442575 822041357359500312663863)
        ·
          refine ⟨1233062036039250468995795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822041357359500312663863 1233062036039250468995795)
          ·
            refine ⟨1849593054058875703493693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233062036039250468995795 1849593054058875703493693)
            ·
              refine ⟨693597395272078388810135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1849593054058875703493693 693597395272078388810135)
              ·
                refine ⟨1040396092908117583215203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 693597395272078388810135 1040396092908117583215203)
                ·
                  refine ⟨1560594139362176374822805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1040396092908117583215203 1560594139362176374822805)
                  ·
                    refine ⟨73152850282602017569819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1560594139362176374822805 73152850282602017569819)
                    ·
                      rfl

theorem cell23_427394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_427394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427394 prefixEnd_427394 := by exact prefixLift 427394
  have htrace : WordTrace (prefixWord ++ tailWord_427394) baseStart_427394 baseEnd_427394 := by
    simpa [prefixWord, tailWord_427394, baseEnd_427394] using wordTrace_append hprefix tailTrace_427394
  have hstable : (prefixWord ++ tailWord_427394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427394).length < 2 ^ (prefixWord ++ tailWord_427394).sum := by decide
  have hdescent : baseEnd_427394 < baseStart_427394 := by decide
  rcases family_descends (prefixWord ++ tailWord_427394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427417 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 4, 1, 3]
def baseStart_427417 : Nat := 118140960795 + 427417 * 2 ^ 59
def prefixEnd_427417 : Nat := 4983230072969 + 3 ^ 40 * 427417 * 2
def baseEnd_427417 : Nat := 219470360902859462721851

theorem tailTrace_427417 : CollatzResearch.WordTrace tailWord_427417 prefixEnd_427417 219470360902859462721851 := by
  unfold tailWord_427417
  simp only [CollatzResearch.WordTrace]
  refine ⟨15589178692548680857120505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10392785795032453904747003 15589178692548680857120505)
  ·
    refine ⟨11691884019411510642840379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15589178692548680857120505 11691884019411510642840379)
    ·
      refine ⟨17537826029117265964260569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11691884019411510642840379 17537826029117265964260569)
      ·
        refine ⟨13153369521837949473195427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17537826029117265964260569 13153369521837949473195427)
        ·
          refine ⟨19730054282756924209793141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13153369521837949473195427 19730054282756924209793141)
          ·
            refine ⟨1849692589008461644668107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19730054282756924209793141 1849692589008461644668107)
            ·
              refine ⟨2774538883512692467002161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1849692589008461644668107 2774538883512692467002161)
              ·
                refine ⟨2080904162634519350251621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2774538883512692467002161 2080904162634519350251621)
                ·
                  refine ⟨390169530493972378172179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2080904162634519350251621 390169530493972378172179)
                  ·
                    refine ⟨585254295740958567258269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 390169530493972378172179 585254295740958567258269)
                    ·
                      refine ⟨219470360902859462721851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 585254295740958567258269 219470360902859462721851)
                      ·
                        rfl

theorem cell23_427417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 1, 3].length) (baseStart_427417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427417 prefixEnd_427417 := by exact prefixLift 427417
  have htrace : WordTrace (prefixWord ++ tailWord_427417) baseStart_427417 baseEnd_427417 := by
    simpa [prefixWord, tailWord_427417, baseEnd_427417] using wordTrace_append hprefix tailTrace_427417
  have hstable : (prefixWord ++ tailWord_427417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427417).length < 2 ^ (prefixWord ++ tailWord_427417).sum := by decide
  have hdescent : baseEnd_427417 < baseStart_427417 := by decide
  rcases family_descends (prefixWord ++ tailWord_427417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427491 : List Nat := [1, 1, 1, 6, 2, 1, 1, 4, 2, 2, 2]
def baseStart_427491 : Nat := 118140960795 + 427491 * 2 ^ 59
def prefixEnd_427491 : Nat := 4983230072969 + 3 ^ 40 * 427491 * 2
def baseEnd_427491 : Nat := 219508358471292173196511

theorem tailTrace_427491 : CollatzResearch.WordTrace tailWord_427491 prefixEnd_427491 219508358471292173196511 := by
  unfold tailWord_427491
  simp only [CollatzResearch.WordTrace]
  refine ⟨15591877694280591495314327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10394585129520394330209551 15591877694280591495314327)
  ·
    refine ⟨23387816541420887242971491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15591877694280591495314327 23387816541420887242971491)
    ·
      refine ⟨35081724812131330864457237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23387816541420887242971491 35081724812131330864457237)
      ·
        refine ⟨1644455850568656134271433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35081724812131330864457237 1644455850568656134271433)
        ·
          refine ⟨1233341887926492100703575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1644455850568656134271433 1233341887926492100703575)
          ·
            refine ⟨1850012831889738151055363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233341887926492100703575 1850012831889738151055363)
            ·
              refine ⟨2775019247834607226583045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850012831889738151055363 2775019247834607226583045)
              ·
                refine ⟨520316108968988854984321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2775019247834607226583045 520316108968988854984321)
                ·
                  refine ⟨390237081726741641238241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 520316108968988854984321 390237081726741641238241)
                  ·
                    refine ⟨292677811295056230928681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 390237081726741641238241 292677811295056230928681)
                    ·
                      refine ⟨219508358471292173196511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 292677811295056230928681 219508358471292173196511)
                      ·
                        rfl

theorem cell23_427491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_427491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427491 prefixEnd_427491 := by exact prefixLift 427491
  have htrace : WordTrace (prefixWord ++ tailWord_427491) baseStart_427491 baseEnd_427491 := by
    simpa [prefixWord, tailWord_427491, baseEnd_427491] using wordTrace_append hprefix tailTrace_427491
  have hstable : (prefixWord ++ tailWord_427491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427491).length < 2 ^ (prefixWord ++ tailWord_427491).sum := by decide
  have hdescent : baseEnd_427491 < baseStart_427491 := by decide
  rcases family_descends (prefixWord ++ tailWord_427491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427527 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 1, 7]
def baseStart_427527 : Nat := 118140960795 + 427527 * 2 ^ 59
def prefixEnd_427527 : Nat := 4983230072969 + 3 ^ 40 * 427527 * 2
def baseEnd_427527 : Nat := 73175614591618010782115

theorem tailTrace_427527 : CollatzResearch.WordTrace tailWord_427527 prefixEnd_427527 73175614591618010782115 := by
  unfold tailWord_427527
  simp only [CollatzResearch.WordTrace]
  refine ⟨15593190722150169643624835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10395460481433446429083223 15593190722150169643624835)
  ·
    refine ⟨23389786083225254465437253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15593190722150169643624835 23389786083225254465437253)
    ·
      refine ⟨4385584890604735212269485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23389786083225254465437253 4385584890604735212269485)
      ·
        refine ⟨1644594333976775704601057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4385584890604735212269485 1644594333976775704601057)
        ·
          refine ⟨1233445750482581778450793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1644594333976775704601057 1233445750482581778450793)
          ·
            refine ⟨925084312861936333838095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1233445750482581778450793 925084312861936333838095)
            ·
              refine ⟨1387626469292904500757143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925084312861936333838095 1387626469292904500757143)
              ·
                refine ⟨2081439703939356751135715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1387626469292904500757143 2081439703939356751135715)
                ·
                  refine ⟨3122159555909035126703573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2081439703939356751135715 3122159555909035126703573)
                  ·
                    refine ⟨73175614591618010782115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3122159555909035126703573 73175614591618010782115)
                    ·
                      rfl

theorem cell23_427527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_427527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427527 prefixEnd_427527 := by exact prefixLift 427527
  have htrace : WordTrace (prefixWord ++ tailWord_427527) baseStart_427527 baseEnd_427527 := by
    simpa [prefixWord, tailWord_427527, baseEnd_427527] using wordTrace_append hprefix tailTrace_427527
  have hstable : (prefixWord ++ tailWord_427527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427527).length < 2 ^ (prefixWord ++ tailWord_427527).sum := by decide
  have hdescent : baseEnd_427527 < baseStart_427527 := by decide
  rcases family_descends (prefixWord ++ tailWord_427527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427617 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 3, 5]
def baseStart_427617 : Nat := 118140960795 + 427617 * 2 ^ 59
def prefixEnd_427617 : Nat := 4983230072969 + 3 ^ 40 * 427617 * 2
def baseEnd_427617 : Nat := 73191019011252893406977

theorem tailTrace_427617 : CollatzResearch.WordTrace tailWord_427617 prefixEnd_427617 73191019011252893406977 := by
  unfold tailWord_427617
  simp only [CollatzResearch.WordTrace]
  refine ⟨15596473291824115014401105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10397648861216076676267403 15596473291824115014401105)
  ·
    refine ⟨11697354968868086260800829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15596473291824115014401105 11697354968868086260800829)
    ·
      refine ⟨4386508113325532347800311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11697354968868086260800829 4386508113325532347800311)
      ·
        refine ⟨6579762169988298521700467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4386508113325532347800311 6579762169988298521700467)
        ·
          refine ⟨9869643254982447782550701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6579762169988298521700467 9869643254982447782550701)
          ·
            refine ⟨3701116220618417918456513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9869643254982447782550701 3701116220618417918456513)
            ·
              refine ⟨2775837165463813438842385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3701116220618417918456513 2775837165463813438842385)
              ·
                refine ⟨2081877874097860079131789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2775837165463813438842385 2081877874097860079131789)
                ·
                  refine ⟨780704202786697529674421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2081877874097860079131789 780704202786697529674421)
                  ·
                    refine ⟨73191019011252893406977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 780704202786697529674421 73191019011252893406977)
                    ·
                      rfl

theorem cell23_427617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_427617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427617 prefixEnd_427617 := by exact prefixLift 427617
  have htrace : WordTrace (prefixWord ++ tailWord_427617) baseStart_427617 baseEnd_427617 := by
    simpa [prefixWord, tailWord_427617, baseEnd_427617] using wordTrace_append hprefix tailTrace_427617
  have hstable : (prefixWord ++ tailWord_427617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427617).length < 2 ^ (prefixWord ++ tailWord_427617).sum := by decide
  have hdescent : baseEnd_427617 < baseStart_427617 := by decide
  rcases family_descends (prefixWord ++ tailWord_427617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427621 : List Nat := [1, 3, 1, 3, 3, 3, 2, 1, 6]
def baseStart_427621 : Nat := 118140960795 + 427621 * 2 ^ 59
def prefixEnd_427621 : Nat := 4983230072969 + 3 ^ 40 * 427621 * 2
def baseEnd_427621 : Nat := 24397234550708518285657

theorem tailTrace_427621 : CollatzResearch.WordTrace tailWord_427621 prefixEnd_427621 24397234550708518285657 := by
  unfold tailWord_427621
  simp only [CollatzResearch.WordTrace]
  refine ⟨15596619183809623697546717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10397746122539749131697811 15596619183809623697546717)
  ·
    refine ⟨5848732193928608886580019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15596619183809623697546717 5848732193928608886580019)
    ·
      refine ⟨8773098290892913329870029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5848732193928608886580019 8773098290892913329870029)
      ·
        refine ⟨3289911859084842498701261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8773098290892913329870029 3289911859084842498701261)
        ·
          refine ⟨1233716947156815937012973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3289911859084842498701261 1233716947156815937012973)
          ·
            refine ⟨462643855183805976379865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1233716947156815937012973 462643855183805976379865)
            ·
              refine ⟨346982891387854482284899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462643855183805976379865 346982891387854482284899)
              ·
                refine ⟨520474337081781723427349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346982891387854482284899 520474337081781723427349)
                ·
                  refine ⟨24397234550708518285657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 520474337081781723427349 24397234550708518285657)
                  ·
                    rfl

theorem cell23_427621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 6].length) (baseStart_427621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427621 prefixEnd_427621 := by exact prefixLift 427621
  have htrace : WordTrace (prefixWord ++ tailWord_427621) baseStart_427621 baseEnd_427621 := by
    simpa [prefixWord, tailWord_427621, baseEnd_427621] using wordTrace_append hprefix tailTrace_427621
  have hstable : (prefixWord ++ tailWord_427621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427621).length < 2 ^ (prefixWord ++ tailWord_427621).sum := by decide
  have hdescent : baseEnd_427621 < baseStart_427621 := by decide
  rcases family_descends (prefixWord ++ tailWord_427621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427634 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 3, 5]
def baseStart_427634 : Nat := 118140960795 + 427634 * 2 ^ 59
def prefixEnd_427634 : Nat := 4983230072969 + 3 ^ 40 * 427634 * 2
def baseEnd_427634 : Nat := 73193928734961704569451

theorem tailTrace_427634 : CollatzResearch.WordTrace tailWord_427634 prefixEnd_427634 73193928734961704569451 := by
  unfold tailWord_427634
  simp only [CollatzResearch.WordTrace]
  refine ⟨3899273333190631729442489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10398062221841684611846637 3899273333190631729442489)
  ·
    refine ⟨2924454999892973797081867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3899273333190631729442489 2924454999892973797081867)
    ·
      refine ⟨4386682499839460695622801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2924454999892973797081867 4386682499839460695622801)
      ·
        refine ⟨3290011874879595521717101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4386682499839460695622801 3290011874879595521717101)
        ·
          refine ⟨1233754453079848320643913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3290011874879595521717101 1233754453079848320643913)
          ·
            refine ⟨925315839809886240482935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1233754453079848320643913 925315839809886240482935)
            ·
              refine ⟨1387973759714829360724403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925315839809886240482935 1387973759714829360724403)
              ·
                refine ⟨2081960639572244041086605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1387973759714829360724403 2081960639572244041086605)
                ·
                  refine ⟨780735239839591515407477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2081960639572244041086605 780735239839591515407477)
                  ·
                    refine ⟨73193928734961704569451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 780735239839591515407477 73193928734961704569451)
                    ·
                      rfl

theorem cell23_427634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_427634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427634 prefixEnd_427634 := by exact prefixLift 427634
  have htrace : WordTrace (prefixWord ++ tailWord_427634) baseStart_427634 baseEnd_427634 := by
    simpa [prefixWord, tailWord_427634, baseEnd_427634] using wordTrace_append hprefix tailTrace_427634
  have hstable : (prefixWord ++ tailWord_427634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427634).length < 2 ^ (prefixWord ++ tailWord_427634).sum := by decide
  have hdescent : baseEnd_427634 < baseStart_427634 := by decide
  rcases family_descends (prefixWord ++ tailWord_427634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427641 : List Nat := [1, 2, 1, 3, 3, 1, 4, 1, 2, 3, 2]
def baseStart_427641 : Nat := 118140960795 + 427641 * 2 ^ 59
def prefixEnd_427641 : Nat := 4983230072969 + 3 ^ 40 * 427641 * 2
def baseEnd_427641 : Nat := 219585380569466586320821

theorem tailTrace_427641 : CollatzResearch.WordTrace tailWord_427641 prefixEnd_427641 219585380569466586320821 := by
  unfold tailWord_427641
  simp only [CollatzResearch.WordTrace]
  refine ⟨15597348643737167113274777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10398232429158111408849851 15597348643737167113274777)
  ·
    refine ⟨11698011482802875334956083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15597348643737167113274777 11698011482802875334956083)
    ·
      refine ⟨17547017224204313002434125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11698011482802875334956083 17547017224204313002434125)
      ·
        refine ⟨6580131459076617375912797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17547017224204313002434125 6580131459076617375912797)
        ·
          refine ⟨2467549297153731515967299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6580131459076617375912797 2467549297153731515967299)
          ·
            refine ⟨3701323945730597273950949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2467549297153731515967299 3701323945730597273950949)
            ·
              refine ⟨693998239824486988865803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3701323945730597273950949 693998239824486988865803)
              ·
                refine ⟨1040997359736730483298705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 693998239824486988865803 1040997359736730483298705)
                ·
                  refine ⟨780748019802547862474029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1040997359736730483298705 780748019802547862474029)
                  ·
                    refine ⟨292780507425955448427761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 780748019802547862474029 292780507425955448427761)
                    ·
                      refine ⟨219585380569466586320821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 292780507425955448427761 219585380569466586320821)
                      ·
                        rfl

theorem cell23_427641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 3, 2].length) (baseStart_427641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427641 prefixEnd_427641 := by exact prefixLift 427641
  have htrace : WordTrace (prefixWord ++ tailWord_427641) baseStart_427641 baseEnd_427641 := by
    simpa [prefixWord, tailWord_427641, baseEnd_427641] using wordTrace_append hprefix tailTrace_427641
  have hstable : (prefixWord ++ tailWord_427641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427641).length < 2 ^ (prefixWord ++ tailWord_427641).sum := by decide
  have hdescent : baseEnd_427641 < baseStart_427641 := by decide
  rcases family_descends (prefixWord ++ tailWord_427641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427681 : List Nat := [1, 2, 3, 3, 2, 1, 2, 3, 2, 4]
def baseStart_427681 : Nat := 118140960795 + 427681 * 2 ^ 59
def prefixEnd_427681 : Nat := 4983230072969 + 3 ^ 40 * 427681 * 2
def baseEnd_427681 : Nat := 73201973265215476606879

theorem tailTrace_427681 : CollatzResearch.WordTrace tailWord_427681 prefixEnd_427681 73201973265215476606879 := by
  unfold tailWord_427681
  simp only [CollatzResearch.WordTrace]
  refine ⟨15598807563592253944730897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10399205042394835963153931 15598807563592253944730897)
  ·
    refine ⟨11699105672694190458548173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15598807563592253944730897 11699105672694190458548173)
    ·
      refine ⟨4387164627260321421955565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11699105672694190458548173 4387164627260321421955565)
      ·
        refine ⟨1645186735222620533233337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4387164627260321421955565 1645186735222620533233337)
        ·
          refine ⟨1233890051416965399925003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1645186735222620533233337 1233890051416965399925003)
          ·
            refine ⟨1850835077125448099887505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233890051416965399925003 1850835077125448099887505)
            ·
              refine ⟨1388126307844086074915629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1850835077125448099887505 1388126307844086074915629)
              ·
                refine ⟨520547365441532278093361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1388126307844086074915629 520547365441532278093361)
                ·
                  refine ⟨390410524081149208570021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 520547365441532278093361 390410524081149208570021)
                  ·
                    refine ⟨73201973265215476606879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 390410524081149208570021 73201973265215476606879)
                    ·
                      rfl

theorem cell23_427681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_427681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427681 prefixEnd_427681 := by exact prefixLift 427681
  have htrace : WordTrace (prefixWord ++ tailWord_427681) baseStart_427681 baseEnd_427681 := by
    simpa [prefixWord, tailWord_427681, baseEnd_427681] using wordTrace_append hprefix tailTrace_427681
  have hstable : (prefixWord ++ tailWord_427681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427681).length < 2 ^ (prefixWord ++ tailWord_427681).sum := by decide
  have hdescent : baseEnd_427681 < baseStart_427681 := by decide
  rcases family_descends (prefixWord ++ tailWord_427681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427684 : List Nat := [2, 3, 1, 2, 2, 2, 1, 3, 1, 2, 4]
def baseStart_427684 : Nat := 118140960795 + 427684 * 2 ^ 59
def prefixEnd_427684 : Nat := 4983230072969 + 3 ^ 40 * 427684 * 2
def baseEnd_427684 : Nat := 219607460237609918083123

theorem tailTrace_427684 : CollatzResearch.WordTrace tailWord_427684 prefixEnd_427684 219607460237609918083123 := by
  unfold tailWord_427684
  simp only [CollatzResearch.WordTrace]
  refine ⟨7799458491290692728545053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10399277988387590304726737 7799458491290692728545053)
  ·
    refine ⟨2924796934234009773204395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7799458491290692728545053 2924796934234009773204395)
    ·
      refine ⟨4387195401351014659806593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2924796934234009773204395 4387195401351014659806593)
      ·
        refine ⟨3290396551013260994854945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4387195401351014659806593 3290396551013260994854945)
        ·
          refine ⟨2467797413259945746141209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3290396551013260994854945 2467797413259945746141209)
          ·
            refine ⟨1850848059944959309605907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2467797413259945746141209 1850848059944959309605907)
            ·
              refine ⟨2776272089917438964408861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850848059944959309605907 2776272089917438964408861)
              ·
                refine ⟨1041102033719039611653323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2776272089917438964408861 1041102033719039611653323)
                ·
                  refine ⟨1561653050578559417479985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1041102033719039611653323 1561653050578559417479985)
                  ·
                    refine ⟨1171239787933919563109989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1561653050578559417479985 1171239787933919563109989)
                    ·
                      refine ⟨219607460237609918083123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1171239787933919563109989 219607460237609918083123)
                      ·
                        rfl

theorem cell23_427684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_427684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427684 prefixEnd_427684 := by exact prefixLift 427684
  have htrace : WordTrace (prefixWord ++ tailWord_427684) baseStart_427684 baseEnd_427684 := by
    simpa [prefixWord, tailWord_427684, baseEnd_427684] using wordTrace_append hprefix tailTrace_427684
  have hstable : (prefixWord ++ tailWord_427684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427684).length < 2 ^ (prefixWord ++ tailWord_427684).sum := by decide
  have hdescent : baseEnd_427684 < baseStart_427684 := by decide
  rcases family_descends (prefixWord ++ tailWord_427684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427708 : List Nat := [2, 2, 2, 3, 1, 2, 4, 1, 1, 2, 3]
def baseStart_427708 : Nat := 118140960795 + 427708 * 2 ^ 59
def prefixEnd_427708 : Nat := 4983230072969 + 3 ^ 40 * 427708 * 2
def baseEnd_427708 : Nat := 219619783773317824183013

theorem tailTrace_427708 : CollatzResearch.WordTrace tailWord_427708 prefixEnd_427708 219619783773317824183013 := by
  unfold tailWord_427708
  simp only [CollatzResearch.WordTrace]
  refine ⟨7799896167247218777981889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10399861556329625037309185 7799896167247218777981889)
  ·
    refine ⟨5849922125435414083486417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7799896167247218777981889 5849922125435414083486417)
    ·
      refine ⟨4387441594076560562614813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5849922125435414083486417 4387441594076560562614813)
      ·
        refine ⟨1645290597778710210980555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4387441594076560562614813 1645290597778710210980555)
        ·
          refine ⟨2467935896668065316470833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1645290597778710210980555 2467935896668065316470833)
          ·
            refine ⟨1850951922501048987353125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2467935896668065316470833 1850951922501048987353125)
            ·
              refine ⟨347053485468946685128711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1850951922501048987353125 347053485468946685128711)
              ·
                refine ⟨520580228203420027693067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347053485468946685128711 520580228203420027693067)
                ·
                  refine ⟨780870342305130041539601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 520580228203420027693067 780870342305130041539601)
                  ·
                    refine ⟨585652756728847531154701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 780870342305130041539601 585652756728847531154701)
                    ·
                      refine ⟨219619783773317824183013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 585652756728847531154701 219619783773317824183013)
                      ·
                        rfl

theorem cell23_427708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_427708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427708 prefixEnd_427708 := by exact prefixLift 427708
  have htrace : WordTrace (prefixWord ++ tailWord_427708) baseStart_427708 baseEnd_427708 := by
    simpa [prefixWord, tailWord_427708, baseEnd_427708] using wordTrace_append hprefix tailTrace_427708
  have hstable : (prefixWord ++ tailWord_427708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427708).length < 2 ^ (prefixWord ++ tailWord_427708).sum := by decide
  have hdescent : baseEnd_427708 < baseStart_427708 := by decide
  rcases family_descends (prefixWord ++ tailWord_427708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427717 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 2, 2, 5]
def baseStart_427717 : Nat := 118140960795 + 427717 * 2 ^ 59
def prefixEnd_427717 : Nat := 4983230072969 + 3 ^ 40 * 427717 * 2
def baseEnd_427717 : Nat := 219624405099208288970471

theorem tailTrace_427717 : CollatzResearch.WordTrace tailWord_427717 prefixEnd_427717 219624405099208288970471 := by
  unfold tailWord_427717
  simp only [CollatzResearch.WordTrace]
  refine ⟨15600120591461832093041405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10400080394307888062027603 15600120591461832093041405)
  ·
    refine ⟨5850045221798187034890527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15600120591461832093041405 5850045221798187034890527)
    ·
      refine ⟨8775067832697280552335791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5850045221798187034890527 8775067832697280552335791)
      ·
        refine ⟨13162601749045920828503687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8775067832697280552335791 13162601749045920828503687)
        ·
          refine ⟨19743902623568881242755531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13162601749045920828503687 19743902623568881242755531)
          ·
            refine ⟨29615853935353321864133297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19743902623568881242755531 29615853935353321864133297)
            ·
              refine ⟨22211890451514991398099973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29615853935353321864133297 22211890451514991398099973)
              ·
                refine ⟨4164729459659060887143745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22211890451514991398099973 4164729459659060887143745)
                ·
                  refine ⟨3123547094744295665357809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4164729459659060887143745 3123547094744295665357809)
                  ·
                    refine ⟨2342660321058221749018357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3123547094744295665357809 2342660321058221749018357)
                    ·
                      refine ⟨219624405099208288970471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2342660321058221749018357 219624405099208288970471)
                      ·
                        rfl

theorem cell23_427717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_427717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427717 prefixEnd_427717 := by exact prefixLift 427717
  have htrace : WordTrace (prefixWord ++ tailWord_427717) baseStart_427717 baseEnd_427717 := by
    simpa [prefixWord, tailWord_427717, baseEnd_427717] using wordTrace_append hprefix tailTrace_427717
  have hstable : (prefixWord ++ tailWord_427717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427717).length < 2 ^ (prefixWord ++ tailWord_427717).sum := by decide
  have hdescent : baseEnd_427717 < baseStart_427717 := by decide
  rcases family_descends (prefixWord ++ tailWord_427717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427727 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 4]
def baseStart_427727 : Nat := 118140960795 + 427727 * 2 ^ 59
def prefixEnd_427727 : Nat := 4983230072969 + 3 ^ 40 * 427727 * 2
def baseEnd_427727 : Nat := 219629539905753249845425

theorem tailTrace_427727 : CollatzResearch.WordTrace tailWord_427727 prefixEnd_427727 219629539905753249845425 := by
  unfold tailWord_427727
  simp only [CollatzResearch.WordTrace]
  refine ⟨15600485321425603800905435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10400323547617069200603623 15600485321425603800905435)
  ·
    refine ⟨23400727982138405701358153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15600485321425603800905435 23400727982138405701358153)
    ·
      refine ⟨17550545986603804276018615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23400727982138405701358153 17550545986603804276018615)
      ·
        refine ⟨26325818979905706414027923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17550545986603804276018615 26325818979905706414027923)
        ·
          refine ⟨39488728469858559621041885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26325818979905706414027923 39488728469858559621041885)
          ·
            refine ⟨14808273176196959857890707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39488728469858559621041885 14808273176196959857890707)
            ·
              refine ⟨22212409764295439786836061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14808273176196959857890707 22212409764295439786836061)
              ·
                refine ⟨8329653661610789920063523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22212409764295439786836061 8329653661610789920063523)
                ·
                  refine ⟨12494480492416184880095285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8329653661610789920063523 12494480492416184880095285)
                  ·
                    refine ⟨1171357546164017332508933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12494480492416184880095285 1171357546164017332508933)
                    ·
                      refine ⟨219629539905753249845425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1171357546164017332508933 219629539905753249845425)
                      ·
                        rfl

theorem cell23_427727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 4].length) (baseStart_427727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427727 prefixEnd_427727 := by exact prefixLift 427727
  have htrace : WordTrace (prefixWord ++ tailWord_427727) baseStart_427727 baseEnd_427727 := by
    simpa [prefixWord, tailWord_427727, baseEnd_427727] using wordTrace_append hprefix tailTrace_427727
  have hstable : (prefixWord ++ tailWord_427727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427727).length < 2 ^ (prefixWord ++ tailWord_427727).sum := by decide
  have hdescent : baseEnd_427727 < baseStart_427727 := by decide
  rcases family_descends (prefixWord ++ tailWord_427727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427748 : List Nat := [2, 3, 1, 1, 1, 3, 4, 2, 1, 3, 2]
def baseStart_427748 : Nat := 118140960795 + 427748 * 2 ^ 59
def prefixEnd_427748 : Nat := 4983230072969 + 3 ^ 40 * 427748 * 2
def baseEnd_427748 : Nat := 219640322999497667682829

theorem tailTrace_427748 : CollatzResearch.WordTrace tailWord_427748 prefixEnd_427748 219640322999497667682829 := by
  unfold tailWord_427748
  simp only [CollatzResearch.WordTrace]
  refine ⟨7800625627174762193709949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10400834169566349591613265 7800625627174762193709949)
  ·
    refine ⟨2925234610190535822641231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7800625627174762193709949 2925234610190535822641231)
    ·
      refine ⟨4387851915285803733961847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2925234610190535822641231 4387851915285803733961847)
      ·
        refine ⟨6581777872928705600942771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4387851915285803733961847 6581777872928705600942771)
        ·
          refine ⟨9872666809393058401414157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6581777872928705600942771 9872666809393058401414157)
          ·
            refine ⟨3702250053522396900530309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9872666809393058401414157 3702250053522396900530309)
            ·
              refine ⟨694171885035449418849433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3702250053522396900530309 694171885035449418849433)
              ·
                refine ⟨520628913776587064137075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 694171885035449418849433 520628913776587064137075)
                ·
                  refine ⟨780943370664880596205613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 520628913776587064137075 780943370664880596205613)
                  ·
                    refine ⟨292853763999330223577105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 780943370664880596205613 292853763999330223577105)
                    ·
                      refine ⟨219640322999497667682829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 292853763999330223577105 219640322999497667682829)
                      ·
                        rfl

theorem cell23_427748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 1, 3, 2].length) (baseStart_427748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427748 prefixEnd_427748 := by exact prefixLift 427748
  have htrace : WordTrace (prefixWord ++ tailWord_427748) baseStart_427748 baseEnd_427748 := by
    simpa [prefixWord, tailWord_427748, baseEnd_427748] using wordTrace_append hprefix tailTrace_427748
  have hstable : (prefixWord ++ tailWord_427748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427748).length < 2 ^ (prefixWord ++ tailWord_427748).sum := by decide
  have hdescent : baseEnd_427748 < baseStart_427748 := by decide
  rcases family_descends (prefixWord ++ tailWord_427748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427767 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 9]
def baseStart_427767 : Nat := 118140960795 + 427767 * 2 ^ 59
def prefixEnd_427767 : Nat := 4983230072969 + 3 ^ 40 * 427767 * 2
def baseEnd_427767 : Nat := 24405564347992565927249

theorem tailTrace_427767 : CollatzResearch.WordTrace tailWord_427767 prefixEnd_427767 24405564347992565927249 := by
  unfold tailWord_427767
  simp only [CollatzResearch.WordTrace]
  refine ⟨15601944241280690632361555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10401296160853793754907703 15601944241280690632361555)
  ·
    refine ⟨23402916361921035948542333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15601944241280690632361555 23402916361921035948542333)
    ·
      refine ⟨8776093635720388480703375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23402916361921035948542333 8776093635720388480703375)
      ·
        refine ⟨13164140453580582721055063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8776093635720388480703375 13164140453580582721055063)
        ·
          refine ⟨19746210680370874081582595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13164140453580582721055063 19746210680370874081582595)
          ·
            refine ⟨29619316020556311122373893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19746210680370874081582595 29619316020556311122373893)
            ·
              refine ⟨5553621753854308335445105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29619316020556311122373893 5553621753854308335445105)
              ·
                refine ⟨4165216315390731251583829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5553621753854308335445105 4165216315390731251583829)
                ·
                  refine ⟨24405564347992565927249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4165216315390731251583829 24405564347992565927249)
                  ·
                    rfl

theorem cell23_427767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 9].length) (baseStart_427767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427767 prefixEnd_427767 := by exact prefixLift 427767
  have htrace : WordTrace (prefixWord ++ tailWord_427767) baseStart_427767 baseEnd_427767 := by
    simpa [prefixWord, tailWord_427767, baseEnd_427767] using wordTrace_append hprefix tailTrace_427767
  have hstable : (prefixWord ++ tailWord_427767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427767).length < 2 ^ (prefixWord ++ tailWord_427767).sum := by decide
  have hdescent : baseEnd_427767 < baseStart_427767 := by decide
  rcases family_descends (prefixWord ++ tailWord_427767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427838 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 2, 5, 2]
def baseStart_427838 : Nat := 118140960795 + 427838 * 2 ^ 59
def prefixEnd_427838 : Nat := 4983230072969 + 3 ^ 40 * 427838 * 2
def baseEnd_427838 : Nat := 219686536258402315557415

theorem tailTrace_427838 : CollatzResearch.WordTrace tailWord_427838 prefixEnd_427838 219686536258402315557415 := by
  unfold tailWord_427838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1950566728002933719774521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10403022549348979838797445 1950566728002933719774521)
  ·
    refine ⟨1462925046002200289830891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1950566728002933719774521 1462925046002200289830891)
    ·
      refine ⟨2194387569003300434746337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1462925046002200289830891 2194387569003300434746337)
      ·
        refine ⟨1645790676752475326059753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2194387569003300434746337 1645790676752475326059753)
        ·
          refine ⟨1234343007564356494544815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1645790676752475326059753 1234343007564356494544815)
          ·
            refine ⟨1851514511346534741817223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1234343007564356494544815 1851514511346534741817223)
            ·
              refine ⟨2777271767019802112725835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1851514511346534741817223 2777271767019802112725835)
              ·
                refine ⟨4165907650529703169088753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2777271767019802112725835 4165907650529703169088753)
                ·
                  refine ⟨3124430737897277376816565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4165907650529703169088753 3124430737897277376816565)
                  ·
                    refine ⟨292915381677869754076553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3124430737897277376816565 292915381677869754076553)
                    ·
                      refine ⟨219686536258402315557415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 292915381677869754076553 219686536258402315557415)
                      ·
                        rfl

theorem cell23_427838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_427838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427838 prefixEnd_427838 := by exact prefixLift 427838
  have htrace : WordTrace (prefixWord ++ tailWord_427838) baseStart_427838 baseEnd_427838 := by
    simpa [prefixWord, tailWord_427838, baseEnd_427838] using wordTrace_append hprefix tailTrace_427838
  have hstable : (prefixWord ++ tailWord_427838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427838).length < 2 ^ (prefixWord ++ tailWord_427838).sum := by decide
  have hdescent : baseEnd_427838 < baseStart_427838 := by decide
  rcases family_descends (prefixWord ++ tailWord_427838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427861 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 5, 4]
def baseStart_427861 : Nat := 118140960795 + 427861 * 2 ^ 59
def prefixEnd_427861 : Nat := 4983230072969 + 3 ^ 40 * 427861 * 2
def baseEnd_427861 : Nat := 73232782104485241856603

theorem tailTrace_427861 : CollatzResearch.WordTrace tailWord_427861 prefixEnd_427861 73232782104485241856603 := by
  unfold tailWord_427861
  simp only [CollatzResearch.WordTrace]
  refine ⟨15605372702940144686283437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10403581801960096457522291 15605372702940144686283437)
  ·
    refine ⟨5852014763602554257356289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15605372702940144686283437 5852014763602554257356289)
    ·
      refine ⟨4389011072701915693017217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5852014763602554257356289 4389011072701915693017217)
      ·
        refine ⟨3291758304526436769762913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4389011072701915693017217 3291758304526436769762913)
        ·
          refine ⟨2468818728394827577322185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3291758304526436769762913 2468818728394827577322185)
          ·
            refine ⟨1851614046296120682991639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2468818728394827577322185 1851614046296120682991639)
            ·
              refine ⟨2777421069444181024487459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1851614046296120682991639 2777421069444181024487459)
              ·
                refine ⟨4166131604166271536731189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2777421069444181024487459 4166131604166271536731189)
                ·
                  refine ⟨390574837890587956568549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4166131604166271536731189 390574837890587956568549)
                  ·
                    refine ⟨73232782104485241856603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 390574837890587956568549 73232782104485241856603)
                    ·
                      rfl

theorem cell23_427861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_427861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427861 prefixEnd_427861 := by exact prefixLift 427861
  have htrace : WordTrace (prefixWord ++ tailWord_427861) baseStart_427861 baseEnd_427861 := by
    simpa [prefixWord, tailWord_427861, baseEnd_427861] using wordTrace_append hprefix tailTrace_427861
  have hstable : (prefixWord ++ tailWord_427861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427861).length < 2 ^ (prefixWord ++ tailWord_427861).sum := by decide
  have hdescent : baseEnd_427861 < baseStart_427861 := by decide
  rcases family_descends (prefixWord ++ tailWord_427861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427868 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_427868 : Nat := 118140960795 + 427868 * 2 ^ 59
def prefixEnd_427868 : Nat := 4983230072969 + 3 ^ 40 * 427868 * 2
def baseEnd_427868 : Nat := 219701940678037198182277

theorem tailTrace_427868 : CollatzResearch.WordTrace tailWord_427868 prefixEnd_427868 219701940678037198182277 := by
  unfold tailWord_427868
  simp only [CollatzResearch.WordTrace]
  refine ⟨7802814006957392440894129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10403752009276523254525505 7802814006957392440894129)
  ·
    refine ⟨5852110505218044330670597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7802814006957392440894129 5852110505218044330670597)
    ·
      refine ⟨1097270719728383312000737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5852110505218044330670597 1097270719728383312000737)
      ·
        refine ⟨822953039796287484000553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1097270719728383312000737 822953039796287484000553)
        ·
          refine ⟨617214779847215613000415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 822953039796287484000553 617214779847215613000415)
          ·
            refine ⟨925822169770823419500623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617214779847215613000415 925822169770823419500623)
            ·
              refine ⟨1388733254656235129250935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925822169770823419500623 1388733254656235129250935)
              ·
                refine ⟨2083099881984352693876403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1388733254656235129250935 2083099881984352693876403)
                ·
                  refine ⟨3124649822976529040814605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2083099881984352693876403 3124649822976529040814605)
                  ·
                    refine ⟨1171743683616198390305477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3124649822976529040814605 1171743683616198390305477)
                    ·
                      refine ⟨219701940678037198182277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1171743683616198390305477 219701940678037198182277)
                      ·
                        rfl

theorem cell23_427868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_427868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427868 prefixEnd_427868 := by exact prefixLift 427868
  have htrace : WordTrace (prefixWord ++ tailWord_427868) baseStart_427868 baseEnd_427868 := by
    simpa [prefixWord, tailWord_427868, baseEnd_427868] using wordTrace_append hprefix tailTrace_427868
  have hstable : (prefixWord ++ tailWord_427868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427868).length < 2 ^ (prefixWord ++ tailWord_427868).sum := by decide
  have hdescent : baseEnd_427868 < baseStart_427868 := by decide
  rcases family_descends (prefixWord ++ tailWord_427868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427871 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 3]
def baseStart_427871 : Nat := 118140960795 + 427871 * 2 ^ 59
def prefixEnd_427871 : Nat := 4983230072969 + 3 ^ 40 * 427871 * 2
def baseEnd_427871 : Nat := 219703481120000686444763

theorem tailTrace_427871 : CollatzResearch.WordTrace tailWord_427871 prefixEnd_427871 219703481120000686444763 := by
  unfold tailWord_427871
  simp only [CollatzResearch.WordTrace]
  refine ⟨15605737432903916394147467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10403824955269277596098311 15605737432903916394147467)
  ·
    refine ⟨23408606149355874591221201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15605737432903916394147467 23408606149355874591221201)
    ·
      refine ⟨17556454612016905943415901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23408606149355874591221201 17556454612016905943415901)
      ·
        refine ⟨6583670479506339728780963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17556454612016905943415901 6583670479506339728780963)
        ·
          refine ⟨9875505719259509593171445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6583670479506339728780963 9875505719259509593171445)
          ·
            refine ⟨925828661180579024359823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9875505719259509593171445 925828661180579024359823)
            ·
              refine ⟨1388742991770868536539735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925828661180579024359823 1388742991770868536539735)
              ·
                refine ⟨2083114487656302804809603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1388742991770868536539735 2083114487656302804809603)
                ·
                  refine ⟨3124671731484454207214405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2083114487656302804809603 3124671731484454207214405)
                  ·
                    refine ⟨585875949653335163852701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3124671731484454207214405 585875949653335163852701)
                    ·
                      refine ⟨219703481120000686444763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 585875949653335163852701 219703481120000686444763)
                      ·
                        rfl

theorem cell23_427871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_427871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427871 prefixEnd_427871 := by exact prefixLift 427871
  have htrace : WordTrace (prefixWord ++ tailWord_427871) baseStart_427871 baseEnd_427871 := by
    simpa [prefixWord, tailWord_427871, baseEnd_427871] using wordTrace_append hprefix tailTrace_427871
  have hstable : (prefixWord ++ tailWord_427871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427871).length < 2 ^ (prefixWord ++ tailWord_427871).sum := by decide
  have hdescent : baseEnd_427871 < baseStart_427871 := by decide
  rcases family_descends (prefixWord ++ tailWord_427871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427921 : List Nat := [1, 2, 2, 1, 1, 1, 5, 4, 1, 5]
def baseStart_427921 : Nat := 118140960795 + 427921 * 2 ^ 59
def prefixEnd_427921 : Nat := 4983230072969 + 3 ^ 40 * 427921 * 2
def baseEnd_427921 : Nat := 73243051717575163606511

theorem tailTrace_427921 : CollatzResearch.WordTrace tailWord_427921 prefixEnd_427921 73243051717575163606511 := by
  unfold tailWord_427921
  simp only [CollatzResearch.WordTrace]
  refine ⟨15607561082722774933467617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10405040721815183288978411 15607561082722774933467617)
  ·
    refine ⟨11705670812042081200100713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15607561082722774933467617 11705670812042081200100713)
    ·
      refine ⟨8779253109031560900075535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11705670812042081200100713 8779253109031560900075535)
      ·
        refine ⟨13168879663547341350113303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8779253109031560900075535 13168879663547341350113303)
        ·
          refine ⟨19753319495321012025169955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13168879663547341350113303 19753319495321012025169955)
          ·
            refine ⟨29629979242981518037754933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19753319495321012025169955 29629979242981518037754933)
            ·
              refine ⟨2777810554029517316039525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29629979242981518037754933 2777810554029517316039525)
              ·
                refine ⟨520839478880534496757411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2777810554029517316039525 520839478880534496757411)
                ·
                  refine ⟨781259218320801745136117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 520839478880534496757411 781259218320801745136117)
                  ·
                    refine ⟨73243051717575163606511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 781259218320801745136117 73243051717575163606511)
                    ·
                      rfl

theorem cell23_427921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 5].length) (baseStart_427921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427921 prefixEnd_427921 := by exact prefixLift 427921
  have htrace : WordTrace (prefixWord ++ tailWord_427921) baseStart_427921 baseEnd_427921 := by
    simpa [prefixWord, tailWord_427921, baseEnd_427921] using wordTrace_append hprefix tailTrace_427921
  have hstable : (prefixWord ++ tailWord_427921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427921).length < 2 ^ (prefixWord ++ tailWord_427921).sum := by decide
  have hdescent : baseEnd_427921 < baseStart_427921 := by decide
  rcases family_descends (prefixWord ++ tailWord_427921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427951 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 4, 4]
def baseStart_427951 : Nat := 118140960795 + 427951 * 2 ^ 59
def prefixEnd_427951 : Nat := 4983230072969 + 3 ^ 40 * 427951 * 2
def baseEnd_427951 : Nat := 73248186524120124481465

theorem tailTrace_427951 : CollatzResearch.WordTrace tailWord_427951 prefixEnd_427951 73248186524120124481465 := by
  unfold tailWord_427951
  simp only [CollatzResearch.WordTrace]
  refine ⟨15608655272614090057059707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10405770181742726704706471 15608655272614090057059707)
  ·
    refine ⟨23412982908921135085589561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15608655272614090057059707 23412982908921135085589561)
    ·
      refine ⟨17559737181690851314192171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23412982908921135085589561 17559737181690851314192171)
      ·
        refine ⟨26339605772536276971288257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17559737181690851314192171 26339605772536276971288257)
        ·
          refine ⟨19754704329402207728466193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26339605772536276971288257 19754704329402207728466193)
          ·
            refine ⟨14816028247051655796349645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19754704329402207728466193 14816028247051655796349645)
            ·
              refine ⟨5556010592644370923631117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14816028247051655796349645 5556010592644370923631117)
              ·
                refine ⟨2083503972241639096361669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5556010592644370923631117 2083503972241639096361669)
                ·
                  refine ⟨390656994795307330567813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2083503972241639096361669 390656994795307330567813)
                  ·
                    refine ⟨73248186524120124481465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 390656994795307330567813 73248186524120124481465)
                    ·
                      rfl

theorem cell23_427951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 4].length) (baseStart_427951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427951 prefixEnd_427951 := by exact prefixLift 427951
  have htrace : WordTrace (prefixWord ++ tailWord_427951) baseStart_427951 baseEnd_427951 := by
    simpa [prefixWord, tailWord_427951, baseEnd_427951] using wordTrace_append hprefix tailTrace_427951
  have hstable : (prefixWord ++ tailWord_427951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427951).length < 2 ^ (prefixWord ++ tailWord_427951).sum := by decide
  have hdescent : baseEnd_427951 < baseStart_427951 := by decide
  rcases family_descends (prefixWord ++ tailWord_427951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427961 : List Nat := [1, 2, 1, 4, 2, 1, 1, 4, 1, 1, 5]
def baseStart_427961 : Nat := 118140960795 + 427961 * 2 ^ 59
def prefixEnd_427961 : Nat := 4983230072969 + 3 ^ 40 * 427961 * 2
def baseEnd_427961 : Nat := 219749694378905334319349

theorem tailTrace_427961 : CollatzResearch.WordTrace tailWord_427961 prefixEnd_427961 219749694378905334319349 := by
  unfold tailWord_427961
  simp only [CollatzResearch.WordTrace]
  refine ⟨15609020002577861764923737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10406013335051907843282491 15609020002577861764923737)
  ·
    refine ⟨11706765001933396323692803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15609020002577861764923737 11706765001933396323692803)
    ·
      refine ⟨17560147502900094485539205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11706765001933396323692803 17560147502900094485539205)
      ·
        refine ⟨3292527656793767716038601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17560147502900094485539205 3292527656793767716038601)
        ·
          refine ⟨2469395742595325787028951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3292527656793767716038601 2469395742595325787028951)
          ·
            refine ⟨3704093613892988680543427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2469395742595325787028951 3704093613892988680543427)
            ·
              refine ⟨5556140420839483020815141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3704093613892988680543427 5556140420839483020815141)
              ·
                refine ⟨1041776328907403066402839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5556140420839483020815141 1041776328907403066402839)
                ·
                  refine ⟨1562664493361104599604259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1041776328907403066402839 1562664493361104599604259)
                  ·
                    refine ⟨2343996740041656899406389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1562664493361104599604259 2343996740041656899406389)
                    ·
                      refine ⟨219749694378905334319349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2343996740041656899406389 219749694378905334319349)
                      ·
                        rfl

theorem cell23_427961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_427961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427961 prefixEnd_427961 := by exact prefixLift 427961
  have htrace : WordTrace (prefixWord ++ tailWord_427961) baseStart_427961 baseEnd_427961 := by
    simpa [prefixWord, tailWord_427961, baseEnd_427961] using wordTrace_append hprefix tailTrace_427961
  have hstable : (prefixWord ++ tailWord_427961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427961).length < 2 ^ (prefixWord ++ tailWord_427961).sum := by decide
  have hdescent : baseEnd_427961 < baseStart_427961 := by decide
  rcases family_descends (prefixWord ++ tailWord_427961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427968 : List Nat := [2, 1, 1, 2, 3, 2, 3, 3, 2, 4]
def baseStart_427968 : Nat := 118140960795 + 427968 * 2 ^ 59
def prefixEnd_427968 : Nat := 4983230072969 + 3 ^ 40 * 427968 * 2
def baseEnd_427968 : Nat := 73251096247828935643939

theorem tailTrace_427968 : CollatzResearch.WordTrace tailWord_427968 prefixEnd_427968 73251096247828935643939 := by
  unfold tailWord_427968
  simp only [CollatzResearch.WordTrace]
  refine ⟨7804637656776250980214279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10406183542368334640285705 7804637656776250980214279)
  ·
    refine ⟨11706956485164376470321419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7804637656776250980214279 11706956485164376470321419)
    ·
      refine ⟨17560434727746564705482129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11706956485164376470321419 17560434727746564705482129)
      ·
        refine ⟨13170326045809923529111597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17560434727746564705482129 13170326045809923529111597)
        ·
          refine ⟨4938872267178721323416849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13170326045809923529111597 4938872267178721323416849)
          ·
            refine ⟨3704154200384040992562637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4938872267178721323416849 3704154200384040992562637)
            ·
              refine ⟨1389057825144015372210989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3704154200384040992562637 1389057825144015372210989)
              ·
                refine ⟨520896684429005764579121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1389057825144015372210989 520896684429005764579121)
                ·
                  refine ⟨390672513321754323434341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 520896684429005764579121 390672513321754323434341)
                  ·
                    refine ⟨73251096247828935643939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 390672513321754323434341 73251096247828935643939)
                    ·
                      rfl

theorem cell23_427968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 2, 4].length) (baseStart_427968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427968 prefixEnd_427968 := by exact prefixLift 427968
  have htrace : WordTrace (prefixWord ++ tailWord_427968) baseStart_427968 baseEnd_427968 := by
    simpa [prefixWord, tailWord_427968, baseEnd_427968] using wordTrace_append hprefix tailTrace_427968
  have hstable : (prefixWord ++ tailWord_427968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427968).length < 2 ^ (prefixWord ++ tailWord_427968).sum := by decide
  have hdescent : baseEnd_427968 < baseStart_427968 := by decide
  rcases family_descends (prefixWord ++ tailWord_427968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427988 : List Nat := [2, 4, 1, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_427988 : Nat := 118140960795 + 427988 * 2 ^ 59
def prefixEnd_427988 : Nat := 4983230072969 + 3 ^ 40 * 427988 * 2
def baseEnd_427988 : Nat := 219763558356576728681725

theorem tailTrace_427988 : CollatzResearch.WordTrace tailWord_427988 prefixEnd_427988 219763558356576728681725 := by
  unfold tailWord_427988
  simp only [CollatzResearch.WordTrace]
  refine ⟨7805002386740022688078309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10406669848986696917437745 7805002386740022688078309)
  ·
    refine ⟨1463437947513754254014683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7805002386740022688078309 1463437947513754254014683)
    ·
      refine ⟨2195156921270631381022025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1463437947513754254014683 2195156921270631381022025)
      ·
        refine ⟨1646367690952973535766519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2195156921270631381022025 1646367690952973535766519)
        ·
          refine ⟨2469551536429460303649779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1646367690952973535766519 2469551536429460303649779)
          ·
            refine ⟨3704327304644190455474669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2469551536429460303649779 3704327304644190455474669)
            ·
              refine ⟨1389122739241571420803001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3704327304644190455474669 1389122739241571420803001)
              ·
                refine ⟨1041842054431178565602251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1389122739241571420803001 1041842054431178565602251)
                ·
                  refine ⟨1562763081646767848403377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1041842054431178565602251 1562763081646767848403377)
                  ·
                    refine ⟨1172072311235075886302533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1562763081646767848403377 1172072311235075886302533)
                    ·
                      refine ⟨219763558356576728681725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1172072311235075886302533 219763558356576728681725)
                      ·
                        rfl

theorem cell23_427988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_427988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427988 prefixEnd_427988 := by exact prefixLift 427988
  have htrace : WordTrace (prefixWord ++ tailWord_427988) baseStart_427988 baseEnd_427988 := by
    simpa [prefixWord, tailWord_427988, baseEnd_427988] using wordTrace_append hprefix tailTrace_427988
  have hstable : (prefixWord ++ tailWord_427988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427988).length < 2 ^ (prefixWord ++ tailWord_427988).sum := by decide
  have hdescent : baseEnd_427988 < baseStart_427988 := by decide
  rcases family_descends (prefixWord ++ tailWord_427988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427992 : List Nat := [2, 1, 2, 2, 2, 2, 2, 5, 1, 2, 2]
def baseStart_427992 : Nat := 118140960795 + 427992 * 2 ^ 59
def prefixEnd_427992 : Nat := 4983230072969 + 3 ^ 40 * 427992 * 2
def baseEnd_427992 : Nat := 219765612279194713031707

theorem tailTrace_427992 : CollatzResearch.WordTrace tailWord_427992 prefixEnd_427992 219765612279194713031707 := by
  unfold tailWord_427992
  simp only [CollatzResearch.WordTrace]
  refine ⟨7805075332732777029651115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10406767110310369372868153 7805075332732777029651115)
  ·
    refine ⟨11707612999099165544476673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7805075332732777029651115 11707612999099165544476673)
    ·
      refine ⟨8780709749324374158357505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11707612999099165544476673 8780709749324374158357505)
      ·
        refine ⟨6585532311993280618768129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8780709749324374158357505 6585532311993280618768129)
        ·
          refine ⟨4939149233994960464076097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6585532311993280618768129 4939149233994960464076097)
          ·
            refine ⟨3704361925496220348057073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4939149233994960464076097 3704361925496220348057073)
            ·
              refine ⟨2778271444122165261042805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3704361925496220348057073 2778271444122165261042805)
              ·
                refine ⟨260462947886452993222763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2778271444122165261042805 260462947886452993222763)
                ·
                  refine ⟨390694421829679489834145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 260462947886452993222763 390694421829679489834145)
                  ·
                    refine ⟨293020816372259617375609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 390694421829679489834145 293020816372259617375609)
                    ·
                      refine ⟨219765612279194713031707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 293020816372259617375609 219765612279194713031707)
                      ·
                        rfl

theorem cell23_427992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 1, 2, 2].length) (baseStart_427992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_427992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_427992 prefixEnd_427992 := by exact prefixLift 427992
  have htrace : WordTrace (prefixWord ++ tailWord_427992) baseStart_427992 baseEnd_427992 := by
    simpa [prefixWord, tailWord_427992, baseEnd_427992] using wordTrace_append hprefix tailTrace_427992
  have hstable : (prefixWord ++ tailWord_427992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427992).length < 2 ^ (prefixWord ++ tailWord_427992).sum := by decide
  have hdescent : baseEnd_427992 < baseStart_427992 := by decide
  rcases family_descends (prefixWord ++ tailWord_427992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428025 : List Nat := [1, 2, 1, 3, 1, 4, 2, 3, 2, 1, 3]
def baseStart_428025 : Nat := 118140960795 + 428025 * 2 ^ 59
def prefixEnd_428025 : Nat := 4983230072969 + 3 ^ 40 * 428025 * 2
def baseEnd_428025 : Nat := 219782557140793083919055

theorem tailTrace_428025 : CollatzResearch.WordTrace tailWord_428025 prefixEnd_428025 219782557140793083919055 := by
  unfold tailWord_428025
  simp only [CollatzResearch.WordTrace]
  refine ⟨15611354274346000695253529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10407569516230667130169019 15611354274346000695253529)
  ·
    refine ⟨11708515705759500521440147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15611354274346000695253529 11708515705759500521440147)
    ·
      refine ⟨17562773558639250782160221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11708515705759500521440147 17562773558639250782160221)
      ·
        refine ⟨6586040084489719043310083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17562773558639250782160221 6586040084489719043310083)
        ·
          refine ⟨9879060126734578564965125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6586040084489719043310083 9879060126734578564965125)
          ·
            refine ⟨1852323773762733480930961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9879060126734578564965125 1852323773762733480930961)
            ·
              refine ⟨1389242830322050110698221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1852323773762733480930961 1389242830322050110698221)
              ·
                refine ⟨520966061370768791511833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1389242830322050110698221 520966061370768791511833)
                ·
                  refine ⟨390724546028076593633875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 520966061370768791511833 390724546028076593633875)
                  ·
                    refine ⟨586086819042114890450813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 390724546028076593633875 586086819042114890450813)
                    ·
                      refine ⟨219782557140793083919055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 586086819042114890450813 219782557140793083919055)
                      ·
                        rfl

theorem cell23_428025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_428025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428025 prefixEnd_428025 := by exact prefixLift 428025
  have htrace : WordTrace (prefixWord ++ tailWord_428025) baseStart_428025 baseEnd_428025 := by
    simpa [prefixWord, tailWord_428025, baseEnd_428025] using wordTrace_append hprefix tailTrace_428025
  have hstable : (prefixWord ++ tailWord_428025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428025).length < 2 ^ (prefixWord ++ tailWord_428025).sum := by decide
  have hdescent : baseEnd_428025 < baseStart_428025 := by decide
  rcases family_descends (prefixWord ++ tailWord_428025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428051 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 5]
def baseStart_428051 : Nat := 118140960795 + 428051 * 2 ^ 59
def prefixEnd_428051 : Nat := 4983230072969 + 3 ^ 40 * 428051 * 2
def baseEnd_428051 : Nat := 219795907637809982193935

theorem tailTrace_428051 : CollatzResearch.WordTrace tailWord_428051 prefixEnd_428051 219795907637809982193935 := by
  unfold tailWord_428051
  simp only [CollatzResearch.WordTrace]
  refine ⟨15612302572251807135700007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10408201714834538090466671 15612302572251807135700007)
  ·
    refine ⟨23418453858377710703550011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15612302572251807135700007 23418453858377710703550011)
    ·
      refine ⟨35127680787566566055325017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23418453858377710703550011 35127680787566566055325017)
      ·
        refine ⟨26345760590674924541493763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35127680787566566055325017 26345760590674924541493763)
        ·
          refine ⟨39518640886012386812240645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26345760590674924541493763 39518640886012386812240645)
          ·
            refine ⟨7409745166127322527295121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39518640886012386812240645 7409745166127322527295121)
            ·
              refine ⟨5557308874595491895471341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7409745166127322527295121 5557308874595491895471341)
              ·
                refine ⟨2083990827973309460801753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5557308874595491895471341 2083990827973309460801753)
                ·
                  refine ⟨1562993120979982095601315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2083990827973309460801753 1562993120979982095601315)
                  ·
                    refine ⟨2344489681469973143401973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1562993120979982095601315 2344489681469973143401973)
                    ·
                      refine ⟨219795907637809982193935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2344489681469973143401973 219795907637809982193935)
                      ·
                        rfl

theorem cell23_428051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 5].length) (baseStart_428051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428051 prefixEnd_428051 := by exact prefixLift 428051
  have htrace : WordTrace (prefixWord ++ tailWord_428051) baseStart_428051 baseEnd_428051 := by
    simpa [prefixWord, tailWord_428051, baseEnd_428051] using wordTrace_append hprefix tailTrace_428051
  have hstable : (prefixWord ++ tailWord_428051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428051).length < 2 ^ (prefixWord ++ tailWord_428051).sum := by decide
  have hdescent : baseEnd_428051 < baseStart_428051 := by decide
  rcases family_descends (prefixWord ++ tailWord_428051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428082 : List Nat := [3, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2]
def baseStart_428082 : Nat := 118140960795 + 428082 * 2 ^ 59
def prefixEnd_428082 : Nat := 4983230072969 + 3 ^ 40 * 428082 * 2
def baseEnd_428082 : Nat := 219811825538099360906293

theorem tailTrace_428082 : CollatzResearch.WordTrace tailWord_428082 prefixEnd_428082 219811825538099360906293 := by
  unfold tailWord_428082
  simp only [CollatzResearch.WordTrace]
  refine ⟨3903358308784874857519625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10408955490092999620052333 3903358308784874857519625)
  ·
    refine ⟨2927518731588656143139719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3903358308784874857519625 2927518731588656143139719)
    ·
      refine ⟨4391278097382984214709579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2927518731588656143139719 4391278097382984214709579)
      ·
        refine ⟨6586917146074476322064369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4391278097382984214709579 6586917146074476322064369)
        ·
          refine ⟨4940187859555857241548277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6586917146074476322064369 4940187859555857241548277)
          ·
            refine ⟨463142611833361616395151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4940187859555857241548277 463142611833361616395151)
            ·
              refine ⟨694713917750042424592727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463142611833361616395151 694713917750042424592727)
              ·
                refine ⟨1042070876625063636889091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 694713917750042424592727 1042070876625063636889091)
                ·
                  refine ⟨1563106314937595455333637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1042070876625063636889091 1563106314937595455333637)
                  ·
                    refine ⟨293082434050799147875057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1563106314937595455333637 293082434050799147875057)
                    ·
                      refine ⟨219811825538099360906293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 293082434050799147875057 219811825538099360906293)
                      ·
                        rfl

theorem cell23_428082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2].length) (baseStart_428082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428082 prefixEnd_428082 := by exact prefixLift 428082
  have htrace : WordTrace (prefixWord ++ tailWord_428082) baseStart_428082 baseEnd_428082 := by
    simpa [prefixWord, tailWord_428082, baseEnd_428082] using wordTrace_append hprefix tailTrace_428082
  have hstable : (prefixWord ++ tailWord_428082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428082).length < 2 ^ (prefixWord ++ tailWord_428082).sum := by decide
  have hdescent : baseEnd_428082 < baseStart_428082 := by decide
  rcases family_descends (prefixWord ++ tailWord_428082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428111 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 5]
def baseStart_428111 : Nat := 118140960795 + 428111 * 2 ^ 59
def prefixEnd_428111 : Nat := 4983230072969 + 3 ^ 40 * 428111 * 2
def baseEnd_428111 : Nat := 219826716477079747443659

theorem tailTrace_428111 : CollatzResearch.WordTrace tailWord_428111 prefixEnd_428111 219826716477079747443659 := by
  unfold tailWord_428111
  simp only [CollatzResearch.WordTrace]
  refine ⟨15614490952034437382884187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10409660634689624921922791 15614490952034437382884187)
  ·
    refine ⟨23421736428051656074326281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15614490952034437382884187 23421736428051656074326281)
    ·
      refine ⟨17566302321038742055744711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23421736428051656074326281 17566302321038742055744711)
      ·
        refine ⟨26349453481558113083617067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17566302321038742055744711 26349453481558113083617067)
        ·
          refine ⟨39524180222337169625425601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26349453481558113083617067 39524180222337169625425601)
          ·
            refine ⟨29643135166752877219069201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39524180222337169625425601 29643135166752877219069201)
            ·
              refine ⟨22232351375064657914301901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29643135166752877219069201 22232351375064657914301901)
              ·
                refine ⟨8337131765649246717863213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22232351375064657914301901 8337131765649246717863213)
                ·
                  refine ⟨3126424412118467519198705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8337131765649246717863213 3126424412118467519198705)
                  ·
                    refine ⟨2344818309088850639399029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3126424412118467519198705 2344818309088850639399029)
                    ·
                      refine ⟨219826716477079747443659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2344818309088850639399029 219826716477079747443659)
                      ·
                        rfl

theorem cell23_428111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_428111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428111 prefixEnd_428111 := by exact prefixLift 428111
  have htrace : WordTrace (prefixWord ++ tailWord_428111) baseStart_428111 baseEnd_428111 := by
    simpa [prefixWord, tailWord_428111, baseEnd_428111] using wordTrace_append hprefix tailTrace_428111
  have hstable : (prefixWord ++ tailWord_428111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428111).length < 2 ^ (prefixWord ++ tailWord_428111).sum := by decide
  have hdescent : baseEnd_428111 < baseStart_428111 := by decide
  rcases family_descends (prefixWord ++ tailWord_428111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428128 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 5]
def baseStart_428128 : Nat := 118140960795 + 428128 * 2 ^ 59
def prefixEnd_428128 : Nat := 4983230072969 + 3 ^ 40 * 428128 * 2
def baseEnd_428128 : Nat := 219835445648206180931081

theorem tailTrace_428128 : CollatzResearch.WordTrace tailWord_428128 prefixEnd_428128 219835445648206180931081 := by
  unfold tailWord_428128
  simp only [CollatzResearch.WordTrace]
  refine ⟨7807555496486424643126519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10410073995315232857502025 7807555496486424643126519)
  ·
    refine ⟨11711333244729636964689779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7807555496486424643126519 11711333244729636964689779)
    ·
      refine ⟨17566999867094455447034669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11711333244729636964689779 17566999867094455447034669)
      ·
        refine ⟨6587624950160420792638001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17566999867094455447034669 6587624950160420792638001)
        ·
          refine ⟨4940718712620315594478501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6587624950160420792638001 4940718712620315594478501)
          ·
            refine ⟨926384758616309173964719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4940718712620315594478501 926384758616309173964719)
            ·
              refine ⟨1389577137924463760947079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926384758616309173964719 1389577137924463760947079)
              ·
                refine ⟨2084365706886695641420619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1389577137924463760947079 2084365706886695641420619)
                ·
                  refine ⟨3126548560330043462130929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2084365706886695641420619 3126548560330043462130929)
                  ·
                    refine ⟨2344911420247532596598197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3126548560330043462130929 2344911420247532596598197)
                    ·
                      refine ⟨219835445648206180931081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2344911420247532596598197 219835445648206180931081)
                      ·
                        rfl

theorem cell23_428128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_428128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428128 prefixEnd_428128 := by exact prefixLift 428128
  have htrace : WordTrace (prefixWord ++ tailWord_428128) baseStart_428128 baseEnd_428128 := by
    simpa [prefixWord, tailWord_428128, baseEnd_428128] using wordTrace_append hprefix tailTrace_428128
  have hstable : (prefixWord ++ tailWord_428128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428128).length < 2 ^ (prefixWord ++ tailWord_428128).sum := by decide
  have hdescent : baseEnd_428128 < baseStart_428128 := by decide
  rcases family_descends (prefixWord ++ tailWord_428128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428206 : List Nat := [4, 1, 4, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_428206 : Nat := 118140960795 + 428206 * 2 ^ 59
def prefixEnd_428206 : Nat := 4983230072969 + 3 ^ 40 * 428206 * 2
def baseEnd_428206 : Nat := 219875497139256875755723

theorem tailTrace_428206 : CollatzResearch.WordTrace tailWord_428206 prefixEnd_428206 219875497139256875755723 := by
  unfold tailWord_428206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1952244485836283575949059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10411970591126845738394981 1952244485836283575949059)
  ·
    refine ⟨2928366728754425363923589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1952244485836283575949059 2928366728754425363923589)
    ·
      refine ⟨549068761641454755735673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2928366728754425363923589 549068761641454755735673)
      ·
        refine ⟨411801571231091066801755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 549068761641454755735673 411801571231091066801755)
        ·
          refine ⟨617702356846636600202633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411801571231091066801755 617702356846636600202633)
          ·
            refine ⟨463276767634977450151975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 617702356846636600202633 463276767634977450151975)
            ·
              refine ⟨694915151452466175227963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463276767634977450151975 694915151452466175227963)
              ·
                refine ⟨1042372727178699262841945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 694915151452466175227963 1042372727178699262841945)
                ·
                  refine ⟨781779545384024447131459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1042372727178699262841945 781779545384024447131459)
                  ·
                    refine ⟨1172669318076036670697189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 781779545384024447131459 1172669318076036670697189)
                    ·
                      refine ⟨219875497139256875755723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1172669318076036670697189 219875497139256875755723)
                      ·
                        rfl

theorem cell23_428206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_428206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428206 prefixEnd_428206 := by exact prefixLift 428206
  have htrace : WordTrace (prefixWord ++ tailWord_428206) baseStart_428206 baseEnd_428206 := by
    simpa [prefixWord, tailWord_428206, baseEnd_428206] using wordTrace_append hprefix tailTrace_428206
  have hstable : (prefixWord ++ tailWord_428206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428206).length < 2 ^ (prefixWord ++ tailWord_428206).sum := by decide
  have hdescent : baseEnd_428206 < baseStart_428206 := by decide
  rcases family_descends (prefixWord ++ tailWord_428206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428209 : List Nat := [1, 2, 2, 5, 2, 2, 1, 1, 2, 2, 3]
def baseStart_428209 : Nat := 118140960795 + 428209 * 2 ^ 59
def prefixEnd_428209 : Nat := 4983230072969 + 3 ^ 40 * 428209 * 2
def baseEnd_428209 : Nat := 219877037581220364018209

theorem tailTrace_428209 : CollatzResearch.WordTrace tailWord_428209 prefixEnd_428209 219877037581220364018209 := by
  unfold tailWord_428209
  simp only [CollatzResearch.WordTrace]
  refine ⟨15618065305679400119951681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10412043537119600079967787 15618065305679400119951681)
  ·
    refine ⟨11713548979259550089963761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15618065305679400119951681 11713548979259550089963761)
    ·
      refine ⟨8785161734444662567472821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11713548979259550089963761 8785161734444662567472821)
      ·
        refine ⟨823608912604187115700577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8785161734444662567472821 823608912604187115700577)
        ·
          refine ⟨617706684453140336775433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 823608912604187115700577 617706684453140336775433)
          ·
            refine ⟨463280013339855252581575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 617706684453140336775433 463280013339855252581575)
            ·
              refine ⟨694920020009782878872363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463280013339855252581575 694920020009782878872363)
              ·
                refine ⟨1042380030014674318308545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 694920020009782878872363 1042380030014674318308545)
                ·
                  refine ⟨781785022511005738731409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1042380030014674318308545 781785022511005738731409)
                  ·
                    refine ⟨586338766883254304048557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 781785022511005738731409 586338766883254304048557)
                    ·
                      refine ⟨219877037581220364018209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 586338766883254304048557 219877037581220364018209)
                      ·
                        rfl

theorem cell23_428209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_428209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428209 prefixEnd_428209 := by exact prefixLift 428209
  have htrace : WordTrace (prefixWord ++ tailWord_428209) baseStart_428209 baseEnd_428209 := by
    simpa [prefixWord, tailWord_428209, baseEnd_428209] using wordTrace_append hprefix tailTrace_428209
  have hstable : (prefixWord ++ tailWord_428209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428209).length < 2 ^ (prefixWord ++ tailWord_428209).sum := by decide
  have hdescent : baseEnd_428209 < baseStart_428209 := by decide
  rcases family_descends (prefixWord ++ tailWord_428209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428259 : List Nat := [1, 1, 1, 8, 1, 1, 2, 2, 1, 5]
def baseStart_428259 : Nat := 118140960795 + 428259 * 2 ^ 59
def prefixEnd_428259 : Nat := 4983230072969 + 3 ^ 40 * 428259 * 2
def baseEnd_428259 : Nat := 73300903871315056130993

theorem tailTrace_428259 : CollatzResearch.WordTrace tailWord_428259 prefixEnd_428259 73300903871315056130993 := by
  unfold tailWord_428259
  simp only [CollatzResearch.WordTrace]
  refine ⟨15619888955498258659271831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10413259303665505772847887 15619888955498258659271831)
  ·
    refine ⟨23429833433247387988907747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15619888955498258659271831 23429833433247387988907747)
    ·
      refine ⟨35144750149871081983361621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23429833433247387988907747 35144750149871081983361621)
      ·
        refine ⟨411852540818801741992519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 35144750149871081983361621 411852540818801741992519)
        ·
          refine ⟨617778811228202612988779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411852540818801741992519 617778811228202612988779)
          ·
            refine ⟨926668216842303919483169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617778811228202612988779 926668216842303919483169)
            ·
              refine ⟨695001162631727939612377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 926668216842303919483169 695001162631727939612377)
              ·
                refine ⟨521250871973795954709283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 695001162631727939612377 521250871973795954709283)
                ·
                  refine ⟨781876307960693932063925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 521250871973795954709283 781876307960693932063925)
                  ·
                    refine ⟨73300903871315056130993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 781876307960693932063925 73300903871315056130993)
                    ·
                      rfl

theorem cell23_428259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 5].length) (baseStart_428259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428259 prefixEnd_428259 := by exact prefixLift 428259
  have htrace : WordTrace (prefixWord ++ tailWord_428259) baseStart_428259 baseEnd_428259 := by
    simpa [prefixWord, tailWord_428259, baseEnd_428259] using wordTrace_append hprefix tailTrace_428259
  have hstable : (prefixWord ++ tailWord_428259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428259).length < 2 ^ (prefixWord ++ tailWord_428259).sum := by decide
  have hdescent : baseEnd_428259 < baseStart_428259 := by decide
  rcases family_descends (prefixWord ++ tailWord_428259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428268 : List Nat := [2, 2, 1, 1, 2, 3, 3, 9]
def baseStart_428268 : Nat := 118140960795 + 428268 * 2 ^ 59
def prefixEnd_428268 : Nat := 4983230072969 + 3 ^ 40 * 428268 * 2
def baseEnd_428268 : Nat := 8144716034808727154831

theorem tailTrace_428268 : CollatzResearch.WordTrace tailWord_428268 prefixEnd_428268 8144716034808727154831 := by
  unfold tailWord_428268
  simp only [CollatzResearch.WordTrace]
  refine ⟨7810108606232826598174729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10413478141643768797566305 7810108606232826598174729)
  ·
    refine ⟨5857581454674619948631047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7810108606232826598174729 5857581454674619948631047)
    ·
      refine ⟨8786372182011929922946571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5857581454674619948631047 8786372182011929922946571)
      ·
        refine ⟨13179558273017894884419857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8786372182011929922946571 13179558273017894884419857)
        ·
          refine ⟨9884668704763421163314893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13179558273017894884419857 9884668704763421163314893)
          ·
            refine ⟨3706750764286282936243085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9884668704763421163314893 3706750764286282936243085)
            ·
              refine ⟨1390031536607356101091157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3706750764286282936243085 1390031536607356101091157)
              ·
                refine ⟨8144716034808727154831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1390031536607356101091157 8144716034808727154831)
                ·
                  rfl

theorem cell23_428268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 9].length) (baseStart_428268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428268 prefixEnd_428268 := by exact prefixLift 428268
  have htrace : WordTrace (prefixWord ++ tailWord_428268) baseStart_428268 baseEnd_428268 := by
    simpa [prefixWord, tailWord_428268, baseEnd_428268] using wordTrace_append hprefix tailTrace_428268
  have hstable : (prefixWord ++ tailWord_428268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428268).length < 2 ^ (prefixWord ++ tailWord_428268).sum := by decide
  have hdescent : baseEnd_428268 < baseStart_428268 := by decide
  rcases family_descends (prefixWord ++ tailWord_428268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428282 : List Nat := [3, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3]
def baseStart_428282 : Nat := 118140960795 + 428282 * 2 ^ 59
def prefixEnd_428282 : Nat := 4983230072969 + 3 ^ 40 * 428282 * 2
def baseEnd_428282 : Nat := 219914521668998578405373

theorem tailTrace_428282 : CollatzResearch.WordTrace tailWord_428282 prefixEnd_428282 219914521668998578405373 := by
  unfold tailWord_428282
  simp only [CollatzResearch.WordTrace]
  refine ⟨3905181958603733396839775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10413818556276622391572733 3905181958603733396839775)
  ·
    refine ⟨5857772937905600095259663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3905181958603733396839775 5857772937905600095259663)
    ·
      refine ⟨8786659406858400142889495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5857772937905600095259663 8786659406858400142889495)
      ·
        refine ⟨13179989110287600214334243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8786659406858400142889495 13179989110287600214334243)
        ·
          refine ⟨19769983665431400321501365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13179989110287600214334243 19769983665431400321501365)
          ·
            refine ⟨1853435968634193780140753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19769983665431400321501365 1853435968634193780140753)
            ·
              refine ⟨1390076976475645335105565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1853435968634193780140753 1390076976475645335105565)
              ·
                refine ⟨521278866178367000664587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1390076976475645335105565 521278866178367000664587)
                ·
                  refine ⟨781918299267550500996881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 521278866178367000664587 781918299267550500996881)
                  ·
                    refine ⟨586438724450662875747661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 781918299267550500996881 586438724450662875747661)
                    ·
                      refine ⟨219914521668998578405373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 586438724450662875747661 219914521668998578405373)
                      ·
                        rfl

theorem cell23_428282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3].length) (baseStart_428282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428282 prefixEnd_428282 := by exact prefixLift 428282
  have htrace : WordTrace (prefixWord ++ tailWord_428282) baseStart_428282 baseEnd_428282 := by
    simpa [prefixWord, tailWord_428282, baseEnd_428282] using wordTrace_append hprefix tailTrace_428282
  have hstable : (prefixWord ++ tailWord_428282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428282).length < 2 ^ (prefixWord ++ tailWord_428282).sum := by decide
  have hdescent : baseEnd_428282 < baseStart_428282 := by decide
  rcases family_descends (prefixWord ++ tailWord_428282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428296 : List Nat := [2, 1, 3, 2, 3, 3, 1, 1, 3, 2, 2]
def baseStart_428296 : Nat := 118140960795 + 428296 * 2 ^ 59
def prefixEnd_428296 : Nat := 4983230072969 + 3 ^ 40 * 428296 * 2
def baseEnd_428296 : Nat := 219921710398161523630309

theorem tailTrace_428296 : CollatzResearch.WordTrace tailWord_428296 prefixEnd_428296 219921710398161523630309 := by
  unfold tailWord_428296
  simp only [CollatzResearch.WordTrace]
  refine ⟨7810619228182106989184371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10414158970909475985579161 7810619228182106989184371)
  ·
    refine ⟨11715928842273160483776557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7810619228182106989184371 11715928842273160483776557)
    ·
      refine ⟨4393473315852435181416209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11715928842273160483776557 4393473315852435181416209)
      ·
        refine ⟨3295104986889326386062157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4393473315852435181416209 3295104986889326386062157)
        ·
          refine ⟨1235664370083497394773309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3295104986889326386062157 1235664370083497394773309)
          ·
            refine ⟨463374138781311523039991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1235664370083497394773309 463374138781311523039991)
            ·
              refine ⟨695061208171967284559987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463374138781311523039991 695061208171967284559987)
              ·
                refine ⟨1042591812257950926839981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 695061208171967284559987 1042591812257950926839981)
                ·
                  refine ⟨390971929596731597564993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1042591812257950926839981 390971929596731597564993)
                  ·
                    refine ⟨293228947197548698173745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 390971929596731597564993 293228947197548698173745)
                    ·
                      refine ⟨219921710398161523630309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 293228947197548698173745 219921710398161523630309)
                      ·
                        rfl

theorem cell23_428296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_428296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428296 prefixEnd_428296 := by exact prefixLift 428296
  have htrace : WordTrace (prefixWord ++ tailWord_428296) baseStart_428296 baseEnd_428296 := by
    simpa [prefixWord, tailWord_428296, baseEnd_428296] using wordTrace_append hprefix tailTrace_428296
  have hstable : (prefixWord ++ tailWord_428296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428296).length < 2 ^ (prefixWord ++ tailWord_428296).sum := by decide
  have hdescent : baseEnd_428296 < baseStart_428296 := by decide
  rcases family_descends (prefixWord ++ tailWord_428296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428333 : List Nat := [1, 5, 3, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_428333 : Nat := 118140960795 + 428333 * 2 ^ 59
def prefixEnd_428333 : Nat := 4983230072969 + 3 ^ 40 * 428333 * 2
def baseEnd_428333 : Nat := 219940709182377878867639

theorem tailTrace_428333 : CollatzResearch.WordTrace tailWord_428333 prefixEnd_428333 219940709182377878867639 := by
  unfold tailWord_428333
  simp only [CollatzResearch.WordTrace]
  refine ⟨15622587957230169297465653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10415058638153446198310435 15622587957230169297465653)
  ·
    refine ⟨1464617620990328371637405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15622587957230169297465653 1464617620990328371637405)
    ·
      refine ⟨549231607871373139364027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1464617620990328371637405 549231607871373139364027)
      ·
        refine ⟨823847411807059709046041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549231607871373139364027 823847411807059709046041)
        ·
          refine ⟨617885558855294781784531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 823847411807059709046041 617885558855294781784531)
          ·
            refine ⟨926828338282942172676797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617885558855294781784531 926828338282942172676797)
            ·
              refine ⟨347560626856103314753799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 926828338282942172676797 347560626856103314753799)
              ·
                refine ⟨521340940284154972130699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347560626856103314753799 521340940284154972130699)
                ·
                  refine ⟨782011410426232458196049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 521340940284154972130699 782011410426232458196049)
                  ·
                    refine ⟨586508557819674343647037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 782011410426232458196049 586508557819674343647037)
                    ·
                      refine ⟨219940709182377878867639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 586508557819674343647037 219940709182377878867639)
                      ·
                        rfl

theorem cell23_428333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_428333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428333 prefixEnd_428333 := by exact prefixLift 428333
  have htrace : WordTrace (prefixWord ++ tailWord_428333) baseStart_428333 baseEnd_428333 := by
    simpa [prefixWord, tailWord_428333, baseEnd_428333] using wordTrace_append hprefix tailTrace_428333
  have hstable : (prefixWord ++ tailWord_428333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428333).length < 2 ^ (prefixWord ++ tailWord_428333).sum := by decide
  have hdescent : baseEnd_428333 < baseStart_428333 := by decide
  rcases family_descends (prefixWord ++ tailWord_428333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428355 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 3]
def baseStart_428355 : Nat := 118140960795 + 428355 * 2 ^ 59
def prefixEnd_428355 : Nat := 4983230072969 + 3 ^ 40 * 428355 * 2
def baseEnd_428355 : Nat := 219952005756776792792537

theorem tailTrace_428355 : CollatzResearch.WordTrace tailWord_428355 prefixEnd_428355 219952005756776792792537 := by
  unfold tailWord_428355
  simp only [CollatzResearch.WordTrace]
  refine ⟨15623390363150467054766519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10415593575433644703177679 15623390363150467054766519)
  ·
    refine ⟨23435085544725700582149779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15623390363150467054766519 23435085544725700582149779)
    ·
      refine ⟨35152628317088550873224669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23435085544725700582149779 35152628317088550873224669)
      ·
        refine ⟨13182235618908206577459251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35152628317088550873224669 13182235618908206577459251)
        ·
          refine ⟨19773353428362309866188877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13182235618908206577459251 19773353428362309866188877)
          ·
            refine ⟨7415007535635866199820829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19773353428362309866188877 7415007535635866199820829)
            ·
              refine ⟨2780627825863449824932811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7415007535635866199820829 2780627825863449824932811)
              ·
                refine ⟨4170941738795174737399217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2780627825863449824932811 4170941738795174737399217)
                ·
                  refine ⟨3128206304096381053049413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4170941738795174737399217 3128206304096381053049413)
                  ·
                    refine ⟨586538682018071447446765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3128206304096381053049413 586538682018071447446765)
                    ·
                      refine ⟨219952005756776792792537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 586538682018071447446765 219952005756776792792537)
                      ·
                        rfl

theorem cell23_428355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 3].length) (baseStart_428355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428355 prefixEnd_428355 := by exact prefixLift 428355
  have htrace : WordTrace (prefixWord ++ tailWord_428355) baseStart_428355 baseEnd_428355 := by
    simpa [prefixWord, tailWord_428355, baseEnd_428355] using wordTrace_append hprefix tailTrace_428355
  have hstable : (prefixWord ++ tailWord_428355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428355).length < 2 ^ (prefixWord ++ tailWord_428355).sum := by decide
  have hdescent : baseEnd_428355 < baseStart_428355 := by decide
  rcases family_descends (prefixWord ++ tailWord_428355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428369 : List Nat := [1, 2, 2, 1, 4, 3, 2, 1, 1, 4, 2]
def baseStart_428369 : Nat := 118140960795 + 428369 * 2 ^ 59
def prefixEnd_428369 : Nat := 4983230072969 + 3 ^ 40 * 428369 * 2
def baseEnd_428369 : Nat := 219959194485939738017473

theorem tailTrace_428369 : CollatzResearch.WordTrace tailWord_428369 prefixEnd_428369 219959194485939738017473 := by
  unfold tailWord_428369
  simp only [CollatzResearch.WordTrace]
  refine ⟨15623900985099747445776161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10415933990066498297184107 15623900985099747445776161)
  ·
    refine ⟨11717925738824810584332121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15623900985099747445776161 11717925738824810584332121)
    ·
      refine ⟨8788444304118607938249091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11717925738824810584332121 8788444304118607938249091)
      ·
        refine ⟨13182666456177911907373637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8788444304118607938249091 13182666456177911907373637)
        ·
          refine ⟨2471749960533358482632557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13182666456177911907373637 2471749960533358482632557)
          ·
            refine ⟨926906235200009430987209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2471749960533358482632557 926906235200009430987209)
            ·
              refine ⟨695179676400007073240407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 926906235200009430987209 695179676400007073240407)
              ·
                refine ⟨1042769514600010609860611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 695179676400007073240407 1042769514600010609860611)
                ·
                  refine ⟨1564154271900015914790917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1042769514600010609860611 1564154271900015914790917)
                  ·
                    refine ⟨293278925981252984023297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1564154271900015914790917 293278925981252984023297)
                    ·
                      refine ⟨219959194485939738017473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 293278925981252984023297 219959194485939738017473)
                      ·
                        rfl

theorem cell23_428369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 4, 2].length) (baseStart_428369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428369 prefixEnd_428369 := by exact prefixLift 428369
  have htrace : WordTrace (prefixWord ++ tailWord_428369) baseStart_428369 baseEnd_428369 := by
    simpa [prefixWord, tailWord_428369, baseEnd_428369] using wordTrace_append hprefix tailTrace_428369
  have hstable : (prefixWord ++ tailWord_428369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428369).length < 2 ^ (prefixWord ++ tailWord_428369).sum := by decide
  have hdescent : baseEnd_428369 < baseStart_428369 := by decide
  rcases family_descends (prefixWord ++ tailWord_428369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428375 : List Nat := [1, 1, 3, 2, 3, 1, 3, 2, 7]
def baseStart_428375 : Nat := 118140960795 + 428375 * 2 ^ 59
def prefixEnd_428375 : Nat := 4983230072969 + 3 ^ 40 * 428375 * 2
def baseEnd_428375 : Nat := 24440252818874079393605

theorem tailTrace_428375 : CollatzResearch.WordTrace tailWord_428375 prefixEnd_428375 24440252818874079393605 := by
  unfold tailWord_428375
  simp only [CollatzResearch.WordTrace]
  refine ⟨15624119823078010470494579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10416079882052006980329719 15624119823078010470494579)
  ·
    refine ⟨23436179734617015705741869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15624119823078010470494579 23436179734617015705741869)
    ·
      refine ⟨8788567400481380889653201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23436179734617015705741869 8788567400481380889653201)
      ·
        refine ⟨6591425550361035667239901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8788567400481380889653201 6591425550361035667239901)
        ·
          refine ⟨2471784581385388375214963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6591425550361035667239901 2471784581385388375214963)
          ·
            refine ⟨3707676872078082562822445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2471784581385388375214963 3707676872078082562822445)
            ·
              refine ⟨1390378827029280961058417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3707676872078082562822445 1390378827029280961058417)
              ·
                refine ⟨1042784120271960720793813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1390378827029280961058417 1042784120271960720793813)
                ·
                  refine ⟨24440252818874079393605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1042784120271960720793813 24440252818874079393605)
                  ·
                    rfl

theorem cell23_428375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 7].length) (baseStart_428375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428375 prefixEnd_428375 := by exact prefixLift 428375
  have htrace : WordTrace (prefixWord ++ tailWord_428375) baseStart_428375 baseEnd_428375 := by
    simpa [prefixWord, tailWord_428375, baseEnd_428375] using wordTrace_append hprefix tailTrace_428375
  have hstable : (prefixWord ++ tailWord_428375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428375).length < 2 ^ (prefixWord ++ tailWord_428375).sum := by decide
  have hdescent : baseEnd_428375 < baseStart_428375 := by decide
  rcases family_descends (prefixWord ++ tailWord_428375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428402 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 2, 3, 3]
def baseStart_428402 : Nat := 118140960795 + 428402 * 2 ^ 59
def prefixEnd_428402 : Nat := 4983230072969 + 3 ^ 40 * 428402 * 2
def baseEnd_428402 : Nat := 219976139347538108904821

theorem tailTrace_428402 : CollatzResearch.WordTrace tailWord_428402 prefixEnd_428402 219976139347538108904821 := by
  unfold tailWord_428402
  simp only [CollatzResearch.WordTrace]
  refine ⟨3906276148495048520431865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10416736395986796054484973 3906276148495048520431865)
  ·
    refine ⟨2929707111371286390323899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3906276148495048520431865 2929707111371286390323899)
    ·
      refine ⟨4394560667056929585485849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2929707111371286390323899 4394560667056929585485849)
      ·
        refine ⟨3295920500292697189114387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4394560667056929585485849 3295920500292697189114387)
        ·
          refine ⟨4943880750439045783671581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3295920500292697189114387 4943880750439045783671581)
          ·
            refine ⟨1853955281414642168876843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4943880750439045783671581 1853955281414642168876843)
            ·
              refine ⟨2780932922121963253315265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1853955281414642168876843 2780932922121963253315265)
              ·
                refine ⟨2085699691591472439986449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2780932922121963253315265 2085699691591472439986449)
                ·
                  refine ⟨1564274768693604329989837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2085699691591472439986449 1564274768693604329989837)
                  ·
                    refine ⟨586603038260101623746189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1564274768693604329989837 586603038260101623746189)
                    ·
                      refine ⟨219976139347538108904821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 586603038260101623746189 219976139347538108904821)
                      ·
                        rfl

theorem cell23_428402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_428402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428402 prefixEnd_428402 := by exact prefixLift 428402
  have htrace : WordTrace (prefixWord ++ tailWord_428402) baseStart_428402 baseEnd_428402 := by
    simpa [prefixWord, tailWord_428402, baseEnd_428402] using wordTrace_append hprefix tailTrace_428402
  have hstable : (prefixWord ++ tailWord_428402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428402).length < 2 ^ (prefixWord ++ tailWord_428402).sum := by decide
  have hdescent : baseEnd_428402 < baseStart_428402 := by decide
  rcases family_descends (prefixWord ++ tailWord_428402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428412 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 2, 5, 2]
def baseStart_428412 : Nat := 118140960795 + 428412 * 2 ^ 59
def prefixEnd_428412 : Nat := 4983230072969 + 3 ^ 40 * 428412 * 2
def baseEnd_428412 : Nat := 219981274154083069779775

theorem tailTrace_428412 : CollatzResearch.WordTrace tailWord_428412 prefixEnd_428412 219981274154083069779775 := by
  unfold tailWord_428412
  simp only [CollatzResearch.WordTrace]
  refine ⟨7812734661971982894795745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10416979549295977193060993 7812734661971982894795745)
  ·
    refine ⟨5859550996478987171096809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7812734661971982894795745 5859550996478987171096809)
    ·
      refine ⟨4394663247359240378322607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5859550996478987171096809 4394663247359240378322607)
      ·
        refine ⟨6591994871038860567483911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4394663247359240378322607 6591994871038860567483911)
        ·
          refine ⟨9887992306558290851225867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6591994871038860567483911 9887992306558290851225867)
          ·
            refine ⟨14831988459837436276838801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9887992306558290851225867 14831988459837436276838801)
            ·
              refine ⟨11123991344878077207629101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14831988459837436276838801 11123991344878077207629101)
              ·
                refine ⟨4171496754329278952860913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11123991344878077207629101 4171496754329278952860913)
                ·
                  refine ⟨3128622565746959214645685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4171496754329278952860913 3128622565746959214645685)
                  ·
                    refine ⟨293308365538777426373033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3128622565746959214645685 293308365538777426373033)
                    ·
                      refine ⟨219981274154083069779775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 293308365538777426373033 219981274154083069779775)
                      ·
                        rfl

theorem cell23_428412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 2, 5, 2].length) (baseStart_428412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428412 prefixEnd_428412 := by exact prefixLift 428412
  have htrace : WordTrace (prefixWord ++ tailWord_428412) baseStart_428412 baseEnd_428412 := by
    simpa [prefixWord, tailWord_428412, baseEnd_428412] using wordTrace_append hprefix tailTrace_428412
  have hstable : (prefixWord ++ tailWord_428412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428412).length < 2 ^ (prefixWord ++ tailWord_428412).sum := by decide
  have hdescent : baseEnd_428412 < baseStart_428412 := by decide
  rcases family_descends (prefixWord ++ tailWord_428412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428442 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4]
def baseStart_428442 : Nat := 118140960795 + 428442 * 2 ^ 59
def prefixEnd_428442 : Nat := 4983230072969 + 3 ^ 40 * 428442 * 2
def baseEnd_428442 : Nat := 219996678573717952404637

theorem tailTrace_428442 : CollatzResearch.WordTrace tailWord_428442 prefixEnd_428442 219996678573717952404637 := by
  unfold tailWord_428442
  simp only [CollatzResearch.WordTrace]
  refine ⟨3906640878458820228295895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10417709009223520608789053 3906640878458820228295895)
  ·
    refine ⟨5859961317688230342443843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3906640878458820228295895 5859961317688230342443843)
    ·
      refine ⟨8789941976532345513665765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5859961317688230342443843 8789941976532345513665765)
      ·
        refine ⟨1648114120599814783812331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8789941976532345513665765 1648114120599814783812331)
        ·
          refine ⟨2472171180899722175718497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1648114120599814783812331 2472171180899722175718497)
          ·
            refine ⟨1854128385674791631788873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2472171180899722175718497 1854128385674791631788873)
            ·
              refine ⟨1390596289256093723841655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1854128385674791631788873 1390596289256093723841655)
              ·
                refine ⟨2085894433884140585762483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1390596289256093723841655 2085894433884140585762483)
                ·
                  refine ⟨3128841650826210878643725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2085894433884140585762483 3128841650826210878643725)
                  ·
                    refine ⟨1173315619059829079491397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3128841650826210878643725 1173315619059829079491397)
                    ·
                      refine ⟨219996678573717952404637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1173315619059829079491397 219996678573717952404637)
                      ·
                        rfl

theorem cell23_428442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_428442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428442 prefixEnd_428442 := by exact prefixLift 428442
  have htrace : WordTrace (prefixWord ++ tailWord_428442) baseStart_428442 baseEnd_428442 := by
    simpa [prefixWord, tailWord_428442, baseEnd_428442] using wordTrace_append hprefix tailTrace_428442
  have hstable : (prefixWord ++ tailWord_428442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428442).length < 2 ^ (prefixWord ++ tailWord_428442).sum := by decide
  have hdescent : baseEnd_428442 < baseStart_428442 := by decide
  rcases family_descends (prefixWord ++ tailWord_428442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428452 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 5, 4]
def baseStart_428452 : Nat := 118140960795 + 428452 * 2 ^ 59
def prefixEnd_428452 : Nat := 4983230072969 + 3 ^ 40 * 428452 * 2
def baseEnd_428452 : Nat := 73333937793420971093197

theorem tailTrace_428452 : CollatzResearch.WordTrace tailWord_428452 prefixEnd_428452 73333937793420971093197 := by
  unfold tailWord_428452
  simp only [CollatzResearch.WordTrace]
  refine ⟨7813464121899526310523805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10417952162532701747365073 7813464121899526310523805)
  ·
    refine ⟨2930049045712322366446427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7813464121899526310523805 2930049045712322366446427)
    ·
      refine ⟨4395073568568483549669641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2930049045712322366446427 4395073568568483549669641)
      ·
        refine ⟨3296305176426362662252231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4395073568568483549669641 3296305176426362662252231)
        ·
          refine ⟨4944457764639543993378347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3296305176426362662252231 4944457764639543993378347)
          ·
            refine ⟨7416686646959315990067521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4944457764639543993378347 7416686646959315990067521)
            ·
              refine ⟨5562514985219486992550641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7416686646959315990067521 5562514985219486992550641)
              ·
                refine ⟨4171886238914615244412981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5562514985219486992550641 4171886238914615244412981)
                ·
                  refine ⟨391114334898245179163717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4171886238914615244412981 391114334898245179163717)
                  ·
                    refine ⟨73333937793420971093197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 391114334898245179163717 73333937793420971093197)
                    ·
                      rfl

theorem cell23_428452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_428452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428452 prefixEnd_428452 := by exact prefixLift 428452
  have htrace : WordTrace (prefixWord ++ tailWord_428452) baseStart_428452 baseEnd_428452 := by
    simpa [prefixWord, tailWord_428452, baseEnd_428452] using wordTrace_append hprefix tailTrace_428452
  have hstable : (prefixWord ++ tailWord_428452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428452).length < 2 ^ (prefixWord ++ tailWord_428452).sum := by decide
  have hdescent : baseEnd_428452 < baseStart_428452 := by decide
  rcases family_descends (prefixWord ++ tailWord_428452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428569 : List Nat := [1, 2, 1, 2, 1, 1, 2, 7, 1, 2, 3]
def baseStart_428569 : Nat := 118140960795 + 428569 * 2 ^ 59
def prefixEnd_428569 : Nat := 4983230072969 + 3 ^ 40 * 428569 * 2
def baseEnd_428569 : Nat := 220061890616838955516553

theorem tailTrace_428569 : CollatzResearch.WordTrace tailWord_428569 prefixEnd_428569 220061890616838955516553 := by
  unfold tailWord_428569
  simp only [CollatzResearch.WordTrace]
  refine ⟨15631195584375181603056761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10420797056250121068704507 15631195584375181603056761)
  ·
    refine ⟨11723396688281386202292571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15631195584375181603056761 11723396688281386202292571)
    ·
      refine ⟨17585095032422079303438857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11723396688281386202292571 17585095032422079303438857)
      ·
        refine ⟨13188821274316559477579143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17585095032422079303438857 13188821274316559477579143)
        ·
          refine ⟨19783231911474839216368715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13188821274316559477579143 19783231911474839216368715)
          ·
            refine ⟨29674847867212258824553073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19783231911474839216368715 29674847867212258824553073)
            ·
              refine ⟨22256135900409194118414805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29674847867212258824553073 22256135900409194118414805)
              ·
                refine ⟨521628185165840487150347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22256135900409194118414805 521628185165840487150347)
                ·
                  refine ⟨782442277748760730725521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 521628185165840487150347 782442277748760730725521)
                  ·
                    refine ⟨586831708311570548044141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 782442277748760730725521 586831708311570548044141)
                    ·
                      refine ⟨220061890616838955516553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 586831708311570548044141 220061890616838955516553)
                      ·
                        rfl

theorem cell23_428569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 2, 3].length) (baseStart_428569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428569 prefixEnd_428569 := by exact prefixLift 428569
  have htrace : WordTrace (prefixWord ++ tailWord_428569) baseStart_428569 baseEnd_428569 := by
    simpa [prefixWord, tailWord_428569, baseEnd_428569] using wordTrace_append hprefix tailTrace_428569
  have hstable : (prefixWord ++ tailWord_428569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428569).length < 2 ^ (prefixWord ++ tailWord_428569).sum := by decide
  have hdescent : baseEnd_428569 < baseStart_428569 := by decide
  rcases family_descends (prefixWord ++ tailWord_428569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428572 : List Nat := [2, 2, 3, 1, 2, 3, 10]
def baseStart_428572 : Nat := 118140960795 + 428572 * 2 ^ 59
def prefixEnd_428572 : Nat := 4983230072969 + 3 ^ 40 * 428572 * 2
def baseEnd_428572 : Nat := 2716832482207437577519

theorem tailTrace_428572 : CollatzResearch.WordTrace tailWord_428572 prefixEnd_428572 2716832482207437577519 := by
  unfold tailWord_428572
  simp only [CollatzResearch.WordTrace]
  refine ⟨7815652501682156557707985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10420870002242875410277313 7815652501682156557707985)
  ·
    refine ⟨5861739376261617418280989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7815652501682156557707985 5861739376261617418280989)
    ·
      refine ⟨2198152266098106531855371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5861739376261617418280989 2198152266098106531855371)
      ·
        refine ⟨3297228399147159797783057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2198152266098106531855371 3297228399147159797783057)
        ·
          refine ⟨2472921299360369848337293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3297228399147159797783057 2472921299360369848337293)
          ·
            refine ⟨927345487260138693126485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2472921299360369848337293 927345487260138693126485)
            ·
              refine ⟨2716832482207437577519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 927345487260138693126485 2716832482207437577519)
              ·
                rfl

theorem cell23_428572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 10].length) (baseStart_428572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428572 prefixEnd_428572 := by exact prefixLift 428572
  have htrace : WordTrace (prefixWord ++ tailWord_428572) baseStart_428572 baseEnd_428572 := by
    simpa [prefixWord, tailWord_428572, baseEnd_428572] using wordTrace_append hprefix tailTrace_428572
  have hstable : (prefixWord ++ tailWord_428572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428572).length < 2 ^ (prefixWord ++ tailWord_428572).sum := by decide
  have hdescent : baseEnd_428572 < baseStart_428572 := by decide
  rcases family_descends (prefixWord ++ tailWord_428572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428576 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 4, 4]
def baseStart_428576 : Nat := 118140960795 + 428576 * 2 ^ 59
def prefixEnd_428576 : Nat := 4983230072969 + 3 ^ 40 * 428576 * 2
def baseEnd_428576 : Nat := 73355161660473476043007

theorem tailTrace_428576 : CollatzResearch.WordTrace tailWord_428576 prefixEnd_428576 73355161660473476043007 := by
  unfold tailWord_428576
  simp only [CollatzResearch.WordTrace]
  refine ⟨7815725447674910899280791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10420967263566547865707721 7815725447674910899280791)
  ·
    refine ⟨11723588171512366348921187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7815725447674910899280791 11723588171512366348921187)
    ·
      refine ⟨17585382257268549523381781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11723588171512366348921187 17585382257268549523381781)
      ·
        refine ⟨824314793309463258908521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17585382257268549523381781 824314793309463258908521)
        ·
          refine ⟨618236094982097444181391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 824314793309463258908521 618236094982097444181391)
          ·
            refine ⟨927354142473146166272087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618236094982097444181391 927354142473146166272087)
            ·
              refine ⟨1391031213709719249408131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 927354142473146166272087 1391031213709719249408131)
              ·
                refine ⟨2086546820564578874112197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1391031213709719249408131 2086546820564578874112197)
                ·
                  refine ⟨391227528855858538896037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2086546820564578874112197 391227528855858538896037)
                  ·
                    refine ⟨73355161660473476043007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 391227528855858538896037 73355161660473476043007)
                    ·
                      rfl

theorem cell23_428576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 4, 4].length) (baseStart_428576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428576 prefixEnd_428576 := by exact prefixLift 428576
  have htrace : WordTrace (prefixWord ++ tailWord_428576) baseStart_428576 baseEnd_428576 := by
    simpa [prefixWord, tailWord_428576, baseEnd_428576] using wordTrace_append hprefix tailTrace_428576
  have hstable : (prefixWord ++ tailWord_428576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428576).length < 2 ^ (prefixWord ++ tailWord_428576).sum := by decide
  have hdescent : baseEnd_428576 < baseStart_428576 := by decide
  rcases family_descends (prefixWord ++ tailWord_428576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428606 : List Nat := [4, 2, 1, 4, 1, 1, 1, 9]
def baseStart_428606 : Nat := 118140960795 + 428606 * 2 ^ 59
def prefixEnd_428606 : Nat := 4983230072969 + 3 ^ 40 * 428606 * 2
def baseEnd_428606 : Nat := 8151144051890937435329

theorem tailTrace_428606 : CollatzResearch.WordTrace tailWord_428606 prefixEnd_428606 8151144051890937435329 := by
  unfold tailWord_428606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1954068135655142115269209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10421696723494091281435781 1954068135655142115269209)
  ·
    refine ⟨1465551101741356586451907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1954068135655142115269209 1465551101741356586451907)
    ·
      refine ⟨2198326652612034879677861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1465551101741356586451907 2198326652612034879677861)
      ·
        refine ⟨412186247364756539939599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2198326652612034879677861 412186247364756539939599)
        ·
          refine ⟨618279371047134809909399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412186247364756539939599 618279371047134809909399)
          ·
            refine ⟨927419056570702214864099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618279371047134809909399 927419056570702214864099)
            ·
              refine ⟨1391128584856053322296149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 927419056570702214864099 1391128584856053322296149)
              ·
                refine ⟨8151144051890937435329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1391128584856053322296149 8151144051890937435329)
                ·
                  rfl

theorem cell23_428606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 9].length) (baseStart_428606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428606 prefixEnd_428606 := by exact prefixLift 428606
  have htrace : WordTrace (prefixWord ++ tailWord_428606) baseStart_428606 baseEnd_428606 := by
    simpa [prefixWord, tailWord_428606, baseEnd_428606] using wordTrace_append hprefix tailTrace_428606
  have hstable : (prefixWord ++ tailWord_428606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428606).length < 2 ^ (prefixWord ++ tailWord_428606).sum := by decide
  have hdescent : baseEnd_428606 < baseStart_428606 := by decide
  rcases family_descends (prefixWord ++ tailWord_428606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428632 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 4, 6]
def baseStart_428632 : Nat := 118140960795 + 428632 * 2 ^ 59
def prefixEnd_428632 : Nat := 4983230072969 + 3 ^ 40 * 428632 * 2
def baseEnd_428632 : Nat := 73364746632690736342921

theorem tailTrace_428632 : CollatzResearch.WordTrace tailWord_428632 prefixEnd_428632 73364746632690736342921 := by
  unfold tailWord_428632
  simp only [CollatzResearch.WordTrace]
  refine ⟨7816746691573471681300075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10422328922097962241733433 7816746691573471681300075)
  ·
    refine ⟨11725120037360207521950113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7816746691573471681300075 11725120037360207521950113)
    ·
      refine ⟨8793840028020155641462585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11725120037360207521950113 8793840028020155641462585)
      ·
        refine ⟨6595380021015116731096939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8793840028020155641462585 6595380021015116731096939)
        ·
          refine ⟨9893070031522675096645409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6595380021015116731096939 9893070031522675096645409)
          ·
            refine ⟨7419802523642006322484057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9893070031522675096645409 7419802523642006322484057)
            ·
              refine ⟨5564851892731504741863043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7419802523642006322484057 5564851892731504741863043)
              ·
                refine ⟨8347277839097257112794565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5564851892731504741863043 8347277839097257112794565)
                ·
                  refine ⟨1565114594830735708648981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8347277839097257112794565 1565114594830735708648981)
                  ·
                    refine ⟨73364746632690736342921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1565114594830735708648981 73364746632690736342921)
                    ·
                      rfl

theorem cell23_428632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_428632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428632 prefixEnd_428632 := by exact prefixLift 428632
  have htrace : WordTrace (prefixWord ++ tailWord_428632) baseStart_428632 baseEnd_428632 := by
    simpa [prefixWord, tailWord_428632, baseEnd_428632] using wordTrace_append hprefix tailTrace_428632
  have hstable : (prefixWord ++ tailWord_428632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428632).length < 2 ^ (prefixWord ++ tailWord_428632).sum := by decide
  have hdescent : baseEnd_428632 < baseStart_428632 := by decide
  rcases family_descends (prefixWord ++ tailWord_428632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
