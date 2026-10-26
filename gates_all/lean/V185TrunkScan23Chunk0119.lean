import V185TrunkScan23Chunk0118

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_703666 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3]
def baseStart_703666 : Nat := 118140960795 + 703666 * 2 ^ 59
def prefixEnd_703666 : Nat := 4983230072969 + 3 ^ 40 * 703666 * 2
def baseEnd_703666 : Nat := 361318878226749137238905

theorem tailTrace_703666 : CollatzResearch.WordTrace tailWord_703666 prefixEnd_703666 361318878226749137238905 := by
  unfold tailWord_703666
  simp only [CollatzResearch.WordTrace]
  refine ⟨6416201867186433357540713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17109871645830488953441901 6416201867186433357540713)
  ·
    refine ⟨4812151400389825018155535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6416201867186433357540713 4812151400389825018155535)
    ·
      refine ⟨7218227100584737527233303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4812151400389825018155535 7218227100584737527233303)
      ·
        refine ⟨10827340650877106290849955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7218227100584737527233303 10827340650877106290849955)
        ·
          refine ⟨16241010976315659436274933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10827340650877106290849955 16241010976315659436274933)
          ·
            refine ⟨1522594779029593072150775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16241010976315659436274933 1522594779029593072150775)
            ·
              refine ⟨2283892168544389608226163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1522594779029593072150775 2283892168544389608226163)
              ·
                refine ⟨3425838252816584412339245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2283892168544389608226163 3425838252816584412339245)
                ·
                  refine ⟨1284689344806219154627217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3425838252816584412339245 1284689344806219154627217)
                  ·
                    refine ⟨963517008604664365970413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1284689344806219154627217 963517008604664365970413)
                    ·
                      refine ⟨361318878226749137238905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 963517008604664365970413 361318878226749137238905)
                      ·
                        rfl

theorem cell23_703666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_703666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703666 prefixEnd_703666 := by exact prefixLift 703666
  have htrace : WordTrace (prefixWord ++ tailWord_703666) baseStart_703666 baseEnd_703666 := by
    simpa [prefixWord, tailWord_703666, baseEnd_703666] using wordTrace_append hprefix tailTrace_703666
  have hstable : (prefixWord ++ tailWord_703666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703666).length < 2 ^ (prefixWord ++ tailWord_703666).sum := by decide
  have hdescent : baseEnd_703666 < baseStart_703666 := by decide
  rcases family_descends (prefixWord ++ tailWord_703666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703676 : List Nat := [2, 2, 2, 3, 2, 2, 1, 2, 1, 2, 4]
def baseStart_703676 : Nat := 118140960795 + 703676 * 2 ^ 59
def prefixEnd_703676 : Nat := 4983230072969 + 3 ^ 40 * 703676 * 2
def baseEnd_703676 : Nat := 361324013033294098113859

theorem tailTrace_703676 : CollatzResearch.WordTrace tailWord_703676 prefixEnd_703676 361324013033294098113859 := by
  unfold tailWord_703676
  simp only [CollatzResearch.WordTrace]
  refine ⟨12832586099354752569013441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17110114799139670092017921 12832586099354752569013441)
  ·
    refine ⟨9624439574516064426760081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12832586099354752569013441 9624439574516064426760081)
    ·
      refine ⟨7218329680887048320070061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9624439574516064426760081 7218329680887048320070061)
      ·
        refine ⟨2706873630332643120026273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7218329680887048320070061 2706873630332643120026273)
        ·
          refine ⟨2030155222749482340019705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2706873630332643120026273 2030155222749482340019705)
          ·
            refine ⟨1522616417062111755014779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2030155222749482340019705 1522616417062111755014779)
            ·
              refine ⟨2283924625593167632522169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1522616417062111755014779 2283924625593167632522169)
              ·
                refine ⟨1712943469194875724391627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2283924625593167632522169 1712943469194875724391627)
                ·
                  refine ⟨2569415203792313586587441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1712943469194875724391627 2569415203792313586587441)
                  ·
                    refine ⟨1927061402844235189940581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2569415203792313586587441 1927061402844235189940581)
                    ·
                      refine ⟨361324013033294098113859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1927061402844235189940581 361324013033294098113859)
                      ·
                        rfl

theorem cell23_703676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_703676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703676 prefixEnd_703676 := by exact prefixLift 703676
  have htrace : WordTrace (prefixWord ++ tailWord_703676) baseStart_703676 baseEnd_703676 := by
    simpa [prefixWord, tailWord_703676, baseEnd_703676] using wordTrace_append hprefix tailTrace_703676
  have hstable : (prefixWord ++ tailWord_703676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703676).length < 2 ^ (prefixWord ++ tailWord_703676).sum := by decide
  have hdescent : baseEnd_703676 < baseStart_703676 := by decide
  rcases family_descends (prefixWord ++ tailWord_703676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703679 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 3]
def baseStart_703679 : Nat := 118140960795 + 703679 * 2 ^ 59
def prefixEnd_703679 : Nat := 4983230072969 + 3 ^ 40 * 703679 * 2
def baseEnd_703679 : Nat := 361325553475257586376345

theorem tailTrace_703679 : CollatzResearch.WordTrace tailWord_703679 prefixEnd_703679 361325553475257586376345 := by
  unfold tailWord_703679
  simp only [CollatzResearch.WordTrace]
  refine ⟨25665281617698636650386091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17110187745132424433590727 25665281617698636650386091)
  ·
    refine ⟨38497922426547954975579137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25665281617698636650386091 38497922426547954975579137)
    ·
      refine ⟨28873441819910966231684353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38497922426547954975579137 28873441819910966231684353)
      ·
        refine ⟨21655081364933224673763265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28873441819910966231684353 21655081364933224673763265)
        ·
          refine ⟨16241311023699918505322449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21655081364933224673763265 16241311023699918505322449)
          ·
            refine ⟨12180983267774938878991837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16241311023699918505322449 12180983267774938878991837)
            ·
              refine ⟨4567868725415602079621939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12180983267774938878991837 4567868725415602079621939)
              ·
                refine ⟨6851803088123403119432909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4567868725415602079621939 6851803088123403119432909)
                ·
                  refine ⟨2569426158046276169787341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6851803088123403119432909 2569426158046276169787341)
                  ·
                    refine ⟨963534809267353563670253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2569426158046276169787341 963534809267353563670253)
                    ·
                      refine ⟨361325553475257586376345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 963534809267353563670253 361325553475257586376345)
                      ·
                        rfl

theorem cell23_703679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 3].length) (baseStart_703679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703679 prefixEnd_703679 := by exact prefixLift 703679
  have htrace : WordTrace (prefixWord ++ tailWord_703679) baseStart_703679 baseEnd_703679 := by
    simpa [prefixWord, tailWord_703679, baseEnd_703679] using wordTrace_append hprefix tailTrace_703679
  have hstable : (prefixWord ++ tailWord_703679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703679).length < 2 ^ (prefixWord ++ tailWord_703679).sum := by decide
  have hdescent : baseEnd_703679 < baseStart_703679 := by decide
  rcases family_descends (prefixWord ++ tailWord_703679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703713 : List Nat := [1, 2, 3, 1, 3, 2, 2, 3, 2, 1, 3]
def baseStart_703713 : Nat := 118140960795 + 703713 * 2 ^ 59
def prefixEnd_703713 : Nat := 4983230072969 + 3 ^ 40 * 703713 * 2
def baseEnd_703713 : Nat := 361343011817510453351189

theorem tailTrace_703713 : CollatzResearch.WordTrace tailWord_703713 prefixEnd_703713 361343011817510453351189 := by
  unfold tailWord_703713
  simp only [CollatzResearch.WordTrace]
  refine ⟨25666521699575460457123793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17111014466383640304749195 25666521699575460457123793)
  ·
    refine ⟨19249891274681595342842845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25666521699575460457123793 19249891274681595342842845)
    ·
      refine ⟨7218709228005598253566067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19249891274681595342842845 7218709228005598253566067)
      ·
        refine ⟨10828063842008397380349101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7218709228005598253566067 10828063842008397380349101)
        ·
          refine ⟨4060523940753149017630913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10828063842008397380349101 4060523940753149017630913)
          ·
            refine ⟨3045392955564861763223185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4060523940753149017630913 3045392955564861763223185)
            ·
              refine ⟨2284044716673646322417389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3045392955564861763223185 2284044716673646322417389)
              ·
                refine ⟨856516768752617370906521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2284044716673646322417389 856516768752617370906521)
                ·
                  refine ⟨642387576564463028179891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 856516768752617370906521 642387576564463028179891)
                  ·
                    refine ⟨963581364846694542269837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 642387576564463028179891 963581364846694542269837)
                    ·
                      refine ⟨361343011817510453351189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 963581364846694542269837 361343011817510453351189)
                      ·
                        rfl

theorem cell23_703713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_703713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703713 prefixEnd_703713 := by exact prefixLift 703713
  have htrace : WordTrace (prefixWord ++ tailWord_703713) baseStart_703713 baseEnd_703713 := by
    simpa [prefixWord, tailWord_703713, baseEnd_703713] using wordTrace_append hprefix tailTrace_703713
  have hstable : (prefixWord ++ tailWord_703713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703713).length < 2 ^ (prefixWord ++ tailWord_703713).sum := by decide
  have hdescent : baseEnd_703713 < baseStart_703713 := by decide
  rcases family_descends (prefixWord ++ tailWord_703713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703740 : List Nat := [2, 2, 2, 1, 5, 1, 1, 3, 1, 3, 2]
def baseStart_703740 : Nat := 118140960795 + 703740 * 2 ^ 59
def prefixEnd_703740 : Nat := 4983230072969 + 3 ^ 40 * 703740 * 2
def baseEnd_703740 : Nat := 361356875795181847713565

theorem tailTrace_703740 : CollatzResearch.WordTrace tailWord_703740 prefixEnd_703740 361356875795181847713565 := by
  unfold tailWord_703740
  simp only [CollatzResearch.WordTrace]
  refine ⟨12833753235238822034178337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17111670980318429378904449 12833753235238822034178337)
  ·
    refine ⟨9625314926429116525633753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12833753235238822034178337 9625314926429116525633753)
    ·
      refine ⟨7218986194821837394225315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9625314926429116525633753 7218986194821837394225315)
      ·
        refine ⟨10828479292232756091337973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7218986194821837394225315 10828479292232756091337973)
        ·
          refine ⟨1015169933646820883562935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10828479292232756091337973 1015169933646820883562935)
          ·
            refine ⟨1522754900470231325344403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1015169933646820883562935 1522754900470231325344403)
            ·
              refine ⟨2284132350705346988016605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1522754900470231325344403 2284132350705346988016605)
              ·
                refine ⟨856549631514505120506227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2284132350705346988016605 856549631514505120506227)
                ·
                  refine ⟨1284824447271757680759341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 856549631514505120506227 1284824447271757680759341)
                  ·
                    refine ⟨481809167726909130284753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1284824447271757680759341 481809167726909130284753)
                    ·
                      refine ⟨361356875795181847713565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 481809167726909130284753 361356875795181847713565)
                      ·
                        rfl

theorem cell23_703740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 1, 3, 2].length) (baseStart_703740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703740 prefixEnd_703740 := by exact prefixLift 703740
  have htrace : WordTrace (prefixWord ++ tailWord_703740) baseStart_703740 baseEnd_703740 := by
    simpa [prefixWord, tailWord_703740, baseEnd_703740] using wordTrace_append hprefix tailTrace_703740
  have hstable : (prefixWord ++ tailWord_703740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703740).length < 2 ^ (prefixWord ++ tailWord_703740).sum := by decide
  have hdescent : baseEnd_703740 < baseStart_703740 := by decide
  rcases family_descends (prefixWord ++ tailWord_703740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703749 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 4, 2, 4]
def baseStart_703749 : Nat := 118140960795 + 703749 * 2 ^ 59
def prefixEnd_703749 : Nat := 4983230072969 + 3 ^ 40 * 703749 * 2
def baseEnd_703749 : Nat := 361361497121072312501023

theorem tailTrace_703749 : CollatzResearch.WordTrace tailWord_703749 prefixEnd_703749 361361497121072312501023 := by
  unfold tailWord_703749
  simp only [CollatzResearch.WordTrace]
  refine ⟨25667834727445038605434301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17111889818296692403622867 25667834727445038605434301)
  ·
    refine ⟨9625438022791889477037863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25667834727445038605434301 9625438022791889477037863)
    ·
      refine ⟨14438157034187834215556795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9625438022791889477037863 14438157034187834215556795)
      ·
        refine ⟨21657235551281751323335193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14438157034187834215556795 21657235551281751323335193)
        ·
          refine ⟨16242926663461313492501395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21657235551281751323335193 16242926663461313492501395)
          ·
            refine ⟨24364389995191970238752093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16242926663461313492501395 24364389995191970238752093)
            ·
              refine ⟨9136646248196988839532035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24364389995191970238752093 9136646248196988839532035)
              ·
                refine ⟨13704969372295483259298053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9136646248196988839532035 13704969372295483259298053)
                ·
                  refine ⟨2569681757305403111118385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13704969372295483259298053 2569681757305403111118385)
                  ·
                    refine ⟨1927261317979052333338789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2569681757305403111118385 1927261317979052333338789)
                    ·
                      refine ⟨361361497121072312501023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1927261317979052333338789 361361497121072312501023)
                      ·
                        rfl

theorem cell23_703749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_703749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703749 prefixEnd_703749 := by exact prefixLift 703749
  have htrace : WordTrace (prefixWord ++ tailWord_703749) baseStart_703749 baseEnd_703749 := by
    simpa [prefixWord, tailWord_703749, baseEnd_703749] using wordTrace_append hprefix tailTrace_703749
  have hstable : (prefixWord ++ tailWord_703749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703749).length < 2 ^ (prefixWord ++ tailWord_703749).sum := by decide
  have hdescent : baseEnd_703749 < baseStart_703749 := by decide
  rcases family_descends (prefixWord ++ tailWord_703749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703753 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 4, 2, 2]
def baseStart_703753 : Nat := 118140960795 + 703753 * 2 ^ 59
def prefixEnd_703753 : Nat := 4983230072969 + 3 ^ 40 * 703753 * 2
def baseEnd_703753 : Nat := 361363551043690296851005

theorem tailTrace_703753 : CollatzResearch.WordTrace tailWord_703753 prefixEnd_703753 361363551043690296851005 := by
  unfold tailWord_703753
  simp only [CollatzResearch.WordTrace]
  refine ⟨25667980619430547288579913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17111987079620364859053275 25667980619430547288579913)
  ·
    refine ⟨19250985464572910466434935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25667980619430547288579913 19250985464572910466434935)
    ·
      refine ⟨28876478196859365699652403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19250985464572910466434935 28876478196859365699652403)
      ·
        refine ⟨43314717295289048549478605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28876478196859365699652403 43314717295289048549478605)
        ·
          refine ⟨16243018985733393206054477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43314717295289048549478605 16243018985733393206054477)
          ·
            refine ⟨6091132119650022452270429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16243018985733393206054477 6091132119650022452270429)
            ·
              refine ⟨2284174544868758419601411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6091132119650022452270429 2284174544868758419601411)
              ·
                refine ⟨3426261817303137629402117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2284174544868758419601411 3426261817303137629402117)
                ·
                  refine ⟨642424090744338305512897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3426261817303137629402117 642424090744338305512897)
                  ·
                    refine ⟨481818068058253729134673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 642424090744338305512897 481818068058253729134673)
                    ·
                      refine ⟨361363551043690296851005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 481818068058253729134673 361363551043690296851005)
                      ·
                        rfl

theorem cell23_703753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 2, 2].length) (baseStart_703753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703753 prefixEnd_703753 := by exact prefixLift 703753
  have htrace : WordTrace (prefixWord ++ tailWord_703753) baseStart_703753 baseEnd_703753 := by
    simpa [prefixWord, tailWord_703753, baseEnd_703753] using wordTrace_append hprefix tailTrace_703753
  have hstable : (prefixWord ++ tailWord_703753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703753).length < 2 ^ (prefixWord ++ tailWord_703753).sum := by decide
  have hdescent : baseEnd_703753 < baseStart_703753 := by decide
  rcases family_descends (prefixWord ++ tailWord_703753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703770 : List Nat := [3, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2]
def baseStart_703770 : Nat := 118140960795 + 703770 * 2 ^ 59
def prefixEnd_703770 : Nat := 4983230072969 + 3 ^ 40 * 703770 * 2
def baseEnd_703770 : Nat := 361372280214816730338427

theorem tailTrace_703770 : CollatzResearch.WordTrace tailWord_703770 prefixEnd_703770 361372280214816730338427 := by
  unfold tailWord_703770
  simp only [CollatzResearch.WordTrace]
  refine ⟨6417150165092239797987191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17112400440245972794632509 6417150165092239797987191)
  ·
    refine ⟨9625725247638359696980787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6417150165092239797987191 9625725247638359696980787)
    ·
      refine ⟨14438587871457539545471181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9625725247638359696980787 14438587871457539545471181)
      ·
        refine ⟨5414470451796577329551693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14438587871457539545471181 5414470451796577329551693)
        ·
          refine ⟨2030426419423716498581885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5414470451796577329551693 2030426419423716498581885)
          ·
            refine ⟨761409907283893686968207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2030426419423716498581885 761409907283893686968207)
            ·
              refine ⟨1142114860925840530452311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761409907283893686968207 1142114860925840530452311)
              ·
                refine ⟨1713172291388760795678467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142114860925840530452311 1713172291388760795678467)
                ·
                  refine ⟨2569758437083141193517701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1713172291388760795678467 2569758437083141193517701)
                  ·
                    refine ⟨481829706953088973784569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2569758437083141193517701 481829706953088973784569)
                    ·
                      refine ⟨361372280214816730338427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 481829706953088973784569 361372280214816730338427)
                      ·
                        rfl

theorem cell23_703770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_703770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703770 prefixEnd_703770 := by exact prefixLift 703770
  have htrace : WordTrace (prefixWord ++ tailWord_703770) baseStart_703770 baseEnd_703770 := by
    simpa [prefixWord, tailWord_703770, baseEnd_703770] using wordTrace_append hprefix tailTrace_703770
  have hstable : (prefixWord ++ tailWord_703770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703770).length < 2 ^ (prefixWord ++ tailWord_703770).sum := by decide
  have hdescent : baseEnd_703770 < baseStart_703770 := by decide
  rcases family_descends (prefixWord ++ tailWord_703770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703774 : List Nat := [4, 3, 2, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_703774 : Nat := 118140960795 + 703774 * 2 ^ 59
def prefixEnd_703774 : Nat := 4983230072969 + 3 ^ 40 * 703774 * 2
def baseEnd_703774 : Nat := 361374334137434714688409

theorem tailTrace_703774 : CollatzResearch.WordTrace tailWord_703774 prefixEnd_703774 361374334137434714688409 := by
  unfold tailWord_703774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3208593319044308484386797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17112497701569645250062917 3208593319044308484386797)
  ·
    refine ⟨1203222494641615681645049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3208593319044308484386797 1203222494641615681645049)
    ·
      refine ⟨902416870981211761233787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1203222494641615681645049 902416870981211761233787)
      ·
        refine ⟨1353625306471817641850681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 902416870981211761233787 1353625306471817641850681)
        ·
          refine ⟨1015218979853863231388011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1353625306471817641850681 1015218979853863231388011)
          ·
            refine ⟨1522828469780794847082017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1015218979853863231388011 1522828469780794847082017)
            ·
              refine ⟨1142121352335596135311513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1522828469780794847082017 1142121352335596135311513)
              ·
                refine ⟨856591014251697101483635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1142121352335596135311513 856591014251697101483635)
                ·
                  refine ⟨1284886521377545652225453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 856591014251697101483635 1284886521377545652225453)
                  ·
                    refine ⟨481832445516579619584545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1284886521377545652225453 481832445516579619584545)
                    ·
                      refine ⟨361374334137434714688409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 481832445516579619584545 361374334137434714688409)
                      ·
                        rfl

theorem cell23_703774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_703774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703774 prefixEnd_703774 := by exact prefixLift 703774
  have htrace : WordTrace (prefixWord ++ tailWord_703774) baseStart_703774 baseEnd_703774 := by
    simpa [prefixWord, tailWord_703774, baseEnd_703774] using wordTrace_append hprefix tailTrace_703774
  have hstable : (prefixWord ++ tailWord_703774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703774).length < 2 ^ (prefixWord ++ tailWord_703774).sum := by decide
  have hdescent : baseEnd_703774 < baseStart_703774 := by decide
  rcases family_descends (prefixWord ++ tailWord_703774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703793 : List Nat := [1, 2, 2, 3, 3, 1, 3, 3, 5]
def baseStart_703793 : Nat := 118140960795 + 703793 * 2 ^ 59
def prefixEnd_703793 : Nat := 4983230072969 + 3 ^ 40 * 703793 * 2
def baseEnd_703793 : Nat := 40153787807763348927869

theorem tailTrace_703793 : CollatzResearch.WordTrace tailWord_703793 prefixEnd_703793 40153787807763348927869 := by
  unfold tailWord_703793
  simp only [CollatzResearch.WordTrace]
  refine ⟨25669439539285634120036033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17112959692857089413357355 25669439539285634120036033)
  ·
    refine ⟨19252079654464225590027025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25669439539285634120036033 19252079654464225590027025)
    ·
      refine ⟨14439059740848169192520269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19252079654464225590027025 14439059740848169192520269)
      ·
        refine ⟨5414647402818063447195101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14439059740848169192520269 5414647402818063447195101)
        ·
          refine ⟨2030492776056773792698163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5414647402818063447195101 2030492776056773792698163)
          ·
            refine ⟨3045739164085160689047245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2030492776056773792698163 3045739164085160689047245)
            ·
              refine ⟨1142152186531935258392717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3045739164085160689047245 1142152186531935258392717)
              ·
                refine ⟨428307069949475721897269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1142152186531935258392717 428307069949475721897269)
                ·
                  refine ⟨40153787807763348927869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 428307069949475721897269 40153787807763348927869)
                  ·
                    rfl

theorem cell23_703793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 5].length) (baseStart_703793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703793 prefixEnd_703793 := by exact prefixLift 703793
  have htrace : WordTrace (prefixWord ++ tailWord_703793) baseStart_703793 baseEnd_703793 := by
    simpa [prefixWord, tailWord_703793, baseEnd_703793] using wordTrace_append hprefix tailTrace_703793
  have hstable : (prefixWord ++ tailWord_703793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703793).length < 2 ^ (prefixWord ++ tailWord_703793).sum := by decide
  have hdescent : baseEnd_703793 < baseStart_703793 := by decide
  rcases family_descends (prefixWord ++ tailWord_703793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703826 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_703826 : Nat := 118140960795 + 703826 * 2 ^ 59
def prefixEnd_703826 : Nat := 4983230072969 + 3 ^ 40 * 703826 * 2
def baseEnd_703826 : Nat := 361401035131468511238169

theorem tailTrace_703826 : CollatzResearch.WordTrace tailWord_703826 prefixEnd_703826 361401035131468511238169 := by
  unfold tailWord_703826
  simp only [CollatzResearch.WordTrace]
  refine ⟨6417660787041520188996833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17113762098777387170658221 6417660787041520188996833)
  ·
    refine ⟨4813245590281140141747625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6417660787041520188996833 4813245590281140141747625)
    ·
      refine ⟨3609934192710855106310719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4813245590281140141747625 3609934192710855106310719)
      ·
        refine ⟨5414901289066282659466079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3609934192710855106310719 5414901289066282659466079)
        ·
          refine ⟨8122351933599423989199119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5414901289066282659466079 8122351933599423989199119)
          ·
            refine ⟨12183527900399135983798679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8122351933599423989199119 12183527900399135983798679)
            ·
              refine ⟨18275291850598703975698019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12183527900399135983798679 18275291850598703975698019)
              ·
                refine ⟨27412937775898055963547029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18275291850598703975698019 27412937775898055963547029)
                ·
                  refine ⟨1284981458245221373291267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27412937775898055963547029 1284981458245221373291267)
                  ·
                    refine ⟨1927472187367832059936901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1284981458245221373291267 1927472187367832059936901)
                    ·
                      refine ⟨361401035131468511238169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1927472187367832059936901 361401035131468511238169)
                      ·
                        rfl

theorem cell23_703826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_703826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703826 prefixEnd_703826 := by exact prefixLift 703826
  have htrace : WordTrace (prefixWord ++ tailWord_703826) baseStart_703826 baseEnd_703826 := by
    simpa [prefixWord, tailWord_703826, baseEnd_703826] using wordTrace_append hprefix tailTrace_703826
  have hstable : (prefixWord ++ tailWord_703826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703826).length < 2 ^ (prefixWord ++ tailWord_703826).sum := by decide
  have hdescent : baseEnd_703826 < baseStart_703826 := by decide
  rcases family_descends (prefixWord ++ tailWord_703826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703839 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 6]
def baseStart_703839 : Nat := 118140960795 + 703839 * 2 ^ 59
def prefixEnd_703839 : Nat := 4983230072969 + 3 ^ 40 * 703839 * 2
def baseEnd_703839 : Nat := 361407710379976960375609

theorem tailTrace_703839 : CollatzResearch.WordTrace tailWord_703839 prefixEnd_703839 361407710379976960375609 := by
  unfold tailWord_703839
  simp only [CollatzResearch.WordTrace]
  refine ⟨25671117297118983976210571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17114078198079322650807047 25671117297118983976210571)
  ·
    refine ⟨38506675945678475964315857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25671117297118983976210571 38506675945678475964315857)
    ·
      refine ⟨28880006959258856973236893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38506675945678475964315857 28880006959258856973236893)
      ·
        refine ⟨10830002609722071364963835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28880006959258856973236893 10830002609722071364963835)
        ·
          refine ⟨16245003914583107047445753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10830002609722071364963835 16245003914583107047445753)
          ·
            refine ⟨12183752935937330285584315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16245003914583107047445753 12183752935937330285584315)
            ·
              refine ⟨18275629403905995428376473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12183752935937330285584315 18275629403905995428376473)
              ·
                refine ⟨13706722052929496571282355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18275629403905995428376473 13706722052929496571282355)
                ·
                  refine ⟨20560083079394244856923533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13706722052929496571282355 20560083079394244856923533)
                  ·
                    refine ⟨7710031154772841821346325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20560083079394244856923533 7710031154772841821346325)
                    ·
                      refine ⟨361407710379976960375609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7710031154772841821346325 361407710379976960375609)
                      ·
                        rfl

theorem cell23_703839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_703839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703839 prefixEnd_703839 := by exact prefixLift 703839
  have htrace : WordTrace (prefixWord ++ tailWord_703839) baseStart_703839 baseEnd_703839 := by
    simpa [prefixWord, tailWord_703839, baseEnd_703839] using wordTrace_append hprefix tailTrace_703839
  have hstable : (prefixWord ++ tailWord_703839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703839).length < 2 ^ (prefixWord ++ tailWord_703839).sum := by decide
  have hdescent : baseEnd_703839 < baseStart_703839 := by decide
  rcases family_descends (prefixWord ++ tailWord_703839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703843 : List Nat := [1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 4]
def baseStart_703843 : Nat := 118140960795 + 703843 * 2 ^ 59
def prefixEnd_703843 : Nat := 4983230072969 + 3 ^ 40 * 703843 * 2
def baseEnd_703843 : Nat := 361409764302594944725591

theorem tailTrace_703843 : CollatzResearch.WordTrace tailWord_703843 prefixEnd_703843 361409764302594944725591 := by
  unfold tailWord_703843
  simp only [CollatzResearch.WordTrace]
  refine ⟨25671263189104492659356183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17114175459402995106237455 25671263189104492659356183)
  ·
    refine ⟨38506894783656738989034275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25671263189104492659356183 38506894783656738989034275)
    ·
      refine ⟨57760342175485108483551413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38506894783656738989034275 57760342175485108483551413)
      ·
        refine ⟨5415032078951728920332945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57760342175485108483551413 5415032078951728920332945)
        ·
          refine ⟨4061274059213796690249709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5415032078951728920332945 4061274059213796690249709)
          ·
            refine ⟨1522977772205173758843641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4061274059213796690249709 1522977772205173758843641)
            ·
              refine ⟨1142233329153880319132731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1522977772205173758843641 1142233329153880319132731)
              ·
                refine ⟨1713349993730820478699097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142233329153880319132731 1713349993730820478699097)
                ·
                  refine ⟨1285012495298115359024323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1713349993730820478699097 1285012495298115359024323)
                  ·
                    refine ⟨1927518742947173038536485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1285012495298115359024323 1927518742947173038536485)
                    ·
                      refine ⟨361409764302594944725591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1927518742947173038536485 361409764302594944725591)
                      ·
                        rfl

theorem cell23_703843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_703843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703843 prefixEnd_703843 := by exact prefixLift 703843
  have htrace : WordTrace (prefixWord ++ tailWord_703843) baseStart_703843 baseEnd_703843 := by
    simpa [prefixWord, tailWord_703843, baseEnd_703843] using wordTrace_append hprefix tailTrace_703843
  have hstable : (prefixWord ++ tailWord_703843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703843).length < 2 ^ (prefixWord ++ tailWord_703843).sum := by decide
  have hdescent : baseEnd_703843 < baseStart_703843 := by decide
  rcases family_descends (prefixWord ++ tailWord_703843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703849 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 8]
def baseStart_703849 : Nat := 118140960795 + 703849 * 2 ^ 59
def prefixEnd_703849 : Nat := 4983230072969 + 3 ^ 40 * 703849 * 2
def baseEnd_703849 : Nat := 40156982798502435694507

theorem tailTrace_703849 : CollatzResearch.WordTrace tailWord_703849 prefixEnd_703849 40156982798502435694507 := by
  unfold tailWord_703849
  simp only [CollatzResearch.WordTrace]
  refine ⟨25671482027082755684074601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17114321351388503789383067 25671482027082755684074601)
  ·
    refine ⟨19253611520312066763055951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25671482027082755684074601 19253611520312066763055951)
    ·
      refine ⟨28880417280468100144583927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19253611520312066763055951 28880417280468100144583927)
      ·
        refine ⟨43320625920702150216875891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28880417280468100144583927 43320625920702150216875891)
        ·
          refine ⟨64980938881053225325313837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43320625920702150216875891 64980938881053225325313837)
          ·
            refine ⟨24367852080394959496992689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64980938881053225325313837 24367852080394959496992689)
            ·
              refine ⟨18275889060296219622744517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24367852080394959496992689 18275889060296219622744517)
              ·
                refine ⟨3426729198805541179264597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18275889060296219622744517 3426729198805541179264597)
                ·
                  refine ⟨40156982798502435694507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3426729198805541179264597 40156982798502435694507)
                  ·
                    rfl

theorem cell23_703849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 8].length) (baseStart_703849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703849 prefixEnd_703849 := by exact prefixLift 703849
  have htrace : WordTrace (prefixWord ++ tailWord_703849) baseStart_703849 baseEnd_703849 := by
    simpa [prefixWord, tailWord_703849, baseEnd_703849] using wordTrace_append hprefix tailTrace_703849
  have hstable : (prefixWord ++ tailWord_703849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703849).length < 2 ^ (prefixWord ++ tailWord_703849).sum := by decide
  have hdescent : baseEnd_703849 < baseStart_703849 := by decide
  rcases family_descends (prefixWord ++ tailWord_703849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703893 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 5, 1, 3]
def baseStart_703893 : Nat := 118140960795 + 703893 * 2 ^ 59
def prefixEnd_703893 : Nat := 4983230072969 + 3 ^ 40 * 703893 * 2
def baseEnd_703893 : Nat := 361435438335319749100361

theorem tailTrace_703893 : CollatzResearch.WordTrace tailWord_703893 prefixEnd_703893 361435438335319749100361 := by
  unfold tailWord_703893
  simp only [CollatzResearch.WordTrace]
  refine ⟨25673086838923351198676333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17115391225948900799117555 25673086838923351198676333)
  ·
    refine ⟨9627407564596256699503625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25673086838923351198676333 9627407564596256699503625)
    ·
      refine ⟨7220555673447192524627719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9627407564596256699503625 7220555673447192524627719)
      ·
        refine ⟨10830833510170788786941579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7220555673447192524627719 10830833510170788786941579)
        ·
          refine ⟨16246250265256183180412369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10830833510170788786941579 16246250265256183180412369)
          ·
            refine ⟨12184687698942137385309277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16246250265256183180412369 12184687698942137385309277)
            ·
              refine ⟨4569257887103301519490979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12184687698942137385309277 4569257887103301519490979)
              ·
                refine ⟨6853886830654952279236469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4569257887103301519490979 6853886830654952279236469)
                ·
                  refine ⟨642551890373901776178419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6853886830654952279236469 642551890373901776178419)
                  ·
                    refine ⟨963827835560852664267629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 642551890373901776178419 963827835560852664267629)
                    ·
                      refine ⟨361435438335319749100361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 963827835560852664267629 361435438335319749100361)
                      ·
                        rfl

theorem cell23_703893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_703893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703893 prefixEnd_703893 := by exact prefixLift 703893
  have htrace : WordTrace (prefixWord ++ tailWord_703893) baseStart_703893 baseEnd_703893 := by
    simpa [prefixWord, tailWord_703893, baseEnd_703893] using wordTrace_append hprefix tailTrace_703893
  have hstable : (prefixWord ++ tailWord_703893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703893).length < 2 ^ (prefixWord ++ tailWord_703893).sum := by decide
  have hdescent : baseEnd_703893 < baseStart_703893 := by decide
  rcases family_descends (prefixWord ++ tailWord_703893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703936 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 5]
def baseStart_703936 : Nat := 118140960795 + 703936 * 2 ^ 59
def prefixEnd_703936 : Nat := 4983230072969 + 3 ^ 40 * 703936 * 2
def baseEnd_703936 : Nat := 361457518003463080862663

theorem tailTrace_703936 : CollatzResearch.WordTrace tailWord_703936 prefixEnd_703936 361457518003463080862663 := by
  unfold tailWord_703936
  simp only [CollatzResearch.WordTrace]
  refine ⟨12837327588883784771245831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17116436785178379694994441 12837327588883784771245831)
  ·
    refine ⟨19255991383325677156868747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12837327588883784771245831 19255991383325677156868747)
    ·
      refine ⟨28883987074988515735303121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19255991383325677156868747 28883987074988515735303121)
      ·
        refine ⟨21662990306241386801477341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28883987074988515735303121 21662990306241386801477341)
        ·
          refine ⟨8123621364840520050554003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21662990306241386801477341 8123621364840520050554003)
          ·
            refine ⟨12185432047260780075831005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8123621364840520050554003 12185432047260780075831005)
            ·
              refine ⟨4569537017722792528436627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12185432047260780075831005 4569537017722792528436627)
              ·
                refine ⟨6854305526584188792654941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4569537017722792528436627 6854305526584188792654941)
                ·
                  refine ⟨2570364572469070797245603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6854305526584188792654941 2570364572469070797245603)
                  ·
                    refine ⟨3855546858703606195868405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2570364572469070797245603 3855546858703606195868405)
                    ·
                      refine ⟨361457518003463080862663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3855546858703606195868405 361457518003463080862663)
                      ·
                        rfl

theorem cell23_703936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_703936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703936 prefixEnd_703936 := by exact prefixLift 703936
  have htrace : WordTrace (prefixWord ++ tailWord_703936) baseStart_703936 baseEnd_703936 := by
    simpa [prefixWord, tailWord_703936, baseEnd_703936] using wordTrace_append hprefix tailTrace_703936
  have hstable : (prefixWord ++ tailWord_703936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703936).length < 2 ^ (prefixWord ++ tailWord_703936).sum := by decide
  have hdescent : baseEnd_703936 < baseStart_703936 := by decide
  rcases family_descends (prefixWord ++ tailWord_703936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703973 : List Nat := [1, 3, 1, 5, 1, 3, 9]
def baseStart_703973 : Nat := 118140960795 + 703973 * 2 ^ 59
def prefixEnd_703973 : Nat := 4983230072969 + 3 ^ 40 * 703973 * 2
def baseEnd_703973 : Nat := 4462673046761474519753

theorem tailTrace_703973 : CollatzResearch.WordTrace tailWord_703973 prefixEnd_703973 4462673046761474519753 := by
  unfold tailWord_703973
  simp only [CollatzResearch.WordTrace]
  refine ⟨25676004678633524861588573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17117336452422349907725715 25676004678633524861588573)
  ·
    refine ⟨9628501754487571823095715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25676004678633524861588573 9628501754487571823095715)
    ·
      refine ⟨14442752631731357734643573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9628501754487571823095715 14442752631731357734643573)
      ·
        refine ⟨1354008059224814787622835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14442752631731357734643573 1354008059224814787622835)
        ·
          refine ⟨2031012088837222181434253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1354008059224814787622835 2031012088837222181434253)
          ·
            refine ⟨761629533313958318037845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2031012088837222181434253 761629533313958318037845)
            ·
              refine ⟨4462673046761474519753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 761629533313958318037845 4462673046761474519753)
              ·
                rfl

theorem cell23_703973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 9].length) (baseStart_703973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703973 prefixEnd_703973 := by exact prefixLift 703973
  have htrace : WordTrace (prefixWord ++ tailWord_703973) baseStart_703973 baseEnd_703973 := by
    simpa [prefixWord, tailWord_703973, baseEnd_703973] using wordTrace_append hprefix tailTrace_703973
  have hstable : (prefixWord ++ tailWord_703973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703973).length < 2 ^ (prefixWord ++ tailWord_703973).sum := by decide
  have hdescent : baseEnd_703973 < baseStart_703973 := by decide
  rcases family_descends (prefixWord ++ tailWord_703973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703993 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 2, 7, 2]
def baseStart_703993 : Nat := 118140960795 + 703993 * 2 ^ 59
def prefixEnd_703993 : Nat := 4983230072969 + 3 ^ 40 * 703993 * 2
def baseEnd_703993 : Nat := 361486786400769357849901

theorem tailTrace_703993 : CollatzResearch.WordTrace tailWord_703993 prefixEnd_703993 361486786400769357849901 := by
  unfold tailWord_703993
  simp only [CollatzResearch.WordTrace]
  refine ⟨25676734138561068277316633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17117822759040712184877755 25676734138561068277316633)
  ·
    refine ⟨19257550603920801207987475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25676734138561068277316633 19257550603920801207987475)
    ·
      refine ⟨28886325905881201811981213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19257550603920801207987475 28886325905881201811981213)
      ·
        refine ⟨10832372214705450679492955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28886325905881201811981213 10832372214705450679492955)
        ·
          refine ⟨16248558322058176019239433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10832372214705450679492955 16248558322058176019239433)
          ·
            refine ⟨12186418741543632014429575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16248558322058176019239433 12186418741543632014429575)
            ·
              refine ⟨18279628112315448021644363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12186418741543632014429575 18279628112315448021644363)
              ·
                refine ⟨27419442168473172032466545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18279628112315448021644363 27419442168473172032466545)
                ·
                  refine ⟨20564581626354879024349909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27419442168473172032466545 20564581626354879024349909)
                  ·
                    refine ⟨481982381867692477133201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20564581626354879024349909 481982381867692477133201)
                    ·
                      refine ⟨361486786400769357849901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 481982381867692477133201 361486786400769357849901)
                      ·
                        rfl

theorem cell23_703993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 7, 2].length) (baseStart_703993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703993 prefixEnd_703993 := by exact prefixLift 703993
  have htrace : WordTrace (prefixWord ++ tailWord_703993) baseStart_703993 baseEnd_703993 := by
    simpa [prefixWord, tailWord_703993, baseEnd_703993] using wordTrace_append hprefix tailTrace_703993
  have hstable : (prefixWord ++ tailWord_703993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703993).length < 2 ^ (prefixWord ++ tailWord_703993).sum := by decide
  have hdescent : baseEnd_703993 < baseStart_703993 := by decide
  rcases family_descends (prefixWord ++ tailWord_703993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704004 : List Nat := [2, 3, 2, 3, 2, 2, 1, 2, 1, 2, 3]
def baseStart_704004 : Nat := 118140960795 + 704004 * 2 ^ 59
def prefixEnd_704004 : Nat := 4983230072969 + 3 ^ 40 * 704004 * 2
def baseEnd_704004 : Nat := 361492434687968814812351

theorem tailTrace_704004 : CollatzResearch.WordTrace tailWord_704004 prefixEnd_704004 361492434687968814812351 := by
  unfold tailWord_704004
  simp only [CollatzResearch.WordTrace]
  refine ⟨12838567670760608577983533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17118090227680811437311377 12838567670760608577983533)
  ·
    refine ⟨4814462876535228216743825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12838567670760608577983533 4814462876535228216743825)
    ·
      refine ⟨3610847157401421162557869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4814462876535228216743825 3610847157401421162557869)
      ·
        refine ⟨1354067684025532935959201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3610847157401421162557869 1354067684025532935959201)
        ·
          refine ⟨1015550763019149701969401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1354067684025532935959201 1015550763019149701969401)
          ·
            refine ⟨761663072264362276477051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1015550763019149701969401 761663072264362276477051)
            ·
              refine ⟨1142494608396543414715577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761663072264362276477051 1142494608396543414715577)
              ·
                refine ⟨856870956297407561036683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1142494608396543414715577 856870956297407561036683)
                ·
                  refine ⟨1285306434446111341555025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 856870956297407561036683 1285306434446111341555025)
                  ·
                    refine ⟨963979825834583506166269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1285306434446111341555025 963979825834583506166269)
                    ·
                      refine ⟨361492434687968814812351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 963979825834583506166269 361492434687968814812351)
                      ·
                        rfl

theorem cell23_704004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_704004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704004 prefixEnd_704004 := by exact prefixLift 704004
  have htrace : WordTrace (prefixWord ++ tailWord_704004) baseStart_704004 baseEnd_704004 := by
    simpa [prefixWord, tailWord_704004, baseEnd_704004] using wordTrace_append hprefix tailTrace_704004
  have hstable : (prefixWord ++ tailWord_704004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704004).length < 2 ^ (prefixWord ++ tailWord_704004).sum := by decide
  have hdescent : baseEnd_704004 < baseStart_704004 := by decide
  rcases family_descends (prefixWord ++ tailWord_704004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704053 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_704053 : Nat := 118140960795 + 704053 * 2 ^ 59
def prefixEnd_704053 : Nat := 4983230072969 + 3 ^ 40 * 704053 * 2
def baseEnd_704053 : Nat := 361517595240039123099625

theorem tailTrace_704053 : CollatzResearch.WordTrace tailWord_704053 prefixEnd_704053 361517595240039123099625 := by
  unfold tailWord_704053
  simp only [CollatzResearch.WordTrace]
  refine ⟨25678922518343698524500813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17119281678895799016333875 25678922518343698524500813)
  ·
    refine ⟨9629595944378886946687805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25678922518343698524500813 9629595944378886946687805)
    ·
      refine ⟨3611098479142082605007927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9629595944378886946687805 3611098479142082605007927)
      ·
        refine ⟨5416647718713123907511891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3611098479142082605007927 5416647718713123907511891)
        ·
          refine ⟨8124971578069685861267837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5416647718713123907511891 8124971578069685861267837)
          ·
            refine ⟨3046864341776132197975439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8124971578069685861267837 3046864341776132197975439)
            ·
              refine ⟨4570296512664198296963159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3046864341776132197975439 4570296512664198296963159)
              ·
                refine ⟨6855444768996297445444739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4570296512664198296963159 6855444768996297445444739)
                ·
                  refine ⟨10283167153494446168167109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6855444768996297445444739 10283167153494446168167109)
                  ·
                    refine ⟨1928093841280208656531333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10283167153494446168167109 1928093841280208656531333)
                    ·
                      refine ⟨361517595240039123099625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1928093841280208656531333 361517595240039123099625)
                      ·
                        rfl

theorem cell23_704053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_704053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704053 prefixEnd_704053 := by exact prefixLift 704053
  have htrace : WordTrace (prefixWord ++ tailWord_704053) baseStart_704053 baseEnd_704053 := by
    simpa [prefixWord, tailWord_704053, baseEnd_704053] using wordTrace_append hprefix tailTrace_704053
  have hstable : (prefixWord ++ tailWord_704053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704053).length < 2 ^ (prefixWord ++ tailWord_704053).sum := by decide
  have hdescent : baseEnd_704053 < baseStart_704053 := by decide
  rcases family_descends (prefixWord ++ tailWord_704053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704057 : List Nat := [1, 2, 1, 5, 1, 3, 2, 1, 1, 4, 2]
def baseStart_704057 : Nat := 118140960795 + 704057 * 2 ^ 59
def prefixEnd_704057 : Nat := 4983230072969 + 3 ^ 40 * 704057 * 2
def baseEnd_704057 : Nat := 361519649162657107449607

theorem tailTrace_704057 : CollatzResearch.WordTrace tailWord_704057 prefixEnd_704057 361519649162657107449607 := by
  unfold tailWord_704057
  simp only [CollatzResearch.WordTrace]
  refine ⟨25679068410329207207646425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17119378940219471471764283 25679068410329207207646425)
  ·
    refine ⟨19259301307746905405734819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25679068410329207207646425 19259301307746905405734819)
    ·
      refine ⟨28888951961620358108602229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19259301307746905405734819 28888951961620358108602229)
      ·
        refine ⟨2708339246401908572681459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28888951961620358108602229 2708339246401908572681459)
        ·
          refine ⟨4062508869602862859022189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2708339246401908572681459 4062508869602862859022189)
          ·
            refine ⟨1523440826101073572133321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4062508869602862859022189 1523440826101073572133321)
            ·
              refine ⟨1142580619575805179099991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1523440826101073572133321 1142580619575805179099991)
              ·
                refine ⟨1713870929363707768649987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142580619575805179099991 1713870929363707768649987)
                ·
                  refine ⟨2570806394045561652974981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1713870929363707768649987 2570806394045561652974981)
                  ·
                    refine ⟨482026198883542809932809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2570806394045561652974981 482026198883542809932809)
                    ·
                      refine ⟨361519649162657107449607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 482026198883542809932809 361519649162657107449607)
                      ·
                        rfl

theorem cell23_704057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_704057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704057 prefixEnd_704057 := by exact prefixLift 704057
  have htrace : WordTrace (prefixWord ++ tailWord_704057) baseStart_704057 baseEnd_704057 := by
    simpa [prefixWord, tailWord_704057, baseEnd_704057] using wordTrace_append hprefix tailTrace_704057
  have hstable : (prefixWord ++ tailWord_704057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704057).length < 2 ^ (prefixWord ++ tailWord_704057).sum := by decide
  have hdescent : baseEnd_704057 < baseStart_704057 := by decide
  rcases family_descends (prefixWord ++ tailWord_704057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704063 : List Nat := [1, 1, 2, 2, 3, 4, 1, 2, 7]
def baseStart_704063 : Nat := 118140960795 + 704063 * 2 ^ 59
def prefixEnd_704063 : Nat := 4983230072969 + 3 ^ 40 * 704063 * 2
def baseEnd_704063 : Nat := 40169192227398231552731

theorem tailTrace_704063 : CollatzResearch.WordTrace tailWord_704063 prefixEnd_704063 40169192227398231552731 := by
  unfold tailWord_704063
  simp only [CollatzResearch.WordTrace]
  refine ⟨25679287248307470232364843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17119524832204980154909895 25679287248307470232364843)
  ·
    refine ⟨38518930872461205348547265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25679287248307470232364843 38518930872461205348547265)
    ·
      refine ⟨28889198154345904011410449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38518930872461205348547265 28889198154345904011410449)
      ·
        refine ⟨21666898615759428008557837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28889198154345904011410449 21666898615759428008557837)
        ·
          refine ⟨8125086980909785503209189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21666898615759428008557837 8125086980909785503209189)
          ·
            refine ⟨1523453808920584781851723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8125086980909785503209189 1523453808920584781851723)
            ·
              refine ⟨2285180713380877172777585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1523453808920584781851723 2285180713380877172777585)
              ·
                refine ⟨1713885535035657879583189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2285180713380877172777585 1713885535035657879583189)
                ·
                  refine ⟨40169192227398231552731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1713885535035657879583189 40169192227398231552731)
                  ·
                    rfl

theorem cell23_704063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 7].length) (baseStart_704063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704063 prefixEnd_704063 := by exact prefixLift 704063
  have htrace : WordTrace (prefixWord ++ tailWord_704063) baseStart_704063 baseEnd_704063 := by
    simpa [prefixWord, tailWord_704063, baseEnd_704063] using wordTrace_append hprefix tailTrace_704063
  have hstable : (prefixWord ++ tailWord_704063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704063).length < 2 ^ (prefixWord ++ tailWord_704063).sum := by decide
  have hdescent : baseEnd_704063 < baseStart_704063 := by decide
  rcases family_descends (prefixWord ++ tailWord_704063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704080 : List Nat := [2, 1, 1, 1, 1, 3, 6, 3, 5]
def baseStart_704080 : Nat := 118140960795 + 704080 * 2 ^ 59
def prefixEnd_704080 : Nat := 4983230072969 + 3 ^ 40 * 704080 * 2
def baseEnd_704080 : Nat := 40170162135301168606889

theorem tailTrace_704080 : CollatzResearch.WordTrace tailWord_704080 prefixEnd_704080 40170162135301168606889 := by
  unfold tailWord_704080
  simp only [CollatzResearch.WordTrace]
  refine ⟨12839953644622941067866847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17119938192830588090489129 12839953644622941067866847)
  ·
    refine ⟨19259930466934411601800271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12839953644622941067866847 19259930466934411601800271)
    ·
      refine ⟨28889895700401617402700407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19259930466934411601800271 28889895700401617402700407)
      ·
        refine ⟨43334843550602426104050611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28889895700401617402700407 43334843550602426104050611)
        ·
          refine ⟨65002265325903639156075917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43334843550602426104050611 65002265325903639156075917)
          ·
            refine ⟨24375849497213864683528469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65002265325903639156075917 24375849497213864683528469)
            ·
              refine ⟨1142617945181899907040397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24375849497213864683528469 1142617945181899907040397)
              ·
                refine ⟨428481729443212465140149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1142617945181899907040397 428481729443212465140149)
                ·
                  refine ⟨40170162135301168606889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 428481729443212465140149 40170162135301168606889)
                  ·
                    rfl

theorem cell23_704080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 5].length) (baseStart_704080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704080 prefixEnd_704080 := by exact prefixLift 704080
  have htrace : WordTrace (prefixWord ++ tailWord_704080) baseStart_704080 baseEnd_704080 := by
    simpa [prefixWord, tailWord_704080, baseEnd_704080] using wordTrace_append hprefix tailTrace_704080
  have hstable : (prefixWord ++ tailWord_704080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704080).length < 2 ^ (prefixWord ++ tailWord_704080).sum := by decide
  have hdescent : baseEnd_704080 < baseStart_704080 := by decide
  rcases family_descends (prefixWord ++ tailWord_704080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704103 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_704103 : Nat := 118140960795 + 704103 * 2 ^ 59
def prefixEnd_704103 : Nat := 4983230072969 + 3 ^ 40 * 704103 * 2
def baseEnd_704103 : Nat := 361543269272763927474395

theorem tailTrace_704103 : CollatzResearch.WordTrace tailWord_704103 prefixEnd_704103 361543269272763927474395 := by
  unfold tailWord_704103
  simp only [CollatzResearch.WordTrace]
  refine ⟨25680746168162557063820963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17120497445441704709213975 25680746168162557063820963)
  ·
    refine ⟨38521119252243835595731445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25680746168162557063820963 38521119252243835595731445)
    ·
      refine ⟨3611354929897859587099823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38521119252243835595731445 3611354929897859587099823)
      ·
        refine ⟨5417032394846789380649735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3611354929897859587099823 5417032394846789380649735)
        ·
          refine ⟨8125548592270184070974603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5417032394846789380649735 8125548592270184070974603)
          ·
            refine ⟨12188322888405276106461905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8125548592270184070974603 12188322888405276106461905)
            ·
              refine ⟨9141242166303957079846429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12188322888405276106461905 9141242166303957079846429)
              ·
                refine ⟨3427965812363983904942411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9141242166303957079846429 3427965812363983904942411)
                ·
                  refine ⟨5141948718545975857413617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3427965812363983904942411 5141948718545975857413617)
                  ·
                    refine ⟨3856461538909481893060213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5141948718545975857413617 3856461538909481893060213)
                    ·
                      refine ⟨361543269272763927474395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3856461538909481893060213 361543269272763927474395)
                      ·
                        rfl

theorem cell23_704103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_704103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704103 prefixEnd_704103 := by exact prefixLift 704103
  have htrace : WordTrace (prefixWord ++ tailWord_704103) baseStart_704103 baseEnd_704103 := by
    simpa [prefixWord, tailWord_704103, baseEnd_704103] using wordTrace_append hprefix tailTrace_704103
  have hstable : (prefixWord ++ tailWord_704103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704103).length < 2 ^ (prefixWord ++ tailWord_704103).sum := by decide
  have hdescent : baseEnd_704103 < baseStart_704103 := by decide
  rcases family_descends (prefixWord ++ tailWord_704103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704231 : List Nat := [1, 1, 5, 4, 1, 1, 1, 2, 3, 1, 3]
def baseStart_704231 : Nat := 118140960795 + 704231 * 2 ^ 59
def prefixEnd_704231 : Nat := 4983230072969 + 3 ^ 40 * 704231 * 2
def baseEnd_704231 : Nat := 361608994796539426673807

theorem tailTrace_704231 : CollatzResearch.WordTrace tailWord_704231 prefixEnd_704231 361608994796539426673807 := by
  unfold tailWord_704231
  simp only [CollatzResearch.WordTrace]
  refine ⟨25685414711698834924480547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17123609807799223282987031 25685414711698834924480547)
  ·
    refine ⟨38528122067548252386720821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25685414711698834924480547 38528122067548252386720821)
    ·
      refine ⟨3612011443832648661255077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38528122067548252386720821 3612011443832648661255077)
      ·
        refine ⟨677252145718621623985327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3612011443832648661255077 677252145718621623985327)
        ·
          refine ⟨1015878218577932435977991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677252145718621623985327 1015878218577932435977991)
          ·
            refine ⟨1523817327866898653966987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1015878218577932435977991 1523817327866898653966987)
            ·
              refine ⟨2285725991800347980950481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1523817327866898653966987 2285725991800347980950481)
              ·
                refine ⟨1714294493850260985712861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2285725991800347980950481 1714294493850260985712861)
                ·
                  refine ⟨642860435193847869642323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1714294493850260985712861 642860435193847869642323)
                  ·
                    refine ⟨964290652790771804463485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 642860435193847869642323 964290652790771804463485)
                    ·
                      refine ⟨361608994796539426673807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 964290652790771804463485 361608994796539426673807)
                      ·
                        rfl

theorem cell23_704231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_704231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704231 prefixEnd_704231 := by exact prefixLift 704231
  have htrace : WordTrace (prefixWord ++ tailWord_704231) baseStart_704231 baseEnd_704231 := by
    simpa [prefixWord, tailWord_704231, baseEnd_704231] using wordTrace_append hprefix tailTrace_704231
  have hstable : (prefixWord ++ tailWord_704231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704231).length < 2 ^ (prefixWord ++ tailWord_704231).sum := by decide
  have hdescent : baseEnd_704231 < baseStart_704231 := by decide
  rcases family_descends (prefixWord ++ tailWord_704231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704237 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_704237 : Nat := 118140960795 + 704237 * 2 ^ 59
def prefixEnd_704237 : Nat := 4983230072969 + 3 ^ 40 * 704237 * 2
def baseEnd_704237 : Nat := 361612075680466403198779

theorem tailTrace_704237 : CollatzResearch.WordTrace tailWord_704237 prefixEnd_704237 361612075680466403198779 := by
  unfold tailWord_704237
  simp only [CollatzResearch.WordTrace]
  refine ⟨25685633549677097949198965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17123755699784731966132643 25685633549677097949198965)
  ·
    refine ⟨2408028145282227932737403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25685633549677097949198965 2408028145282227932737403)
    ·
      refine ⟨3612042217923341899106105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2408028145282227932737403 3612042217923341899106105)
      ·
        refine ⟨2709031663442506424329579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3612042217923341899106105 2709031663442506424329579)
        ·
          refine ⟨4063547495163759636494369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2709031663442506424329579 4063547495163759636494369)
          ·
            refine ⟨3047660621372819727370777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4063547495163759636494369 3047660621372819727370777)
            ·
              refine ⟨2285745466029614795528083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3047660621372819727370777 2285745466029614795528083)
              ·
                refine ⟨3428618199044422193292125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2285745466029614795528083 3428618199044422193292125)
                ·
                  refine ⟨1285731824641658322484547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3428618199044422193292125 1285731824641658322484547)
                  ·
                    refine ⟨1928597736962487483726821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1285731824641658322484547 1928597736962487483726821)
                    ·
                      refine ⟨361612075680466403198779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1928597736962487483726821 361612075680466403198779)
                      ·
                        rfl

theorem cell23_704237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_704237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704237 prefixEnd_704237 := by exact prefixLift 704237
  have htrace : WordTrace (prefixWord ++ tailWord_704237) baseStart_704237 baseEnd_704237 := by
    simpa [prefixWord, tailWord_704237, baseEnd_704237] using wordTrace_append hprefix tailTrace_704237
  have hstable : (prefixWord ++ tailWord_704237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704237).length < 2 ^ (prefixWord ++ tailWord_704237).sum := by decide
  have hdescent : baseEnd_704237 < baseStart_704237 := by decide
  rcases family_descends (prefixWord ++ tailWord_704237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704243 : List Nat := [1, 1, 1, 2, 2, 3, 2, 11]
def baseStart_704243 : Nat := 118140960795 + 704243 * 2 ^ 59
def prefixEnd_704243 : Nat := 4983230072969 + 3 ^ 40 * 704243 * 2
def baseEnd_704243 : Nat := 13393153946829384434213

theorem tailTrace_704243 : CollatzResearch.WordTrace tailWord_704243 prefixEnd_704243 13393153946829384434213 := by
  unfold tailWord_704243
  simp only [CollatzResearch.WordTrace]
  refine ⟨25685852387655360973917383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17123901591770240649278255 25685852387655360973917383)
  ·
    refine ⟨38528778581483041460876075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25685852387655360973917383 38528778581483041460876075)
    ·
      refine ⟨57793167872224562191314113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38528778581483041460876075 57793167872224562191314113)
      ·
        refine ⟨43344875904168421643485585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57793167872224562191314113 43344875904168421643485585)
        ·
          refine ⟨32508656928126316232614189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43344875904168421643485585 32508656928126316232614189)
          ·
            refine ⟨12190746348047368587230321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32508656928126316232614189 12190746348047368587230321)
            ·
              refine ⟨9143059761035526440422741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12190746348047368587230321 9143059761035526440422741)
              ·
                refine ⟨13393153946829384434213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 9143059761035526440422741 13393153946829384434213)
                ·
                  rfl

theorem cell23_704243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 11].length) (baseStart_704243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704243 prefixEnd_704243 := by exact prefixLift 704243
  have htrace : WordTrace (prefixWord ++ tailWord_704243) baseStart_704243 baseEnd_704243 := by
    simpa [prefixWord, tailWord_704243, baseEnd_704243] using wordTrace_append hprefix tailTrace_704243
  have hstable : (prefixWord ++ tailWord_704243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704243).length < 2 ^ (prefixWord ++ tailWord_704243).sum := by decide
  have hdescent : baseEnd_704243 < baseStart_704243 := by decide
  rcases family_descends (prefixWord ++ tailWord_704243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704260 : List Nat := [2, 3, 2, 2, 1, 3, 10]
def baseStart_704260 : Nat := 118140960795 + 704260 * 2 ^ 59
def prefixEnd_704260 : Nat := 4983230072969 + 3 ^ 40 * 704260 * 2
def baseEnd_704260 : Nat := 4464492416487898928533

theorem tailTrace_704260 : CollatzResearch.WordTrace tailWord_704260 prefixEnd_704260 4464492416487898928533 := by
  unfold tailWord_704260
  simp only [CollatzResearch.WordTrace]
  refine ⟨12843236214296886438643117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17124314952395848584857489 12843236214296886438643117)
  ·
    refine ⟨4816213580361332414491169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12843236214296886438643117 4816213580361332414491169)
    ·
      refine ⟨3612160185270999310868377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4816213580361332414491169 3612160185270999310868377)
      ·
        refine ⟨2709120138953249483151283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3612160185270999310868377 2709120138953249483151283)
        ·
          refine ⟨4063680208429874224726925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2709120138953249483151283 4063680208429874224726925)
          ·
            refine ⟨1523880078161202834272597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4063680208429874224726925 1523880078161202834272597)
            ·
              refine ⟨4464492416487898928533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1523880078161202834272597 4464492416487898928533)
              ·
                rfl

theorem cell23_704260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 10].length) (baseStart_704260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704260 prefixEnd_704260 := by exact prefixLift 704260
  have htrace : WordTrace (prefixWord ++ tailWord_704260) baseStart_704260 baseEnd_704260 := by
    simpa [prefixWord, tailWord_704260, baseEnd_704260] using wordTrace_append hprefix tailTrace_704260
  have hstable : (prefixWord ++ tailWord_704260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704260).length < 2 ^ (prefixWord ++ tailWord_704260).sum := by decide
  have hdescent : baseEnd_704260 < baseStart_704260 := by decide
  rcases family_descends (prefixWord ++ tailWord_704260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704274 : List Nat := [3, 2, 4, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_704274 : Nat := 118140960795 + 704274 * 2 ^ 59
def prefixEnd_704274 : Nat := 4983230072969 + 3 ^ 40 * 704274 * 2
def baseEnd_704274 : Nat := 361631074464682758436109

theorem tailTrace_704274 : CollatzResearch.WordTrace tailWord_704274 prefixEnd_704274 361631074464682758436109 := by
  unfold tailWord_704274
  simp only [CollatzResearch.WordTrace]
  refine ⟨6421745762635763317073969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17124655367028702178863917 6421745762635763317073969)
  ·
    refine ⟨4816309321976822487805477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6421745762635763317073969 4816309321976822487805477)
    ·
      refine ⟨903057997870654216463527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4816309321976822487805477 903057997870654216463527)
      ·
        refine ⟨1354586996805981324695291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 903057997870654216463527 1354586996805981324695291)
        ·
          refine ⟨2031880495208971987042937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1354586996805981324695291 2031880495208971987042937)
          ·
            refine ⟨1523910371406728990282203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2031880495208971987042937 1523910371406728990282203)
            ·
              refine ⟨2285865557110093485423305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1523910371406728990282203 2285865557110093485423305)
              ·
                refine ⟨1714399167832570114067479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2285865557110093485423305 1714399167832570114067479)
                ·
                  refine ⟨2571598751748855171101219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1714399167832570114067479 2571598751748855171101219)
                  ·
                    refine ⟨3857398127623282756651829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2571598751748855171101219 3857398127623282756651829)
                    ·
                      refine ⟨361631074464682758436109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3857398127623282756651829 361631074464682758436109)
                      ·
                        rfl

theorem cell23_704274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_704274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704274 prefixEnd_704274 := by exact prefixLift 704274
  have htrace : WordTrace (prefixWord ++ tailWord_704274) baseStart_704274 baseEnd_704274 := by
    simpa [prefixWord, tailWord_704274, baseEnd_704274] using wordTrace_append hprefix tailTrace_704274
  have hstable : (prefixWord ++ tailWord_704274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704274).length < 2 ^ (prefixWord ++ tailWord_704274).sum := by decide
  have hdescent : baseEnd_704274 < baseStart_704274 := by decide
  rcases family_descends (prefixWord ++ tailWord_704274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704300 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 5]
def baseStart_704300 : Nat := 118140960795 + 704300 * 2 ^ 59
def prefixEnd_704300 : Nat := 4983230072969 + 3 ^ 40 * 704300 * 2
def baseEnd_704300 : Nat := 361644424961699656710989

theorem tailTrace_704300 : CollatzResearch.WordTrace tailWord_704300 prefixEnd_704300 361644424961699656710989 := by
  unfold tailWord_704300
  simp only [CollatzResearch.WordTrace]
  refine ⟨12843965674224429854371177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17125287565632573139161569 12843965674224429854371177)
  ·
    refine ⟨9632974255668322390778383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12843965674224429854371177 9632974255668322390778383)
    ·
      refine ⟨14449461383502483586167575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9632974255668322390778383 14449461383502483586167575)
      ·
        refine ⟨21674192075253725379251363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14449461383502483586167575 21674192075253725379251363)
        ·
          refine ⟨32511288112880588068877045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21674192075253725379251363 32511288112880588068877045)
          ·
            refine ⟨3047933260582555131457223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32511288112880588068877045 3047933260582555131457223)
            ·
              refine ⟨4571899890873832697185835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3047933260582555131457223 4571899890873832697185835)
              ·
                refine ⟨6857849836310749045778753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4571899890873832697185835 6857849836310749045778753)
                ·
                  refine ⟨5143387377233061784334065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6857849836310749045778753 5143387377233061784334065)
                  ·
                    refine ⟨3857540532924796338250549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5143387377233061784334065 3857540532924796338250549)
                    ·
                      refine ⟨361644424961699656710989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3857540532924796338250549 361644424961699656710989)
                      ·
                        rfl

theorem cell23_704300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_704300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704300 prefixEnd_704300 := by exact prefixLift 704300
  have htrace : WordTrace (prefixWord ++ tailWord_704300) baseStart_704300 baseEnd_704300 := by
    simpa [prefixWord, tailWord_704300, baseEnd_704300] using wordTrace_append hprefix tailTrace_704300
  have hstable : (prefixWord ++ tailWord_704300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704300).length < 2 ^ (prefixWord ++ tailWord_704300).sum := by decide
  have hdescent : baseEnd_704300 < baseStart_704300 := by decide
  rcases family_descends (prefixWord ++ tailWord_704300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704330 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 1, 3, 5]
def baseStart_704330 : Nat := 118140960795 + 704330 * 2 ^ 59
def prefixEnd_704330 : Nat := 4983230072969 + 3 ^ 40 * 704330 * 2
def baseEnd_704330 : Nat := 361659829381334539335851

theorem tailTrace_704330 : CollatzResearch.WordTrace tailWord_704330 prefixEnd_704330 361659829381334539335851 := by
  unfold tailWord_704330
  simp only [CollatzResearch.WordTrace]
  refine ⟨6422256384585043708083611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17126017025560116554889629 6422256384585043708083611)
  ·
    refine ⟨9633384576877565562125417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6422256384585043708083611 9633384576877565562125417)
    ·
      refine ⟨7225038432658174171594063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9633384576877565562125417 7225038432658174171594063)
      ·
        refine ⟨10837557648987261257391095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7225038432658174171594063 10837557648987261257391095)
        ·
          refine ⟨16256336473480891886086643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10837557648987261257391095 16256336473480891886086643)
          ·
            refine ⟨24384504710221337829129965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16256336473480891886086643 24384504710221337829129965)
            ·
              refine ⟨9144189266333001685923737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24384504710221337829129965 9144189266333001685923737)
              ·
                refine ⟨6858141949749751264442803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9144189266333001685923737 6858141949749751264442803)
                ·
                  refine ⟨10287212924624626896664205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6858141949749751264442803 10287212924624626896664205)
                  ·
                    refine ⟨3857704846734235086249077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10287212924624626896664205 3857704846734235086249077)
                    ·
                      refine ⟨361659829381334539335851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3857704846734235086249077 361659829381334539335851)
                      ·
                        rfl

theorem cell23_704330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_704330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704330 prefixEnd_704330 := by exact prefixLift 704330
  have htrace : WordTrace (prefixWord ++ tailWord_704330) baseStart_704330 baseEnd_704330 := by
    simpa [prefixWord, tailWord_704330, baseEnd_704330] using wordTrace_append hprefix tailTrace_704330
  have hstable : (prefixWord ++ tailWord_704330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704330).length < 2 ^ (prefixWord ++ tailWord_704330).sum := by decide
  have hdescent : baseEnd_704330 < baseStart_704330 := by decide
  rcases family_descends (prefixWord ++ tailWord_704330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704338 : List Nat := [3, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3]
def baseStart_704338 : Nat := 118140960795 + 704338 * 2 ^ 59
def prefixEnd_704338 : Nat := 4983230072969 + 3 ^ 40 * 704338 * 2
def baseEnd_704338 : Nat := 361663937226570508035815

theorem tailTrace_704338 : CollatzResearch.WordTrace tailWord_704338 prefixEnd_704338 361663937226570508035815 := by
  unfold tailWord_704338
  simp only [CollatzResearch.WordTrace]
  refine ⟨6422329330577798049656417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17126211548207461465750445 6422329330577798049656417)
  ·
    refine ⟨4816746997933348537242313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6422329330577798049656417 4816746997933348537242313)
    ·
      refine ⟨3612560248450011402931735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4816746997933348537242313 3612560248450011402931735)
      ·
        refine ⟨5418840372675017104397603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3612560248450011402931735 5418840372675017104397603)
        ·
          refine ⟨8128260559012525656596405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5418840372675017104397603 8128260559012525656596405)
          ·
            refine ⟨762024427407424280305913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8128260559012525656596405 762024427407424280305913)
            ·
              refine ⟨571518320555568210229435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 762024427407424280305913 571518320555568210229435)
              ·
                refine ⟨857277480833352315344153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 571518320555568210229435 857277480833352315344153)
                ·
                  refine ⟨642958110625014236508115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 857277480833352315344153 642958110625014236508115)
                  ·
                    refine ⟨964437165937521354762173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 642958110625014236508115 964437165937521354762173)
                    ·
                      refine ⟨361663937226570508035815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 964437165937521354762173 361663937226570508035815)
                      ·
                        rfl

theorem cell23_704338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_704338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704338 prefixEnd_704338 := by exact prefixLift 704338
  have htrace : WordTrace (prefixWord ++ tailWord_704338) baseStart_704338 baseEnd_704338 := by
    simpa [prefixWord, tailWord_704338, baseEnd_704338] using wordTrace_append hprefix tailTrace_704338
  have hstable : (prefixWord ++ tailWord_704338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704338).length < 2 ^ (prefixWord ++ tailWord_704338).sum := by decide
  have hdescent : baseEnd_704338 < baseStart_704338 := by decide
  rcases family_descends (prefixWord ++ tailWord_704338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704377 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 2, 3, 3]
def baseStart_704377 : Nat := 118140960795 + 704377 * 2 ^ 59
def prefixEnd_704377 : Nat := 4983230072969 + 3 ^ 40 * 704377 * 2
def baseEnd_704377 : Nat := 361683962972095855448135

theorem tailTrace_704377 : CollatzResearch.WordTrace tailWord_704377 prefixEnd_704377 361683962972095855448135 := by
  unfold tailWord_704377
  simp only [CollatzResearch.WordTrace]
  refine ⟨25690739769169901859295385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17127159846113267906196923 25690739769169901859295385)
  ·
    refine ⟨19268054826877426394471539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25690739769169901859295385 19268054826877426394471539)
    ·
      refine ⟨28902082240316139591707309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19268054826877426394471539 28902082240316139591707309)
      ·
        refine ⟨10838280840118552346890241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28902082240316139591707309 10838280840118552346890241)
        ·
          refine ⟨8128710630088914260167681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10838280840118552346890241 8128710630088914260167681)
          ·
            refine ⟨6096532972566685695125761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8128710630088914260167681 6096532972566685695125761)
            ·
              refine ⟨4572399729425014271344321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6096532972566685695125761 4572399729425014271344321)
              ·
                refine ⟨3429299797068760703508241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4572399729425014271344321 3429299797068760703508241)
                ·
                  refine ⟨2571974847801570527631181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3429299797068760703508241 2571974847801570527631181)
                  ·
                    refine ⟨964490567925588947861693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2571974847801570527631181 964490567925588947861693)
                    ·
                      refine ⟨361683962972095855448135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 964490567925588947861693 361683962972095855448135)
                      ·
                        rfl

theorem cell23_704377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_704377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704377 prefixEnd_704377 := by exact prefixLift 704377
  have htrace : WordTrace (prefixWord ++ tailWord_704377) baseStart_704377 baseEnd_704377 := by
    simpa [prefixWord, tailWord_704377, baseEnd_704377] using wordTrace_append hprefix tailTrace_704377
  have hstable : (prefixWord ++ tailWord_704377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704377).length < 2 ^ (prefixWord ++ tailWord_704377).sum := by decide
  have hdescent : baseEnd_704377 < baseStart_704377 := by decide
  rcases family_descends (prefixWord ++ tailWord_704377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704380 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 5, 7]
def baseStart_704380 : Nat := 118140960795 + 704380 * 2 ^ 59
def prefixEnd_704380 : Nat := 4983230072969 + 3 ^ 40 * 704380 * 2
def baseEnd_704380 : Nat := 120561834471353114570207

theorem tailTrace_704380 : CollatzResearch.WordTrace tailWord_704380 prefixEnd_704380 120561834471353114570207 := by
  unfold tailWord_704380
  simp only [CollatzResearch.WordTrace]
  refine ⟨12845424594079516685827297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17127232792106022247769729 12845424594079516685827297)
  ·
    refine ⟨9634068445559637514370473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12845424594079516685827297 9634068445559637514370473)
    ·
      refine ⟨7225551334169728135777855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9634068445559637514370473 7225551334169728135777855)
      ·
        refine ⟨10838327001254592203666783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7225551334169728135777855 10838327001254592203666783)
        ·
          refine ⟨16257490501881888305500175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10838327001254592203666783 16257490501881888305500175)
          ·
            refine ⟨24386235752822832458250263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16257490501881888305500175 24386235752822832458250263)
            ·
              refine ⟨36579353629234248687375395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24386235752822832458250263 36579353629234248687375395)
              ·
                refine ⟨54869030443851373031063093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36579353629234248687375395 54869030443851373031063093)
                ·
                  refine ⟨5143971604111066221662165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54869030443851373031063093 5143971604111066221662165)
                  ·
                    refine ⟨120561834471353114570207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5143971604111066221662165 120561834471353114570207)
                    ·
                      rfl

theorem cell23_704380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_704380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704380 prefixEnd_704380 := by exact prefixLift 704380
  have htrace : WordTrace (prefixWord ++ tailWord_704380) baseStart_704380 baseEnd_704380 := by
    simpa [prefixWord, tailWord_704380, baseEnd_704380] using wordTrace_append hprefix tailTrace_704380
  have hstable : (prefixWord ++ tailWord_704380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704380).length < 2 ^ (prefixWord ++ tailWord_704380).sum := by decide
  have hdescent : baseEnd_704380 < baseStart_704380 := by decide
  rcases family_descends (prefixWord ++ tailWord_704380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704524 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 3, 1, 4]
def baseStart_704524 : Nat := 118140960795 + 704524 * 2 ^ 59
def prefixEnd_704524 : Nat := 4983230072969 + 3 ^ 40 * 704524 * 2
def baseEnd_704524 : Nat := 361759444628306780309959

theorem tailTrace_704524 : CollatzResearch.WordTrace tailWord_704524 prefixEnd_704524 361759444628306780309959 := by
  unfold tailWord_704524
  simp only [CollatzResearch.WordTrace]
  refine ⟨12848050649818672982448313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17130734199758230643264417 12848050649818672982448313)
  ·
    refine ⟨9636037987364004736836235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12848050649818672982448313 9636037987364004736836235)
    ·
      refine ⟨14454056981046007105254353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9636037987364004736836235 14454056981046007105254353)
      ·
        refine ⟨10840542735784505328940765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14454056981046007105254353 10840542735784505328940765)
        ·
          refine ⟨4065203525919189498352787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10840542735784505328940765 4065203525919189498352787)
          ·
            refine ⟨6097805288878784247529181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4065203525919189498352787 6097805288878784247529181)
            ·
              refine ⟨2286676983329544092823443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6097805288878784247529181 2286676983329544092823443)
              ·
                refine ⟨3430015474994316139235165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2286676983329544092823443 3430015474994316139235165)
                ·
                  refine ⟨1286255803122868552213187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3430015474994316139235165 1286255803122868552213187)
                  ·
                    refine ⟨1929383704684302828319781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1286255803122868552213187 1929383704684302828319781)
                    ·
                      refine ⟨361759444628306780309959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1929383704684302828319781 361759444628306780309959)
                      ·
                        rfl

theorem cell23_704524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_704524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704524 prefixEnd_704524 := by exact prefixLift 704524
  have htrace : WordTrace (prefixWord ++ tailWord_704524) baseStart_704524 baseEnd_704524 := by
    simpa [prefixWord, tailWord_704524, baseEnd_704524] using wordTrace_append hprefix tailTrace_704524
  have hstable : (prefixWord ++ tailWord_704524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704524).length < 2 ^ (prefixWord ++ tailWord_704524).sum := by decide
  have hdescent : baseEnd_704524 < baseStart_704524 := by decide
  rcases family_descends (prefixWord ++ tailWord_704524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704552 : List Nat := [2, 1, 5, 3, 1, 1, 1, 4, 1, 1, 3]
def baseStart_704552 : Nat := 118140960795 + 704552 * 2 ^ 59
def prefixEnd_704552 : Nat := 4983230072969 + 3 ^ 40 * 704552 * 2
def baseEnd_704552 : Nat := 361773822086632670759831

theorem tailTrace_704552 : CollatzResearch.WordTrace tailWord_704552 prefixEnd_704552 361773822086632670759831 := by
  unfold tailWord_704552
  simp only [CollatzResearch.WordTrace]
  refine ⟨12848561271767953373457955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17131415029023937831277273 12848561271767953373457955)
  ·
    refine ⟨19272841907651930060186933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12848561271767953373457955 19272841907651930060186933)
    ·
      refine ⟨1806828928842368443142525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19272841907651930060186933 1806828928842368443142525)
      ·
        refine ⟨677560848315888166178447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1806828928842368443142525 677560848315888166178447)
        ·
          refine ⟨1016341272473832249267671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677560848315888166178447 1016341272473832249267671)
          ·
            refine ⟨1524511908710748373901507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1016341272473832249267671 1524511908710748373901507)
            ·
              refine ⟨2286767863066122560852261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1524511908710748373901507 2286767863066122560852261)
              ·
                refine ⟨428768974324897980159799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2286767863066122560852261 428768974324897980159799)
                ·
                  refine ⟨643153461487346970239699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 428768974324897980159799 643153461487346970239699)
                  ·
                    refine ⟨964730192231020455359549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 643153461487346970239699 964730192231020455359549)
                    ·
                      refine ⟨361773822086632670759831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 964730192231020455359549 361773822086632670759831)
                      ·
                        rfl

theorem cell23_704552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_704552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704552 prefixEnd_704552 := by exact prefixLift 704552
  have htrace : WordTrace (prefixWord ++ tailWord_704552) baseStart_704552 baseEnd_704552 := by
    simpa [prefixWord, tailWord_704552, baseEnd_704552] using wordTrace_append hprefix tailTrace_704552
  have hstable : (prefixWord ++ tailWord_704552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704552).length < 2 ^ (prefixWord ++ tailWord_704552).sum := by decide
  have hdescent : baseEnd_704552 < baseStart_704552 := by decide
  rcases family_descends (prefixWord ++ tailWord_704552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704567 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 6]
def baseStart_704567 : Nat := 118140960795 + 704567 * 2 ^ 59
def prefixEnd_704567 : Nat := 4983230072969 + 3 ^ 40 * 704567 * 2
def baseEnd_704567 : Nat := 361781524296450112072261

theorem tailTrace_704567 : CollatzResearch.WordTrace tailWord_704567 prefixEnd_704567 361781524296450112072261 := by
  unfold tailWord_704567
  simp only [CollatzResearch.WordTrace]
  refine ⟨25697669638481564308711955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17131779758987709539141303 25697669638481564308711955)
  ·
    refine ⟨38546504457722346463067933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25697669638481564308711955 38546504457722346463067933)
    ·
      refine ⟨14454939171645879923650475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38546504457722346463067933 14454939171645879923650475)
      ·
        refine ⟨21682408757468819885475713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14454939171645879923650475 21682408757468819885475713)
        ·
          refine ⟨16261806568101614914106785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21682408757468819885475713 16261806568101614914106785)
          ·
            refine ⟨12196354926076211185580089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16261806568101614914106785 12196354926076211185580089)
            ·
              refine ⟨9147266194557158389185067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12196354926076211185580089 9147266194557158389185067)
              ·
                refine ⟨13720899291835737583777601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9147266194557158389185067 13720899291835737583777601)
                ·
                  refine ⟨10290674468876803187833201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13720899291835737583777601 10290674468876803187833201)
                  ·
                    refine ⟨7718005851657602390874901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10290674468876803187833201 7718005851657602390874901)
                    ·
                      refine ⟨361781524296450112072261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7718005851657602390874901 361781524296450112072261)
                      ·
                        rfl

theorem cell23_704567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_704567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704567 prefixEnd_704567 := by exact prefixLift 704567
  have htrace : WordTrace (prefixWord ++ tailWord_704567) baseStart_704567 baseEnd_704567 := by
    simpa [prefixWord, tailWord_704567, baseEnd_704567] using wordTrace_append hprefix tailTrace_704567
  have hstable : (prefixWord ++ tailWord_704567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704567).length < 2 ^ (prefixWord ++ tailWord_704567).sum := by decide
  have hdescent : baseEnd_704567 < baseStart_704567 := by decide
  rcases family_descends (prefixWord ++ tailWord_704567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704587 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 5]
def baseStart_704587 : Nat := 118140960795 + 704587 * 2 ^ 59
def prefixEnd_704587 : Nat := 4983230072969 + 3 ^ 40 * 704587 * 2
def baseEnd_704587 : Nat := 361791793909540033822169

theorem tailTrace_704587 : CollatzResearch.WordTrace tailWord_704587 prefixEnd_704587 361791793909540033822169 := by
  unfold tailWord_704587
  simp only [CollatzResearch.WordTrace]
  refine ⟨25698399098409107724440015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17132266065606071816293343 25698399098409107724440015)
  ·
    refine ⟨38547598647613661586660023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25698399098409107724440015 38547598647613661586660023)
    ·
      refine ⟨57821397971420492379990035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38547598647613661586660023 57821397971420492379990035)
      ·
        refine ⟨86732096957130738569985053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57821397971420492379990035 86732096957130738569985053)
        ·
          refine ⟨32524536358924026963744395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86732096957130738569985053 32524536358924026963744395)
          ·
            refine ⟨48786804538386040445616593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32524536358924026963744395 48786804538386040445616593)
            ·
              refine ⟨36590103403789530334212445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48786804538386040445616593 36590103403789530334212445)
              ·
                refine ⟨13721288776421073875329667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36590103403789530334212445 13721288776421073875329667)
                ·
                  refine ⟨20581933164631610812994501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13721288776421073875329667 20581933164631610812994501)
                  ·
                    refine ⟨3859112468368427027436469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20581933164631610812994501 3859112468368427027436469)
                    ·
                      refine ⟨361791793909540033822169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3859112468368427027436469 361791793909540033822169)
                      ·
                        rfl

theorem cell23_704587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 5].length) (baseStart_704587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704587 prefixEnd_704587 := by exact prefixLift 704587
  have htrace : WordTrace (prefixWord ++ tailWord_704587) baseStart_704587 baseEnd_704587 := by
    simpa [prefixWord, tailWord_704587, baseEnd_704587] using wordTrace_append hprefix tailTrace_704587
  have hstable : (prefixWord ++ tailWord_704587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704587).length < 2 ^ (prefixWord ++ tailWord_704587).sum := by decide
  have hdescent : baseEnd_704587 < baseStart_704587 := by decide
  rcases family_descends (prefixWord ++ tailWord_704587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704608 : List Nat := [2, 1, 1, 3, 2, 3, 3, 2, 2, 1, 3]
def baseStart_704608 : Nat := 118140960795 + 704608 * 2 ^ 59
def prefixEnd_704608 : Nat := 4983230072969 + 3 ^ 40 * 704608 * 2
def baseEnd_704608 : Nat := 361802577003284451659573

theorem tailTrace_704608 : CollatzResearch.WordTrace tailWord_704608 prefixEnd_704608 361802577003284451659573 := by
  unfold tailWord_704608
  simp only [CollatzResearch.WordTrace]
  refine ⟨12849582515666514155477239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17132776687555352207302985 12849582515666514155477239)
  ·
    refine ⟨19274373773499771233215859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12849582515666514155477239 19274373773499771233215859)
    ·
      refine ⟨28911560660249656849823789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19274373773499771233215859 28911560660249656849823789)
      ·
        refine ⟨10841835247593621318683921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28911560660249656849823789 10841835247593621318683921)
        ·
          refine ⟨8131376435695215989012941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10841835247593621318683921 8131376435695215989012941)
          ·
            refine ⟨3049266163385705995879853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8131376435695215989012941 3049266163385705995879853)
            ·
              refine ⟨1143474811269639748454945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3049266163385705995879853 1143474811269639748454945)
              ·
                refine ⟨857606108452229811341209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1143474811269639748454945 857606108452229811341209)
                ·
                  refine ⟨643204581339172358505907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 857606108452229811341209 643204581339172358505907)
                  ·
                    refine ⟨964806872008758537758861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 643204581339172358505907 964806872008758537758861)
                    ·
                      refine ⟨361802577003284451659573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 964806872008758537758861 361802577003284451659573)
                      ·
                        rfl

theorem cell23_704608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_704608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704608 prefixEnd_704608 := by exact prefixLift 704608
  have htrace : WordTrace (prefixWord ++ tailWord_704608) baseStart_704608 baseEnd_704608 := by
    simpa [prefixWord, tailWord_704608, baseEnd_704608] using wordTrace_append hprefix tailTrace_704608
  have hstable : (prefixWord ++ tailWord_704608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704608).length < 2 ^ (prefixWord ++ tailWord_704608).sum := by decide
  have hdescent : baseEnd_704608 < baseStart_704608 := by decide
  rcases family_descends (prefixWord ++ tailWord_704608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704624 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 2, 6]
def baseStart_704624 : Nat := 118140960795 + 704624 * 2 ^ 59
def prefixEnd_704624 : Nat := 4983230072969 + 3 ^ 40 * 704624 * 2
def baseEnd_704624 : Nat := 120603597564585463019833

theorem tailTrace_704624 : CollatzResearch.WordTrace tailWord_704624 prefixEnd_704624 120603597564585463019833 := by
  unfold tailWord_704624
  simp only [CollatzResearch.WordTrace]
  refine ⟨12849874299637531521768463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17133165732850042029024617 12849874299637531521768463)
  ·
    refine ⟨19274811449456297282652695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12849874299637531521768463 19274811449456297282652695)
    ·
      refine ⟨28912217174184445923979043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19274811449456297282652695 28912217174184445923979043)
      ·
        refine ⟨43368325761276668885968565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28912217174184445923979043 43368325761276668885968565)
        ·
          refine ⟨4065780540119687708059553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43368325761276668885968565 4065780540119687708059553)
          ·
            refine ⟨3049335405089765781044665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4065780540119687708059553 3049335405089765781044665)
            ·
              refine ⟨2287001553817324335783499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3049335405089765781044665 2287001553817324335783499)
              ·
                refine ⟨3430502330725986503675249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2287001553817324335783499 3430502330725986503675249)
                ·
                  refine ⟨2572876748044489877756437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3430502330725986503675249 2572876748044489877756437)
                  ·
                    refine ⟨120603597564585463019833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2572876748044489877756437 120603597564585463019833)
                    ·
                      rfl

theorem cell23_704624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 2, 6].length) (baseStart_704624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704624 prefixEnd_704624 := by exact prefixLift 704624
  have htrace : WordTrace (prefixWord ++ tailWord_704624) baseStart_704624 baseEnd_704624 := by
    simpa [prefixWord, tailWord_704624, baseEnd_704624] using wordTrace_append hprefix tailTrace_704624
  have hstable : (prefixWord ++ tailWord_704624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704624).length < 2 ^ (prefixWord ++ tailWord_704624).sum := by decide
  have hdescent : baseEnd_704624 < baseStart_704624 := by decide
  rcases family_descends (prefixWord ++ tailWord_704624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704627 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 10]
def baseStart_704627 : Nat := 118140960795 + 704627 * 2 ^ 59
def prefixEnd_704627 : Nat := 4983230072969 + 3 ^ 40 * 704627 * 2
def baseEnd_704627 : Nat := 361812333135719877321985

theorem tailTrace_704627 : CollatzResearch.WordTrace tailWord_704627 prefixEnd_704627 361812333135719877321985 := by
  unfold tailWord_704627
  simp only [CollatzResearch.WordTrace]
  refine ⟨25699858018264194555896135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17133238678842796370597423 25699858018264194555896135)
  ·
    refine ⟨38549787027396291833844203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25699858018264194555896135 38549787027396291833844203)
    ·
      refine ⟨57824680541094437750766305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38549787027396291833844203 57824680541094437750766305)
      ·
        refine ⟨43368510405820828313074729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57824680541094437750766305 43368510405820828313074729)
        ·
          refine ⟨32526382804365621234806047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43368510405820828313074729 32526382804365621234806047)
          ·
            refine ⟨48789574206548431852209071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32526382804365621234806047 48789574206548431852209071)
            ·
              refine ⟨73184361309822647778313607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48789574206548431852209071 73184361309822647778313607)
              ·
                refine ⟨109776541964733971667470411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73184361309822647778313607 109776541964733971667470411)
                ·
                  refine ⟨164664812947100957501205617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109776541964733971667470411 164664812947100957501205617)
                  ·
                    refine ⟨123498609710325718125904213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 164664812947100957501205617 123498609710325718125904213)
                    ·
                      refine ⟨361812333135719877321985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 123498609710325718125904213 361812333135719877321985)
                      ·
                        rfl

theorem cell23_704627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_704627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704627 prefixEnd_704627 := by exact prefixLift 704627
  have htrace : WordTrace (prefixWord ++ tailWord_704627) baseStart_704627 baseEnd_704627 := by
    simpa [prefixWord, tailWord_704627, baseEnd_704627] using wordTrace_append hprefix tailTrace_704627
  have hstable : (prefixWord ++ tailWord_704627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704627).length < 2 ^ (prefixWord ++ tailWord_704627).sum := by decide
  have hdescent : baseEnd_704627 < baseStart_704627 := by decide
  rcases family_descends (prefixWord ++ tailWord_704627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704671 : List Nat := [1, 1, 2, 6, 1, 1, 3, 1, 7]
def baseStart_704671 : Nat := 118140960795 + 704671 * 2 ^ 59
def prefixEnd_704671 : Nat := 4983230072969 + 3 ^ 40 * 704671 * 2
def baseEnd_704671 : Nat := 40203880698279745019087

theorem tailTrace_704671 : CollatzResearch.WordTrace tailWord_704671 prefixEnd_704671 40203880698279745019087 := by
  unfold tailWord_704671
  simp only [CollatzResearch.WordTrace]
  refine ⟨25701462830104790070497867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17134308553403193380331911 25701462830104790070497867)
  ·
    refine ⟨38552194245157185105746801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25701462830104790070497867 38552194245157185105746801)
    ·
      refine ⟨28914145683867888829310101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38552194245157185105746801 28914145683867888829310101)
      ·
        refine ⟨1355350578931307288873911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28914145683867888829310101 1355350578931307288873911)
        ·
          refine ⟨2033025868396960933310867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1355350578931307288873911 2033025868396960933310867)
          ·
            refine ⟨3049538802595441399966301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2033025868396960933310867 3049538802595441399966301)
            ·
              refine ⟨1143577050973290524987363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3049538802595441399966301 1143577050973290524987363)
              ·
                refine ⟨1715365576459935787481045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1143577050973290524987363 1715365576459935787481045)
                ·
                  refine ⟨40203880698279745019087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1715365576459935787481045 40203880698279745019087)
                  ·
                    rfl

theorem cell23_704671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 7].length) (baseStart_704671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704671 prefixEnd_704671 := by exact prefixLift 704671
  have htrace : WordTrace (prefixWord ++ tailWord_704671) baseStart_704671 baseEnd_704671 := by
    simpa [prefixWord, tailWord_704671, baseEnd_704671] using wordTrace_append hprefix tailTrace_704671
  have hstable : (prefixWord ++ tailWord_704671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704671).length < 2 ^ (prefixWord ++ tailWord_704671).sum := by decide
  have hdescent : baseEnd_704671 < baseStart_704671 := by decide
  rcases family_descends (prefixWord ++ tailWord_704671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704686 : List Nat := [4, 1, 4, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_704686 : Nat := 118140960795 + 704686 * 2 ^ 59
def prefixEnd_704686 : Nat := 4983230072969 + 3 ^ 40 * 704686 * 2
def baseEnd_704686 : Nat := 361842628494335146484215

theorem tailTrace_704686 : CollatzResearch.WordTrace tailWord_704686 prefixEnd_704686 361842628494335146484215 := by
  unfold tailWord_704686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3212751240631305954036739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17134673283366965088195941 3212751240631305954036739)
  ·
    refine ⟨4819126860946958931055109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3212751240631305954036739 4819126860946958931055109)
    ·
      refine ⟨903586286427554799572833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4819126860946958931055109 903586286427554799572833)
      ·
        refine ⟨677689714820666099679625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 903586286427554799572833 677689714820666099679625)
        ·
          refine ⟨508267286115499574759719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 677689714820666099679625 508267286115499574759719)
          ·
            refine ⟨762400929173249362139579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508267286115499574759719 762400929173249362139579)
            ·
              refine ⟨1143601393759874043209369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 762400929173249362139579 1143601393759874043209369)
              ·
                refine ⟨857701045319905532407027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1143601393759874043209369 857701045319905532407027)
                ·
                  refine ⟨1286551567979858298610541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 857701045319905532407027 1286551567979858298610541)
                  ·
                    refine ⟨482456837992446861978953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1286551567979858298610541 482456837992446861978953)
                    ·
                      refine ⟨361842628494335146484215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 482456837992446861978953 361842628494335146484215)
                      ·
                        rfl

theorem cell23_704686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_704686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704686 prefixEnd_704686 := by exact prefixLift 704686
  have htrace : WordTrace (prefixWord ++ tailWord_704686) baseStart_704686 baseEnd_704686 := by
    simpa [prefixWord, tailWord_704686, baseEnd_704686] using wordTrace_append hprefix tailTrace_704686
  have hstable : (prefixWord ++ tailWord_704686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704686).length < 2 ^ (prefixWord ++ tailWord_704686).sum := by decide
  have hdescent : baseEnd_704686 < baseStart_704686 := by decide
  rcases family_descends (prefixWord ++ tailWord_704686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704721 : List Nat := [1, 2, 2, 1, 2, 2, 4, 2, 2, 1, 4]
def baseStart_704721 : Nat := 118140960795 + 704721 * 2 ^ 59
def prefixEnd_704721 : Nat := 4983230072969 + 3 ^ 40 * 704721 * 2
def baseEnd_704721 : Nat := 361860600317242509546553

theorem tailTrace_704721 : CollatzResearch.WordTrace tailWord_704721 prefixEnd_704721 361860600317242509546553 := by
  unfold tailWord_704721
  simp only [CollatzResearch.WordTrace]
  refine ⟨25703286479923648609818017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17135524319949099073212011 25703286479923648609818017)
  ·
    refine ⟨19277464859942736457363513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25703286479923648609818017 19277464859942736457363513)
    ·
      refine ⟨14458098644957052343022635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19277464859942736457363513 14458098644957052343022635)
      ·
        refine ⟨21687147967435578514533953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14458098644957052343022635 21687147967435578514533953)
        ·
          refine ⟨16265360975576683885900465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21687147967435578514533953 16265360975576683885900465)
          ·
            refine ⟨12199020731682512914425349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16265360975576683885900465 12199020731682512914425349)
            ·
              refine ⟨2287316387190471171454753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12199020731682512914425349 2287316387190471171454753)
              ·
                refine ⟨1715487290392853378591065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2287316387190471171454753 1715487290392853378591065)
                ·
                  refine ⟨1286615467794640033943299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1715487290392853378591065 1286615467794640033943299)
                  ·
                    refine ⟨1929923201691960050914949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1286615467794640033943299 1929923201691960050914949)
                    ·
                      refine ⟨361860600317242509546553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1929923201691960050914949 361860600317242509546553)
                      ·
                        rfl

theorem cell23_704721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_704721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704721 prefixEnd_704721 := by exact prefixLift 704721
  have htrace : WordTrace (prefixWord ++ tailWord_704721) baseStart_704721 baseEnd_704721 := by
    simpa [prefixWord, tailWord_704721, baseEnd_704721] using wordTrace_append hprefix tailTrace_704721
  have hstable : (prefixWord ++ tailWord_704721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704721).length < 2 ^ (prefixWord ++ tailWord_704721).sum := by decide
  have hdescent : baseEnd_704721 < baseStart_704721 := by decide
  rcases family_descends (prefixWord ++ tailWord_704721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704821 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 3, 6]
def baseStart_704821 : Nat := 118140960795 + 704821 * 2 ^ 59
def prefixEnd_704821 : Nat := 4983230072969 + 3 ^ 40 * 704821 * 2
def baseEnd_704821 : Nat := 120637316127564039432031

theorem tailTrace_704821 : CollatzResearch.WordTrace tailWord_704821 prefixEnd_704821 120637316127564039432031 := by
  unfold tailWord_704821
  simp only [CollatzResearch.WordTrace]
  refine ⟨25706933779561365688458317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17137955853040910458972211 25706933779561365688458317)
  ·
    refine ⟨9640100167335512133171869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25706933779561365688458317 9640100167335512133171869)
    ·
      refine ⟨3615037562750817049939451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9640100167335512133171869 3615037562750817049939451)
      ·
        refine ⟨5422556344126225574909177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3615037562750817049939451 5422556344126225574909177)
        ·
          refine ⟨4066917258094669181181883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5422556344126225574909177 4066917258094669181181883)
          ·
            refine ⟨6100375887142003771772825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4066917258094669181181883 6100375887142003771772825)
            ·
              refine ⟨4575281915356502828829619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6100375887142003771772825 4575281915356502828829619)
              ·
                refine ⟨6862922873034754243244429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4575281915356502828829619 6862922873034754243244429)
                ·
                  refine ⟨2573596077388032841216661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6862922873034754243244429 2573596077388032841216661)
                  ·
                    refine ⟨120637316127564039432031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2573596077388032841216661 120637316127564039432031)
                    ·
                      rfl

theorem cell23_704821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_704821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704821 prefixEnd_704821 := by exact prefixLift 704821
  have htrace : WordTrace (prefixWord ++ tailWord_704821) baseStart_704821 baseEnd_704821 := by
    simpa [prefixWord, tailWord_704821, baseEnd_704821] using wordTrace_append hprefix tailTrace_704821
  have hstable : (prefixWord ++ tailWord_704821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704821).length < 2 ^ (prefixWord ++ tailWord_704821).sum := by decide
  have hdescent : baseEnd_704821 < baseStart_704821 := by decide
  rcases family_descends (prefixWord ++ tailWord_704821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704828 : List Nat := [2, 2, 2, 2, 1, 2, 1, 5, 1, 1, 4]
def baseStart_704828 : Nat := 118140960795 + 704828 * 2 ^ 59
def prefixEnd_704828 : Nat := 4983230072969 + 3 ^ 40 * 704828 * 2
def baseEnd_704828 : Nat := 361915542747273590908561

theorem tailTrace_704828 : CollatzResearch.WordTrace tailWord_704828 prefixEnd_704828 361915542747273590908561 := by
  unfold tailWord_704828
  simp only [CollatzResearch.WordTrace]
  refine ⟨12853594545268002941981569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17138126060357337255975425 12853594545268002941981569)
  ·
    refine ⟨9640195908951002206486177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12853594545268002941981569 9640195908951002206486177)
    ·
      refine ⟨7230146931713251654864633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9640195908951002206486177 7230146931713251654864633)
      ·
        refine ⟨5422610198784938741148475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7230146931713251654864633 5422610198784938741148475)
        ·
          refine ⟨8133915298177408111722713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5422610198784938741148475 8133915298177408111722713)
          ·
            refine ⟨6100436473633056083792035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8133915298177408111722713 6100436473633056083792035)
            ·
              refine ⟨9150654710449584125688053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6100436473633056083792035 9150654710449584125688053)
              ·
                refine ⟨857873879104648511783255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9150654710449584125688053 857873879104648511783255)
                ·
                  refine ⟨1286810818656972767674883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 857873879104648511783255 1286810818656972767674883)
                  ·
                    refine ⟨1930216227985459151512325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1286810818656972767674883 1930216227985459151512325)
                    ·
                      refine ⟨361915542747273590908561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1930216227985459151512325 361915542747273590908561)
                      ·
                        rfl

theorem cell23_704828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_704828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704828 prefixEnd_704828 := by exact prefixLift 704828
  have htrace : WordTrace (prefixWord ++ tailWord_704828) baseStart_704828 baseEnd_704828 := by
    simpa [prefixWord, tailWord_704828, baseEnd_704828] using wordTrace_append hprefix tailTrace_704828
  have hstable : (prefixWord ++ tailWord_704828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704828).length < 2 ^ (prefixWord ++ tailWord_704828).sum := by decide
  have hdescent : baseEnd_704828 < baseStart_704828 := by decide
  rcases family_descends (prefixWord ++ tailWord_704828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704882 : List Nat := [3, 2, 1, 2, 1, 4, 3, 1, 1, 2, 3]
def baseStart_704882 : Nat := 118140960795 + 704882 * 2 ^ 59
def prefixEnd_704882 : Nat := 4983230072969 + 3 ^ 40 * 704882 * 2
def baseEnd_704882 : Nat := 361943270702616379633313

theorem tailTrace_704882 : CollatzResearch.WordTrace tailWord_704882 prefixEnd_704882 361943270702616379633313 := by
  unfold tailWord_704882
  simp only [CollatzResearch.WordTrace]
  refine ⟨6427289658085093276607225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17139439088226915404285933 6427289658085093276607225)
  ·
    refine ⟨4820467243563819957455419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6427289658085093276607225 4820467243563819957455419)
    ·
      refine ⟨7230700865345729936183129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4820467243563819957455419 7230700865345729936183129)
      ·
        refine ⟨5423025649009297452137347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7230700865345729936183129 5423025649009297452137347)
        ·
          refine ⟨8134538473513946178206021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5423025649009297452137347 8134538473513946178206021)
          ·
            refine ⟨1525225963783864908413629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8134538473513946178206021 1525225963783864908413629)
            ·
              refine ⟨571959736418949340655111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1525225963783864908413629 571959736418949340655111)
              ·
                refine ⟨857939604628424010982667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 571959736418949340655111 857939604628424010982667)
                ·
                  refine ⟨1286909406942636016474001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 857939604628424010982667 1286909406942636016474001)
                  ·
                    refine ⟨965182055206977012355501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1286909406942636016474001 965182055206977012355501)
                    ·
                      refine ⟨361943270702616379633313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 965182055206977012355501 361943270702616379633313)
                      ·
                        rfl

theorem cell23_704882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_704882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704882 prefixEnd_704882 := by exact prefixLift 704882
  have htrace : WordTrace (prefixWord ++ tailWord_704882) baseStart_704882 baseEnd_704882 := by
    simpa [prefixWord, tailWord_704882, baseEnd_704882] using wordTrace_append hprefix tailTrace_704882
  have hstable : (prefixWord ++ tailWord_704882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704882).length < 2 ^ (prefixWord ++ tailWord_704882).sum := by decide
  have hdescent : baseEnd_704882 < baseStart_704882 := by decide
  rcases family_descends (prefixWord ++ tailWord_704882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704905 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 3, 3, 2]
def baseStart_704905 : Nat := 118140960795 + 704905 * 2 ^ 59
def prefixEnd_704905 : Nat := 4983230072969 + 3 ^ 40 * 704905 * 2
def baseEnd_704905 : Nat := 361955080757669789645707

theorem tailTrace_704905 : CollatzResearch.WordTrace tailWord_704905 prefixEnd_704905 361955080757669789645707 := by
  unfold tailWord_704905
  simp only [CollatzResearch.WordTrace]
  refine ⟨25709997511257048034516169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17139998340838032023010779 25709997511257048034516169)
  ·
    refine ⟨19282498133442786025887127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25709997511257048034516169 19282498133442786025887127)
    ·
      refine ⟨28923747200164179038830691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19282498133442786025887127 28923747200164179038830691)
      ·
        refine ⟨43385620800246268558246037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28923747200164179038830691 43385620800246268558246037)
        ·
          refine ⟨2033700975011543838667783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 43385620800246268558246037 2033700975011543838667783)
          ·
            refine ⟨3050551462517315758001675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2033700975011543838667783 3050551462517315758001675)
            ·
              refine ⟨4575827193775973637002513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3050551462517315758001675 4575827193775973637002513)
              ·
                refine ⟨3431870395331980227751885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4575827193775973637002513 3431870395331980227751885)
                ·
                  refine ⟨1286951398249492585406957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3431870395331980227751885 1286951398249492585406957)
                  ·
                    refine ⟨482606774343559719527609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1286951398249492585406957 482606774343559719527609)
                    ·
                      refine ⟨361955080757669789645707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 482606774343559719527609 361955080757669789645707)
                      ·
                        rfl

theorem cell23_704905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 3, 2].length) (baseStart_704905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704905 prefixEnd_704905 := by exact prefixLift 704905
  have htrace : WordTrace (prefixWord ++ tailWord_704905) baseStart_704905 baseEnd_704905 := by
    simpa [prefixWord, tailWord_704905, baseEnd_704905] using wordTrace_append hprefix tailTrace_704905
  have hstable : (prefixWord ++ tailWord_704905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704905).length < 2 ^ (prefixWord ++ tailWord_704905).sum := by decide
  have hdescent : baseEnd_704905 < baseStart_704905 := by decide
  rcases family_descends (prefixWord ++ tailWord_704905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704958 : List Nat := [4, 2, 1, 1, 1, 1, 3, 3, 7]
def baseStart_704958 : Nat := 118140960795 + 704958 * 2 ^ 59
def prefixEnd_704958 : Nat := 4983230072969 + 3 ^ 40 * 704958 * 2
def baseEnd_704958 : Nat := 40220255025817564698107

theorem tailTrace_704958 : CollatzResearch.WordTrace tailWord_704958 prefixEnd_704958 40220255025817564698107 := by
  unfold tailWord_704958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3213991322508129760774441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17141287053376692057463685 3213991322508129760774441)
  ·
    refine ⟨2410493491881097320580831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3213991322508129760774441 2410493491881097320580831)
    ·
      refine ⟨3615740237821645980871247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2410493491881097320580831 3615740237821645980871247)
      ·
        refine ⟨5423610356732468971306871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3615740237821645980871247 5423610356732468971306871)
        ·
          refine ⟨8135415535098703456960307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5423610356732468971306871 8135415535098703456960307)
          ·
            refine ⟨12203123302648055185440461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8135415535098703456960307 12203123302648055185440461)
            ·
              refine ⟨4576171238493020694540173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12203123302648055185440461 4576171238493020694540173)
              ·
                refine ⟨1716064214434882760452565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4576171238493020694540173 1716064214434882760452565)
                ·
                  refine ⟨40220255025817564698107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1716064214434882760452565 40220255025817564698107)
                  ·
                    rfl

theorem cell23_704958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_704958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_704958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_704958 prefixEnd_704958 := by exact prefixLift 704958
  have htrace : WordTrace (prefixWord ++ tailWord_704958) baseStart_704958 baseEnd_704958 := by
    simpa [prefixWord, tailWord_704958, baseEnd_704958] using wordTrace_append hprefix tailTrace_704958
  have hstable : (prefixWord ++ tailWord_704958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704958).length < 2 ^ (prefixWord ++ tailWord_704958).sum := by decide
  have hdescent : baseEnd_704958 < baseStart_704958 := by decide
  rcases family_descends (prefixWord ++ tailWord_704958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705005 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 4, 5]
def baseStart_705005 : Nat := 118140960795 + 705005 * 2 ^ 59
def prefixEnd_705005 : Nat := 4983230072969 + 3 ^ 40 * 705005 * 2
def baseEnd_705005 : Nat := 120668809607706466131749

theorem tailTrace_705005 : CollatzResearch.WordTrace tailWord_705005 prefixEnd_705005 120668809607706466131749 := by
  unfold tailWord_705005
  simp only [CollatzResearch.WordTrace]
  refine ⟨25713644810894765113156469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17142429873929843408770979 25713644810894765113156469)
  ·
    refine ⟨2410654201021384229358419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25713644810894765113156469 2410654201021384229358419)
    ·
      refine ⟨3615981301532076344037629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2410654201021384229358419 3615981301532076344037629)
      ·
        refine ⟨1355992988074528629014111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3615981301532076344037629 1355992988074528629014111)
        ·
          refine ⟨2033989482111792943521167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1355992988074528629014111 2033989482111792943521167)
          ·
            refine ⟨3050984223167689415281751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2033989482111792943521167 3050984223167689415281751)
            ·
              refine ⟨4576476334751534122922627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3050984223167689415281751 4576476334751534122922627)
              ·
                refine ⟨6864714502127301184383941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4576476334751534122922627 6864714502127301184383941)
                ·
                  refine ⟨1287133969148868972071989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6864714502127301184383941 1287133969148868972071989)
                  ·
                    refine ⟨120668809607706466131749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1287133969148868972071989 120668809607706466131749)
                    ·
                      rfl

theorem cell23_705005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_705005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705005 prefixEnd_705005 := by exact prefixLift 705005
  have htrace : WordTrace (prefixWord ++ tailWord_705005) baseStart_705005 baseEnd_705005 := by
    simpa [prefixWord, tailWord_705005, baseEnd_705005] using wordTrace_append hprefix tailTrace_705005
  have hstable : (prefixWord ++ tailWord_705005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705005).length < 2 ^ (prefixWord ++ tailWord_705005).sum := by decide
  have hdescent : baseEnd_705005 < baseStart_705005 := by decide
  rcases family_descends (prefixWord ++ tailWord_705005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705076 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 2, 4, 2]
def baseStart_705076 : Nat := 118140960795 + 705076 * 2 ^ 59
def prefixEnd_705076 : Nat := 4983230072969 + 3 ^ 40 * 705076 * 2
def baseEnd_705076 : Nat := 362042885949588620607421

theorem tailTrace_705076 : CollatzResearch.WordTrace tailWord_705076 prefixEnd_705076 362042885949588620607421 := by
  unfold tailWord_705076
  simp only [CollatzResearch.WordTrace]
  refine ⟨12858117196818772119495541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17144156262425029492660721 12858117196818772119495541)
  ·
    refine ⟨1205448487201759886202707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12858117196818772119495541 1205448487201759886202707)
    ·
      refine ⟨1808172730802639829304061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1205448487201759886202707 1808172730802639829304061)
      ·
        refine ⟨678064774050989935989023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1808172730802639829304061 678064774050989935989023)
        ·
          refine ⟨1017097161076484903983535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678064774050989935989023 1017097161076484903983535)
          ·
            refine ⟨1525645741614727355975303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017097161076484903983535 1525645741614727355975303)
            ·
              refine ⟨2288468612422091033962955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1525645741614727355975303 2288468612422091033962955)
              ·
                refine ⟨3432702918633136550944433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2288468612422091033962955 3432702918633136550944433)
                ·
                  refine ⟨2574527188974852413208325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3432702918633136550944433 2574527188974852413208325)
                  ·
                    refine ⟨482723847932784827476561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2574527188974852413208325 482723847932784827476561)
                    ·
                      refine ⟨362042885949588620607421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 482723847932784827476561 362042885949588620607421)
                      ·
                        rfl

theorem cell23_705076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_705076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705076 prefixEnd_705076 := by exact prefixLift 705076
  have htrace : WordTrace (prefixWord ++ tailWord_705076) baseStart_705076 baseEnd_705076 := by
    simpa [prefixWord, tailWord_705076, baseEnd_705076] using wordTrace_append hprefix tailTrace_705076
  have hstable : (prefixWord ++ tailWord_705076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705076).length < 2 ^ (prefixWord ++ tailWord_705076).sum := by decide
  have hdescent : baseEnd_705076 < baseStart_705076 := by decide
  rcases family_descends (prefixWord ++ tailWord_705076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705095 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 3, 5]
def baseStart_705095 : Nat := 118140960795 + 705095 * 2 ^ 59
def prefixEnd_705095 : Nat := 4983230072969 + 3 ^ 40 * 705095 * 2
def baseEnd_705095 : Nat := 120684214027341348756611

theorem tailTrace_705095 : CollatzResearch.WordTrace tailWord_705095 prefixEnd_705095 120684214027341348756611 := by
  unfold tailWord_705095
  simp only [CollatzResearch.WordTrace]
  refine ⟨25716927380568710483932739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17144618253712473655955159 25716927380568710483932739)
  ·
    refine ⟨38575391070853065725899109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25716927380568710483932739 38575391070853065725899109)
    ·
      refine ⟨7232885825784949823606083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38575391070853065725899109 7232885825784949823606083)
      ·
        refine ⟨10849328738677424735409125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7232885825784949823606083 10849328738677424735409125)
        ·
          refine ⟨2034249138502017137889211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10849328738677424735409125 2034249138502017137889211)
          ·
            refine ⟨3051373707753025706833817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2034249138502017137889211 3051373707753025706833817)
            ·
              refine ⟨2288530280814769280125363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3051373707753025706833817 2288530280814769280125363)
              ·
                refine ⟨3432795421222153920188045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2288530280814769280125363 3432795421222153920188045)
                ·
                  refine ⟨1287298282958307720070517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3432795421222153920188045 1287298282958307720070517)
                  ·
                    refine ⟨120684214027341348756611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1287298282958307720070517 120684214027341348756611)
                    ·
                      rfl

theorem cell23_705095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_705095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705095 prefixEnd_705095 := by exact prefixLift 705095
  have htrace : WordTrace (prefixWord ++ tailWord_705095) baseStart_705095 baseEnd_705095 := by
    simpa [prefixWord, tailWord_705095, baseEnd_705095] using wordTrace_append hprefix tailTrace_705095
  have hstable : (prefixWord ++ tailWord_705095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705095).length < 2 ^ (prefixWord ++ tailWord_705095).sum := by decide
  have hdescent : baseEnd_705095 < baseStart_705095 := by decide
  rcases family_descends (prefixWord ++ tailWord_705095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705109 : List Nat := [1, 3, 2, 2, 1, 1, 3, 5, 1, 1, 3]
def baseStart_705109 : Nat := 118140960795 + 705109 * 2 ^ 59
def prefixEnd_705109 : Nat := 4983230072969 + 3 ^ 40 * 705109 * 2
def baseEnd_705109 : Nat := 362059830811186991494769

theorem tailTrace_705109 : CollatzResearch.WordTrace tailWord_705109 prefixEnd_705109 362059830811186991494769 := by
  unfold tailWord_705109
  simp only [CollatzResearch.WordTrace]
  refine ⟨25717438002517990874942381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17144958668345327249961587 25717438002517990874942381)
  ·
    refine ⟨9644039250944246578103393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25717438002517990874942381 9644039250944246578103393)
    ·
      refine ⟨7233029438208184933577545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9644039250944246578103393 7233029438208184933577545)
      ·
        refine ⟨5424772078656138700183159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7233029438208184933577545 5424772078656138700183159)
        ·
          refine ⟨8137158117984208050274739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5424772078656138700183159 8137158117984208050274739)
          ·
            refine ⟨12205737176976312075412109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8137158117984208050274739 12205737176976312075412109)
            ·
              refine ⟨4577151441366117028279541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12205737176976312075412109 4577151441366117028279541)
              ·
                refine ⟨429107947628073471401207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4577151441366117028279541 429107947628073471401207)
                ·
                  refine ⟨643661921442110207101811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429107947628073471401207 643661921442110207101811)
                  ·
                    refine ⟨965492882163165310652717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 643661921442110207101811 965492882163165310652717)
                    ·
                      refine ⟨362059830811186991494769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 965492882163165310652717 362059830811186991494769)
                      ·
                        rfl

theorem cell23_705109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_705109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705109 prefixEnd_705109 := by exact prefixLift 705109
  have htrace : WordTrace (prefixWord ++ tailWord_705109) baseStart_705109 baseEnd_705109 := by
    simpa [prefixWord, tailWord_705109, baseEnd_705109] using wordTrace_append hprefix tailTrace_705109
  have hstable : (prefixWord ++ tailWord_705109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705109).length < 2 ^ (prefixWord ++ tailWord_705109).sum := by decide
  have hdescent : baseEnd_705109 < baseStart_705109 := by decide
  rcases family_descends (prefixWord ++ tailWord_705109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705112 : List Nat := [2, 1, 2, 2, 1, 2, 6, 1, 1, 5]
def baseStart_705112 : Nat := 118140960795 + 705112 * 2 ^ 59
def prefixEnd_705112 : Nat := 4983230072969 + 3 ^ 40 * 705112 * 2
def baseEnd_705112 : Nat := 120687123751050159919085

theorem tailTrace_705112 : CollatzResearch.WordTrace tailWord_705112 prefixEnd_705112 120687123751050159919085 := by
  unfold tailWord_705112
  simp only [CollatzResearch.WordTrace]
  refine ⟨12858773710753561193650795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17145031614338081591534393 12858773710753561193650795)
  ·
    refine ⟨19288160566130341790476193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12858773710753561193650795 19288160566130341790476193)
    ·
      refine ⟨14466120424597756342857145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19288160566130341790476193 14466120424597756342857145)
      ·
        refine ⟨10849590318448317257142859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14466120424597756342857145 10849590318448317257142859)
        ·
          refine ⟨16274385477672475885714289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10849590318448317257142859 16274385477672475885714289)
          ·
            refine ⟨12205789108254356914285717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16274385477672475885714289 12205789108254356914285717)
            ·
              refine ⟨572146364449422980357143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12205789108254356914285717 572146364449422980357143)
              ·
                refine ⟨858219546674134470535715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 572146364449422980357143 858219546674134470535715)
                ·
                  refine ⟨1287329320011201705803573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 858219546674134470535715 1287329320011201705803573)
                  ·
                    refine ⟨120687123751050159919085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1287329320011201705803573 120687123751050159919085)
                    ·
                      rfl

theorem cell23_705112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 1, 5].length) (baseStart_705112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705112 prefixEnd_705112 := by exact prefixLift 705112
  have htrace : WordTrace (prefixWord ++ tailWord_705112) baseStart_705112 baseEnd_705112 := by
    simpa [prefixWord, tailWord_705112, baseEnd_705112] using wordTrace_append hprefix tailTrace_705112
  have hstable : (prefixWord ++ tailWord_705112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705112).length < 2 ^ (prefixWord ++ tailWord_705112).sum := by decide
  have hdescent : baseEnd_705112 < baseStart_705112 := by decide
  rcases family_descends (prefixWord ++ tailWord_705112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705135 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 3]
def baseStart_705135 : Nat := 118140960795 + 705135 * 2 ^ 59
def prefixEnd_705135 : Nat := 4983230072969 + 3 ^ 40 * 705135 * 2
def baseEnd_705135 : Nat := 362073181308203889769649

theorem tailTrace_705135 : CollatzResearch.WordTrace tailWord_705135 prefixEnd_705135 362073181308203889769649 := by
  unfold tailWord_705135
  simp only [CollatzResearch.WordTrace]
  refine ⟨25718386300423797315388859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17145590866949198210259239 25718386300423797315388859)
  ·
    refine ⟨38577579450635695973083289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25718386300423797315388859 38577579450635695973083289)
    ·
      refine ⟨28933184587976771979812467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38577579450635695973083289 28933184587976771979812467)
      ·
        refine ⟨43399776881965157969718701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28933184587976771979812467 43399776881965157969718701)
        ·
          refine ⟨16274916330736934238644513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43399776881965157969718701 16274916330736934238644513)
          ·
            refine ⟨12206187248052700678983385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16274916330736934238644513 12206187248052700678983385)
            ·
              refine ⟨9154640436039525509237539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12206187248052700678983385 9154640436039525509237539)
              ·
                refine ⟨13731960654059288263856309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9154640436039525509237539 13731960654059288263856309)
                ·
                  refine ⟨1287371311318058274736529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13731960654059288263856309 1287371311318058274736529)
                  ·
                    refine ⟨965528483488543706052397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1287371311318058274736529 965528483488543706052397)
                    ·
                      refine ⟨362073181308203889769649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 965528483488543706052397 362073181308203889769649)
                      ·
                        rfl

theorem cell23_705135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 3].length) (baseStart_705135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705135 prefixEnd_705135 := by exact prefixLift 705135
  have htrace : WordTrace (prefixWord ++ tailWord_705135) baseStart_705135 baseEnd_705135 := by
    simpa [prefixWord, tailWord_705135, baseEnd_705135] using wordTrace_append hprefix tailTrace_705135
  have hstable : (prefixWord ++ tailWord_705135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705135).length < 2 ^ (prefixWord ++ tailWord_705135).sum := by decide
  have hdescent : baseEnd_705135 < baseStart_705135 := by decide
  rcases family_descends (prefixWord ++ tailWord_705135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705145 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 1, 1, 6]
def baseStart_705145 : Nat := 118140960795 + 705145 * 2 ^ 59
def prefixEnd_705145 : Nat := 4983230072969 + 3 ^ 40 * 705145 * 2
def baseEnd_705145 : Nat := 362078316114748850644603

theorem tailTrace_705145 : CollatzResearch.WordTrace tailWord_705145 prefixEnd_705145 362078316114748850644603 := by
  unfold tailWord_705145
  simp only [CollatzResearch.WordTrace]
  refine ⟨25718751030387569023252889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17145834020258379348835259 25718751030387569023252889)
  ·
    refine ⟨19289063272790676767439667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25718751030387569023252889 19289063272790676767439667)
    ·
      refine ⟨28933594909186015151159501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19289063272790676767439667 28933594909186015151159501)
      ·
        refine ⟨10850098090944755681684813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28933594909186015151159501 10850098090944755681684813)
        ·
          refine ⟨4068786784104283380631805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10850098090944755681684813 4068786784104283380631805)
          ·
            refine ⟨1525795044039106267736927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4068786784104283380631805 1525795044039106267736927)
            ·
              refine ⟨2288692566058659401605391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1525795044039106267736927 2288692566058659401605391)
              ·
                refine ⟨3433038849087989102408087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2288692566058659401605391 3433038849087989102408087)
                ·
                  refine ⟨5149558273631983653612131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3433038849087989102408087 5149558273631983653612131)
                  ·
                    refine ⟨7724337410447975480418197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5149558273631983653612131 7724337410447975480418197)
                    ·
                      refine ⟨362078316114748850644603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7724337410447975480418197 362078316114748850644603)
                      ·
                        rfl

theorem cell23_705145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_705145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705145 prefixEnd_705145 := by exact prefixLift 705145
  have htrace : WordTrace (prefixWord ++ tailWord_705145) baseStart_705145 baseEnd_705145 := by
    simpa [prefixWord, tailWord_705145, baseEnd_705145] using wordTrace_append hprefix tailTrace_705145
  have hstable : (prefixWord ++ tailWord_705145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705145).length < 2 ^ (prefixWord ++ tailWord_705145).sum := by decide
  have hdescent : baseEnd_705145 < baseStart_705145 := by decide
  rcases family_descends (prefixWord ++ tailWord_705145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705149 : List Nat := [1, 4, 1, 1, 5, 1, 2, 2, 1, 1, 4]
def baseStart_705149 : Nat := 118140960795 + 705149 * 2 ^ 59
def prefixEnd_705149 : Nat := 4983230072969 + 3 ^ 40 * 705149 * 2
def baseEnd_705149 : Nat := 362080370037366834994585

theorem tailTrace_705149 : CollatzResearch.WordTrace tailWord_705149 prefixEnd_705149 362080370037366834994585 := by
  unfold tailWord_705149
  simp only [CollatzResearch.WordTrace]
  refine ⟨25718896922373077706398501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17145931281582051804265667 25718896922373077706398501)
  ·
    refine ⟨4822293172944952069949719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25718896922373077706398501 4822293172944952069949719)
    ·
      refine ⟨7233439759417428104924579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4822293172944952069949719 7233439759417428104924579)
      ·
        refine ⟨10850159639126142157386869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7233439759417428104924579 10850159639126142157386869)
        ·
          refine ⟨1017202466168075827255019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10850159639126142157386869 1017202466168075827255019)
          ·
            refine ⟨1525803699252113740882529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017202466168075827255019 1525803699252113740882529)
            ·
              refine ⟨1144352774439085305661897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1525803699252113740882529 1144352774439085305661897)
              ·
                refine ⟨858264580829313979246423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1144352774439085305661897 858264580829313979246423)
                ·
                  refine ⟨1287396871243970968869635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 858264580829313979246423 1287396871243970968869635)
                  ·
                    refine ⟨1931095306865956453304453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1287396871243970968869635 1931095306865956453304453)
                    ·
                      refine ⟨362080370037366834994585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1931095306865956453304453 362080370037366834994585)
                      ·
                        rfl

theorem cell23_705149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_705149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705149 prefixEnd_705149 := by exact prefixLift 705149
  have htrace : WordTrace (prefixWord ++ tailWord_705149) baseStart_705149 baseEnd_705149 := by
    simpa [prefixWord, tailWord_705149, baseEnd_705149] using wordTrace_append hprefix tailTrace_705149
  have hstable : (prefixWord ++ tailWord_705149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705149).length < 2 ^ (prefixWord ++ tailWord_705149).sum := by decide
  have hdescent : baseEnd_705149 < baseStart_705149 := by decide
  rcases family_descends (prefixWord ++ tailWord_705149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705152 : List Nat := [2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 3]
def baseStart_705152 : Nat := 118140960795 + 705152 * 2 ^ 59
def prefixEnd_705152 : Nat := 4983230072969 + 3 ^ 40 * 705152 * 2
def baseEnd_705152 : Nat := 362081910479330323257071

theorem tailTrace_705152 : CollatzResearch.WordTrace tailWord_705152 prefixEnd_705152 362081910479330323257071 := by
  unfold tailWord_705152
  simp only [CollatzResearch.WordTrace]
  refine ⟨12859503170681104609378855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17146004227574806145838473 12859503170681104609378855)
  ·
    refine ⟨19289254756021656914068283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12859503170681104609378855 19289254756021656914068283)
    ·
      refine ⟨28933882134032485371102425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19289254756021656914068283 28933882134032485371102425)
      ·
        refine ⟨21700411600524364028326819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28933882134032485371102425 21700411600524364028326819)
        ·
          refine ⟨32550617400786546042490229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21700411600524364028326819 32550617400786546042490229)
          ·
            refine ⟨3051620381323738691483459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32550617400786546042490229 3051620381323738691483459)
            ·
              refine ⟨4577430571985608037225189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3051620381323738691483459 4577430571985608037225189)
              ·
                refine ⟨858268232247301506979723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4577430571985608037225189 858268232247301506979723)
                ·
                  refine ⟨1287402348370952260469585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 858268232247301506979723 1287402348370952260469585)
                  ·
                    refine ⟨965551761278214195352189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1287402348370952260469585 965551761278214195352189)
                    ·
                      refine ⟨362081910479330323257071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 965551761278214195352189 362081910479330323257071)
                      ·
                        rfl

theorem cell23_705152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 3].length) (baseStart_705152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705152 prefixEnd_705152 := by exact prefixLift 705152
  have htrace : WordTrace (prefixWord ++ tailWord_705152) baseStart_705152 baseEnd_705152 := by
    simpa [prefixWord, tailWord_705152, baseEnd_705152] using wordTrace_append hprefix tailTrace_705152
  have hstable : (prefixWord ++ tailWord_705152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705152).length < 2 ^ (prefixWord ++ tailWord_705152).sum := by decide
  have hdescent : baseEnd_705152 < baseStart_705152 := by decide
  rcases family_descends (prefixWord ++ tailWord_705152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705155 : List Nat := [1, 1, 1, 3, 3, 1, 6, 7]
def baseStart_705155 : Nat := 118140960795 + 705155 * 2 ^ 59
def prefixEnd_705155 : Nat := 4983230072969 + 3 ^ 40 * 705155 * 2
def baseEnd_705155 : Nat := 13410498182270141167391

theorem tailTrace_705155 : CollatzResearch.WordTrace tailWord_705155 prefixEnd_705155 13410498182270141167391 := by
  unfold tailWord_705155
  simp only [CollatzResearch.WordTrace]
  refine ⟨25719115760351340731116919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17146077173567560487411279 25719115760351340731116919)
  ·
    refine ⟨38578673640527011096675379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25719115760351340731116919 38578673640527011096675379)
    ·
      refine ⟨57868010460790516645013069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38578673640527011096675379 57868010460790516645013069)
      ·
        refine ⟨21700503922796443741879901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57868010460790516645013069 21700503922796443741879901)
        ·
          refine ⟨8137688971048666403204963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21700503922796443741879901 8137688971048666403204963)
          ·
            refine ⟨12206533456572999604807445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8137688971048666403204963 12206533456572999604807445)
            ·
              refine ⟨572181255776859356475349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12206533456572999604807445 572181255776859356475349)
              ·
                refine ⟨13410498182270141167391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 572181255776859356475349 13410498182270141167391)
                ·
                  rfl

theorem cell23_705155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 7].length) (baseStart_705155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705155 prefixEnd_705155 := by exact prefixLift 705155
  have htrace : WordTrace (prefixWord ++ tailWord_705155) baseStart_705155 baseEnd_705155 := by
    simpa [prefixWord, tailWord_705155, baseEnd_705155] using wordTrace_append hprefix tailTrace_705155
  have hstable : (prefixWord ++ tailWord_705155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705155).length < 2 ^ (prefixWord ++ tailWord_705155).sum := by decide
  have hdescent : baseEnd_705155 < baseStart_705155 := by decide
  rcases family_descends (prefixWord ++ tailWord_705155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705168 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 3, 9]
def baseStart_705168 : Nat := 118140960795 + 705168 * 2 ^ 59
def prefixEnd_705168 : Nat := 4983230072969 + 3 ^ 40 * 705168 * 2
def baseEnd_705168 : Nat := 120696708723267420218999

theorem tailTrace_705168 : CollatzResearch.WordTrace tailWord_705168 prefixEnd_705168 120696708723267420218999 := by
  unfold tailWord_705168
  simp only [CollatzResearch.WordTrace]
  refine ⟨12859794954652121975670079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17146393272869495967560105 12859794954652121975670079)
  ·
    refine ⟨19289692431978182963505119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12859794954652121975670079 19289692431978182963505119)
    ·
      refine ⟨28934538647967274445257679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19289692431978182963505119 28934538647967274445257679)
      ·
        refine ⟨43401807971950911667886519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28934538647967274445257679 43401807971950911667886519)
        ·
          refine ⟨65102711957926367501829779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43401807971950911667886519 65102711957926367501829779)
          ·
            refine ⟨97654067936889551252744669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65102711957926367501829779 97654067936889551252744669)
            ·
              refine ⟨36620275476333581719779251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97654067936889551252744669 36620275476333581719779251)
              ·
                refine ⟨54930413214500372579668877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36620275476333581719779251 54930413214500372579668877)
                ·
                  refine ⟨20598904955437639717375829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54930413214500372579668877 20598904955437639717375829)
                  ·
                    refine ⟨120696708723267420218999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 20598904955437639717375829 120696708723267420218999)
                    ·
                      rfl

theorem cell23_705168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 9].length) (baseStart_705168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705168 prefixEnd_705168 := by exact prefixLift 705168
  have htrace : WordTrace (prefixWord ++ tailWord_705168) baseStart_705168 baseEnd_705168 := by
    simpa [prefixWord, tailWord_705168, baseEnd_705168] using wordTrace_append hprefix tailTrace_705168
  have hstable : (prefixWord ++ tailWord_705168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705168).length < 2 ^ (prefixWord ++ tailWord_705168).sum := by decide
  have hdescent : baseEnd_705168 < baseStart_705168 := by decide
  rcases family_descends (prefixWord ++ tailWord_705168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705172 : List Nat := [2, 4, 2, 2, 1, 3, 9]
def baseStart_705172 : Nat := 118140960795 + 705172 * 2 ^ 59
def prefixEnd_705172 : Nat := 4983230072969 + 3 ^ 40 * 705172 * 2
def baseEnd_705172 : Nat := 4470273828301484506259

theorem tailTrace_705172 : CollatzResearch.WordTrace tailWord_705172 prefixEnd_705172 4470273828301484506259 := by
  unfold tailWord_705172
  simp only [CollatzResearch.WordTrace]
  refine ⟨12859867900644876317242885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17146490534193168422990513 12859867900644876317242885)
  ·
    refine ⟨2411225231370914309483041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12859867900644876317242885 2411225231370914309483041)
    ·
      refine ⟨1808418923528185732112281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2411225231370914309483041 1808418923528185732112281)
      ·
        refine ⟨1356314192646139299084211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1808418923528185732112281 1356314192646139299084211)
        ·
          refine ⟨2034471288969208948626317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1356314192646139299084211 2034471288969208948626317)
          ·
            refine ⟨762926733363453355734869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2034471288969208948626317 762926733363453355734869)
            ·
              refine ⟨4470273828301484506259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 762926733363453355734869 4470273828301484506259)
              ·
                rfl

theorem cell23_705172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 9].length) (baseStart_705172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705172 prefixEnd_705172 := by exact prefixLift 705172
  have htrace : WordTrace (prefixWord ++ tailWord_705172) baseStart_705172 baseEnd_705172 := by
    simpa [prefixWord, tailWord_705172, baseEnd_705172] using wordTrace_append hprefix tailTrace_705172
  have hstable : (prefixWord ++ tailWord_705172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705172).length < 2 ^ (prefixWord ++ tailWord_705172).sum := by decide
  have hdescent : baseEnd_705172 < baseStart_705172 := by decide
  rcases family_descends (prefixWord ++ tailWord_705172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705199 : List Nat := [1, 1, 2, 1, 2, 6, 1, 3, 2, 1, 3]
def baseStart_705199 : Nat := 118140960795 + 705199 * 2 ^ 59
def prefixEnd_705199 : Nat := 4983230072969 + 3 ^ 40 * 705199 * 2
def baseEnd_705199 : Nat := 362106044070091639369355

theorem tailTrace_705199 : CollatzResearch.WordTrace tailWord_705199 prefixEnd_705199 362106044070091639369355 := by
  unfold tailWord_705199
  simp only [CollatzResearch.WordTrace]
  refine ⟨25720720572191936245718651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17147147048127957497145767 25720720572191936245718651)
  ·
    refine ⟨38581080858287904368577977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25720720572191936245718651 38581080858287904368577977)
    ·
      refine ⟨28935810643715928276433483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38581080858287904368577977 28935810643715928276433483)
      ·
        refine ⟨43403715965573892414650225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28935810643715928276433483 43403715965573892414650225)
        ·
          refine ⟨32552786974180419310987669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43403715965573892414650225 32552786974180419310987669)
          ·
            refine ⟨1525911889414707155202547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32552786974180419310987669 1525911889414707155202547)
            ·
              refine ⟨2288867834122060732803821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1525911889414707155202547 2288867834122060732803821)
              ·
                refine ⟨858325437795772774801433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2288867834122060732803821 858325437795772774801433)
                ·
                  refine ⟨643744078346829581101075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 858325437795772774801433 643744078346829581101075)
                  ·
                    refine ⟨965616117520244371651613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 643744078346829581101075 965616117520244371651613)
                    ·
                      refine ⟨362106044070091639369355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 965616117520244371651613 362106044070091639369355)
                      ·
                        rfl

theorem cell23_705199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 1, 3].length) (baseStart_705199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705199 prefixEnd_705199 := by exact prefixLift 705199
  have htrace : WordTrace (prefixWord ++ tailWord_705199) baseStart_705199 baseEnd_705199 := by
    simpa [prefixWord, tailWord_705199, baseEnd_705199] using wordTrace_append hprefix tailTrace_705199
  have hstable : (prefixWord ++ tailWord_705199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705199).length < 2 ^ (prefixWord ++ tailWord_705199).sum := by decide
  have hdescent : baseEnd_705199 < baseStart_705199 := by decide
  rcases family_descends (prefixWord ++ tailWord_705199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705225 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 6, 4, 3]
def baseStart_705225 : Nat := 118140960795 + 705225 * 2 ^ 59
def prefixEnd_705225 : Nat := 4983230072969 + 3 ^ 40 * 705225 * 2
def baseEnd_705225 : Nat := 362119394567108537644235

theorem tailTrace_705225 : CollatzResearch.WordTrace tailWord_705225 prefixEnd_705225 362119394567108537644235 := by
  unfold tailWord_705225
  simp only [CollatzResearch.WordTrace]
  refine ⟨25721668870097742686165129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17147779246731828457443419 25721668870097742686165129)
  ·
    refine ⟨19291251652573307014623847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25721668870097742686165129 19291251652573307014623847)
    ·
      refine ⟨28936877478859960521935771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19291251652573307014623847 28936877478859960521935771)
      ·
        refine ⟨43405316218289940782903657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28936877478859960521935771 43405316218289940782903657)
        ·
          refine ⟨32553987163717455587177743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43405316218289940782903657 32553987163717455587177743)
          ·
            refine ⟨48830980745576183380766615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32553987163717455587177743 48830980745576183380766615)
            ·
              refine ⟨73246471118364275071149923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48830980745576183380766615 73246471118364275071149923)
              ·
                refine ⟨109869706677546412606724885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73246471118364275071149923 109869706677546412606724885)
                ·
                  refine ⟨5150142500509988090940229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 109869706677546412606724885 5150142500509988090940229)
                  ·
                    refine ⟨965651718845622767051293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5150142500509988090940229 965651718845622767051293)
                    ·
                      refine ⟨362119394567108537644235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 965651718845622767051293 362119394567108537644235)
                      ·
                        rfl

theorem cell23_705225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 4, 3].length) (baseStart_705225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705225 prefixEnd_705225 := by exact prefixLift 705225
  have htrace : WordTrace (prefixWord ++ tailWord_705225) baseStart_705225 baseEnd_705225 := by
    simpa [prefixWord, tailWord_705225, baseEnd_705225] using wordTrace_append hprefix tailTrace_705225
  have hstable : (prefixWord ++ tailWord_705225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705225).length < 2 ^ (prefixWord ++ tailWord_705225).sum := by decide
  have hdescent : baseEnd_705225 < baseStart_705225 := by decide
  rcases family_descends (prefixWord ++ tailWord_705225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705252 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 2, 2, 4]
def baseStart_705252 : Nat := 118140960795 + 705252 * 2 ^ 59
def prefixEnd_705252 : Nat := 4983230072969 + 3 ^ 40 * 705252 * 2
def baseEnd_705252 : Nat := 362133258544779932006611

theorem tailTrace_705252 : CollatzResearch.WordTrace tailWord_705252 prefixEnd_705252 362133258544779932006611 := by
  unfold tailWord_705252
  simp only [CollatzResearch.WordTrace]
  refine ⟨12861326820499963148699005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17148435760666617531598673 12861326820499963148699005)
  ·
    refine ⟨4822997557687486180762127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12861326820499963148699005 4822997557687486180762127)
    ·
      refine ⟨7234496336531229271143191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4822997557687486180762127 7234496336531229271143191)
      ·
        refine ⟨10851744504796843906714787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7234496336531229271143191 10851744504796843906714787)
        ·
          refine ⟨16277616757195265860072181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10851744504796843906714787 16277616757195265860072181)
          ·
            refine ⟨1526026570987056174381767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16277616757195265860072181 1526026570987056174381767)
            ·
              refine ⟨2289039856480584261572651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1526026570987056174381767 2289039856480584261572651)
              ·
                refine ⟨3433559784720876392358977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2289039856480584261572651 3433559784720876392358977)
                ·
                  refine ⟨2575169838540657294269233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3433559784720876392358977 2575169838540657294269233)
                  ·
                    refine ⟨1931377378905492970701925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2575169838540657294269233 1931377378905492970701925)
                    ·
                      refine ⟨362133258544779932006611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1931377378905492970701925 362133258544779932006611)
                      ·
                        rfl

theorem cell23_705252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_705252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705252 prefixEnd_705252 := by exact prefixLift 705252
  have htrace : WordTrace (prefixWord ++ tailWord_705252) baseStart_705252 baseEnd_705252 := by
    simpa [prefixWord, tailWord_705252, baseEnd_705252] using wordTrace_append hprefix tailTrace_705252
  have hstable : (prefixWord ++ tailWord_705252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705252).length < 2 ^ (prefixWord ++ tailWord_705252).sum := by decide
  have hdescent : baseEnd_705252 < baseStart_705252 := by decide
  rcases family_descends (prefixWord ++ tailWord_705252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705256 : List Nat := [2, 1, 4, 1, 4, 1, 2, 1, 1, 4, 2]
def baseStart_705256 : Nat := 118140960795 + 705256 * 2 ^ 59
def prefixEnd_705256 : Nat := 4983230072969 + 3 ^ 40 * 705256 * 2
def baseEnd_705256 : Nat := 362135312467397916356593

theorem tailTrace_705256 : CollatzResearch.WordTrace tailWord_705256 prefixEnd_705256 362135312467397916356593 := by
  unfold tailWord_705256
  simp only [CollatzResearch.WordTrace]
  refine ⟨12861399766492717490271811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17148533021990289987029081 12861399766492717490271811)
  ·
    refine ⟨19292099649739076235407717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12861399766492717490271811 19292099649739076235407717)
    ·
      refine ⟨3617268684326076794138947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19292099649739076235407717 3617268684326076794138947)
      ·
        refine ⟨5425903026489115191208421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3617268684326076794138947 5425903026489115191208421)
        ·
          refine ⟨1017356817466709098351579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5425903026489115191208421 1017356817466709098351579)
          ·
            refine ⟨1526035226200063647527369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017356817466709098351579 1526035226200063647527369)
            ·
              refine ⟨1144526419650047735645527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1526035226200063647527369 1144526419650047735645527)
              ·
                refine ⟨1716789629475071603468291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1144526419650047735645527 1716789629475071603468291)
                ·
                  refine ⟨2575184444212607405202437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1716789629475071603468291 2575184444212607405202437)
                  ·
                    refine ⟨482847083289863888475457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2575184444212607405202437 482847083289863888475457)
                    ·
                      refine ⟨362135312467397916356593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 482847083289863888475457 362135312467397916356593)
                      ·
                        rfl

theorem cell23_705256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_705256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705256 prefixEnd_705256 := by exact prefixLift 705256
  have htrace : WordTrace (prefixWord ++ tailWord_705256) baseStart_705256 baseEnd_705256 := by
    simpa [prefixWord, tailWord_705256, baseEnd_705256] using wordTrace_append hprefix tailTrace_705256
  have hstable : (prefixWord ++ tailWord_705256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705256).length < 2 ^ (prefixWord ++ tailWord_705256).sum := by decide
  have hdescent : baseEnd_705256 < baseStart_705256 := by decide
  rcases family_descends (prefixWord ++ tailWord_705256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705262 : List Nat := [4, 1, 2, 1, 1, 4, 1, 2, 7]
def baseStart_705262 : Nat := 118140960795 + 705262 * 2 ^ 59
def prefixEnd_705262 : Nat := 4983230072969 + 3 ^ 40 * 705262 * 2
def baseEnd_705262 : Nat := 40237599261258321431285

theorem tailTrace_705262 : CollatzResearch.WordTrace tailWord_705262 prefixEnd_705262 40237599261258321431285 := by
  unfold tailWord_705262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3215377296370462250657755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17148678913975798670174693 3215377296370462250657755)
  ·
    refine ⟨4823065944555693375986633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3215377296370462250657755 4823065944555693375986633)
    ·
      refine ⟨3617299458416770031989975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4823065944555693375986633 3617299458416770031989975)
      ·
        refine ⟨5425949187625155047984963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3617299458416770031989975 5425949187625155047984963)
        ·
          refine ⟨8138923781437732571977445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5425949187625155047984963 8138923781437732571977445)
          ·
            refine ⟨1526048209019574857245771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8138923781437732571977445 1526048209019574857245771)
            ·
              refine ⟨2289072313529362285868657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1526048209019574857245771 2289072313529362285868657)
              ·
                refine ⟨1716804235147021714401493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2289072313529362285868657 1716804235147021714401493)
                ·
                  refine ⟨40237599261258321431285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1716804235147021714401493 40237599261258321431285)
                  ·
                    rfl

theorem cell23_705262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_705262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705262 prefixEnd_705262 := by exact prefixLift 705262
  have htrace : WordTrace (prefixWord ++ tailWord_705262) baseStart_705262 baseEnd_705262 := by
    simpa [prefixWord, tailWord_705262, baseEnd_705262] using wordTrace_append hprefix tailTrace_705262
  have hstable : (prefixWord ++ tailWord_705262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705262).length < 2 ^ (prefixWord ++ tailWord_705262).sum := by decide
  have hdescent : baseEnd_705262 < baseStart_705262 := by decide
  rcases family_descends (prefixWord ++ tailWord_705262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705285 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 3, 2, 5]
def baseStart_705285 : Nat := 118140960795 + 705285 * 2 ^ 59
def prefixEnd_705285 : Nat := 4983230072969 + 3 ^ 40 * 705285 * 2
def baseEnd_705285 : Nat := 362150203406378302893959

theorem tailTrace_705285 : CollatzResearch.WordTrace tailWord_705285 prefixEnd_705285 362150203406378302893959 := by
  unfold tailWord_705285
  simp only [CollatzResearch.WordTrace]
  refine ⟨25723857249880372933349309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17149238166586915288899539 25723857249880372933349309)
  ·
    refine ⟨9646446468705139850005991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25723857249880372933349309 9646446468705139850005991)
    ·
      refine ⟨14469669703057709775008987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9646446468705139850005991 14469669703057709775008987)
      ·
        refine ⟨21704504554586564662513481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14469669703057709775008987 21704504554586564662513481)
        ·
          refine ⟨16278378415939923496885111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21704504554586564662513481 16278378415939923496885111)
          ·
            refine ⟨24417567623909885245327667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16278378415939923496885111 24417567623909885245327667)
            ·
              refine ⟨36626351435864827867991501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24417567623909885245327667 36626351435864827867991501)
              ·
                refine ⟨13734881788449310450496813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36626351435864827867991501 13734881788449310450496813)
                ·
                  refine ⟨5150580670668491418936305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13734881788449310450496813 5150580670668491418936305)
                  ·
                    refine ⟨3862935503001368564202229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5150580670668491418936305 3862935503001368564202229)
                    ·
                      refine ⟨362150203406378302893959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3862935503001368564202229 362150203406378302893959)
                      ·
                        rfl

theorem cell23_705285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_705285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705285 prefixEnd_705285 := by exact prefixLift 705285
  have htrace : WordTrace (prefixWord ++ tailWord_705285) baseStart_705285 baseEnd_705285 := by
    simpa [prefixWord, tailWord_705285, baseEnd_705285] using wordTrace_append hprefix tailTrace_705285
  have hstable : (prefixWord ++ tailWord_705285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705285).length < 2 ^ (prefixWord ++ tailWord_705285).sum := by decide
  have hdescent : baseEnd_705285 < baseStart_705285 := by decide
  rcases family_descends (prefixWord ++ tailWord_705285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705312 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 4]
def baseStart_705312 : Nat := 118140960795 + 705312 * 2 ^ 59
def prefixEnd_705312 : Nat := 4983230072969 + 3 ^ 40 * 705312 * 2
def baseEnd_705312 : Nat := 362164067384049697256335

theorem tailTrace_705312 : CollatzResearch.WordTrace tailWord_705312 prefixEnd_705312 362164067384049697256335 := by
  unfold tailWord_705312
  simp only [CollatzResearch.WordTrace]
  refine ⟨12862421010391278272291095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17149894680521704363054793 12862421010391278272291095)
  ·
    refine ⟨19293631515586917408436643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12862421010391278272291095 19293631515586917408436643)
    ·
      refine ⟨28940447273380376112654965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19293631515586917408436643 28940447273380376112654965)
      ·
        refine ⟨2713166931879410260561403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28940447273380376112654965 2713166931879410260561403)
        ·
          refine ⟨4069750397819115390842105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2713166931879410260561403 4069750397819115390842105)
          ·
            refine ⟨3052312798364336543131579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4069750397819115390842105 3052312798364336543131579)
            ·
              refine ⟨4578469197546504814697369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3052312798364336543131579 4578469197546504814697369)
              ·
                refine ⟨3433851898159878611023027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4578469197546504814697369 3433851898159878611023027)
                ·
                  refine ⟨5150777847239817916534541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3433851898159878611023027 5150777847239817916534541)
                  ·
                    refine ⟨1931541692714931718700453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5150777847239817916534541 1931541692714931718700453)
                    ·
                      refine ⟨362164067384049697256335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1931541692714931718700453 362164067384049697256335)
                      ·
                        rfl

theorem cell23_705312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_705312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705312 prefixEnd_705312 := by exact prefixLift 705312
  have htrace : WordTrace (prefixWord ++ tailWord_705312) baseStart_705312 baseEnd_705312 := by
    simpa [prefixWord, tailWord_705312, baseEnd_705312] using wordTrace_append hprefix tailTrace_705312
  have hstable : (prefixWord ++ tailWord_705312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705312).length < 2 ^ (prefixWord ++ tailWord_705312).sum := by decide
  have hdescent : baseEnd_705312 < baseStart_705312 := by decide
  rcases family_descends (prefixWord ++ tailWord_705312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705335 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 10]
def baseStart_705335 : Nat := 118140960795 + 705335 * 2 ^ 59
def prefixEnd_705335 : Nat := 4983230072969 + 3 ^ 40 * 705335 * 2
def baseEnd_705335 : Nat := 40241764159900345252081

theorem tailTrace_705335 : CollatzResearch.WordTrace tailWord_705335 prefixEnd_705335 40241764159900345252081 := by
  unfold tailWord_705335
  simp only [CollatzResearch.WordTrace]
  refine ⟨25725680899699231472669459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17150453933132820981779639 25725680899699231472669459)
  ·
    refine ⟨38588521349548847209004189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25725680899699231472669459 38588521349548847209004189)
    ·
      refine ⟨14470695506080817703376571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38588521349548847209004189 14470695506080817703376571)
      ·
        refine ⟨21706043259121226555064857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14470695506080817703376571 21706043259121226555064857)
        ·
          refine ⟨16279532444340919916298643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21706043259121226555064857 16279532444340919916298643)
          ·
            refine ⟨24419298666511379874447965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16279532444340919916298643 24419298666511379874447965)
            ·
              refine ⟨9157236999941767452917987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24419298666511379874447965 9157236999941767452917987)
              ·
                refine ⟨13735855499912651179376981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9157236999941767452917987 13735855499912651179376981)
                ·
                  refine ⟨40241764159900345252081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 13735855499912651179376981 40241764159900345252081)
                  ·
                    rfl

theorem cell23_705335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 10].length) (baseStart_705335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705335 prefixEnd_705335 := by exact prefixLift 705335
  have htrace : WordTrace (prefixWord ++ tailWord_705335) baseStart_705335 baseEnd_705335 := by
    simpa [prefixWord, tailWord_705335, baseEnd_705335] using wordTrace_append hprefix tailTrace_705335
  have hstable : (prefixWord ++ tailWord_705335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705335).length < 2 ^ (prefixWord ++ tailWord_705335).sum := by decide
  have hdescent : baseEnd_705335 < baseStart_705335 := by decide
  rcases family_descends (prefixWord ++ tailWord_705335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705352 : List Nat := [2, 1, 3, 1, 1, 3, 2, 4, 6]
def baseStart_705352 : Nat := 118140960795 + 705352 * 2 ^ 59
def prefixEnd_705352 : Nat := 4983230072969 + 3 ^ 40 * 705352 * 2
def baseEnd_705352 : Nat := 40242734067803282306239

theorem tailTrace_705352 : CollatzResearch.WordTrace tailWord_705352 prefixEnd_705352 40242734067803282306239 := by
  unfold tailWord_705352
  simp only [CollatzResearch.WordTrace]
  refine ⟨12863150470318821688019155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17150867293758428917358873 12863150470318821688019155)
  ·
    refine ⟨19294725705478232532028733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12863150470318821688019155 19294725705478232532028733)
    ·
      refine ⟨7235522139554337199510775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19294725705478232532028733 7235522139554337199510775)
      ·
        refine ⟨10853283209331505799266163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7235522139554337199510775 10853283209331505799266163)
        ·
          refine ⟨16279924813997258698899245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10853283209331505799266163 16279924813997258698899245)
          ·
            refine ⟨6104971805248972012087217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16279924813997258698899245 6104971805248972012087217)
            ·
              refine ⟨4578728853936729009065413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6104971805248972012087217 4578728853936729009065413)
              ·
                refine ⟨858511660113136689199765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4578728853936729009065413 858511660113136689199765)
                ·
                  refine ⟨40242734067803282306239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 858511660113136689199765 40242734067803282306239)
                  ·
                    rfl

theorem cell23_705352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 6].length) (baseStart_705352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705352 prefixEnd_705352 := by exact prefixLift 705352
  have htrace : WordTrace (prefixWord ++ tailWord_705352) baseStart_705352 baseEnd_705352 := by
    simpa [prefixWord, tailWord_705352, baseEnd_705352] using wordTrace_append hprefix tailTrace_705352
  have hstable : (prefixWord ++ tailWord_705352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705352).length < 2 ^ (prefixWord ++ tailWord_705352).sum := by decide
  have hdescent : baseEnd_705352 < baseStart_705352 := by decide
  rcases family_descends (prefixWord ++ tailWord_705352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705356 : List Nat := [2, 2, 1, 3, 3, 3, 1, 1, 3, 4]
def baseStart_705356 : Nat := 118140960795 + 705356 * 2 ^ 59
def prefixEnd_705356 : Nat := 4983230072969 + 3 ^ 40 * 705356 * 2
def baseEnd_705356 : Nat := 120728886844282508368711

theorem tailTrace_705356 : CollatzResearch.WordTrace tailWord_705356 prefixEnd_705356 120728886844282508368711 := by
  unfold tailWord_705356
  simp only [CollatzResearch.WordTrace]
  refine ⟨12863223416311576029591961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17150964555082101372789281 12863223416311576029591961)
  ·
    refine ⟨9647417562233682022193971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12863223416311576029591961 9647417562233682022193971)
    ·
      refine ⟨14471126343350523033290957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9647417562233682022193971 14471126343350523033290957)
      ·
        refine ⟨5426672378756446137484109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14471126343350523033290957 5426672378756446137484109)
        ·
          refine ⟨2035002142033667301556541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5426672378756446137484109 2035002142033667301556541)
          ·
            refine ⟨763125803262625238083703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2035002142033667301556541 763125803262625238083703)
            ·
              refine ⟨1144688704893937857125555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 763125803262625238083703 1144688704893937857125555)
              ·
                refine ⟨1717033057340906785688333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1144688704893937857125555 1717033057340906785688333)
                ·
                  refine ⟨643887396502840044633125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1717033057340906785688333 643887396502840044633125)
                  ·
                    refine ⟨120728886844282508368711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 643887396502840044633125 120728886844282508368711)
                    ·
                      rfl

theorem cell23_705356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 3, 4].length) (baseStart_705356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705356 prefixEnd_705356 := by exact prefixLift 705356
  have htrace : WordTrace (prefixWord ++ tailWord_705356) baseStart_705356 baseEnd_705356 := by
    simpa [prefixWord, tailWord_705356, baseEnd_705356] using wordTrace_append hprefix tailTrace_705356
  have hstable : (prefixWord ++ tailWord_705356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705356).length < 2 ^ (prefixWord ++ tailWord_705356).sum := by decide
  have hdescent : baseEnd_705356 < baseStart_705356 := by decide
  rcases family_descends (prefixWord ++ tailWord_705356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705369 : List Nat := [1, 2, 1, 2, 2, 4, 4, 1, 6]
def baseStart_705369 : Nat := 118140960795 + 705369 * 2 ^ 59
def prefixEnd_705369 : Nat := 4983230072969 + 3 ^ 40 * 705369 * 2
def baseEnd_705369 : Nat := 40243703975706219360397

theorem tailTrace_705369 : CollatzResearch.WordTrace tailWord_705369 prefixEnd_705369 40243703975706219360397 := by
  unfold tailWord_705369
  simp only [CollatzResearch.WordTrace]
  refine ⟨25726920981576055279407161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17151280654384036852938107 25726920981576055279407161)
  ·
    refine ⟨19295190736182041459555371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25726920981576055279407161 19295190736182041459555371)
    ·
      refine ⟨28942786104273062189333057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19295190736182041459555371 28942786104273062189333057)
      ·
        refine ⟨21707089578204796641999793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28942786104273062189333057 21707089578204796641999793)
        ·
          refine ⟨16280317183653597481499845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21707089578204796641999793 16280317183653597481499845)
          ·
            refine ⟨3052559471935049527781221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16280317183653597481499845 3052559471935049527781221)
            ·
              refine ⟨572354900987821786458979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3052559471935049527781221 572354900987821786458979)
              ·
                refine ⟨858532351481732679688469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 572354900987821786458979 858532351481732679688469)
                ·
                  refine ⟨40243703975706219360397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 858532351481732679688469 40243703975706219360397)
                  ·
                    rfl

theorem cell23_705369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 6].length) (baseStart_705369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705369 prefixEnd_705369 := by exact prefixLift 705369
  have htrace : WordTrace (prefixWord ++ tailWord_705369) baseStart_705369 baseEnd_705369 := by
    simpa [prefixWord, tailWord_705369, baseEnd_705369] using wordTrace_append hprefix tailTrace_705369
  have hstable : (prefixWord ++ tailWord_705369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705369).length < 2 ^ (prefixWord ++ tailWord_705369).sum := by decide
  have hdescent : baseEnd_705369 < baseStart_705369 := by decide
  rcases family_descends (prefixWord ++ tailWord_705369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705412 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 5, 6]
def baseStart_705412 : Nat := 118140960795 + 705412 * 2 ^ 59
def prefixEnd_705412 : Nat := 4983230072969 + 3 ^ 40 * 705412 * 2
def baseEnd_705412 : Nat := 120738471816499768668625

theorem tailTrace_705412 : CollatzResearch.WordTrace tailWord_705412 prefixEnd_705412 120738471816499768668625 := by
  unfold tailWord_705412
  simp only [CollatzResearch.WordTrace]
  refine ⟨12864244660210136811611245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17152326213613515748814993 12864244660210136811611245)
  ·
    refine ⟨4824091747578801304354217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12864244660210136811611245 4824091747578801304354217)
    ·
      refine ⟨3618068810684100978265663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4824091747578801304354217 3618068810684100978265663)
      ·
        refine ⟨5427103216026151467398495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3618068810684100978265663 5427103216026151467398495)
        ·
          refine ⟨8140654824039227201097743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5427103216026151467398495 8140654824039227201097743)
          ·
            refine ⟨12210982236058840801646615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8140654824039227201097743 12210982236058840801646615)
            ·
              refine ⟨18316473354088261202469923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12210982236058840801646615 18316473354088261202469923)
              ·
                refine ⟨27474710031132391803704885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18316473354088261202469923 27474710031132391803704885)
                ·
                  refine ⟨2575754065418661731597333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27474710031132391803704885 2575754065418661731597333)
                  ·
                    refine ⟨120738471816499768668625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2575754065418661731597333 120738471816499768668625)
                    ·
                      rfl

theorem cell23_705412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_705412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705412 prefixEnd_705412 := by exact prefixLift 705412
  have htrace : WordTrace (prefixWord ++ tailWord_705412) baseStart_705412 baseEnd_705412 := by
    simpa [prefixWord, tailWord_705412, baseEnd_705412] using wordTrace_append hprefix tailTrace_705412
  have hstable : (prefixWord ++ tailWord_705412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705412).length < 2 ^ (prefixWord ++ tailWord_705412).sum := by decide
  have hdescent : baseEnd_705412 < baseStart_705412 := by decide
  rcases family_descends (prefixWord ++ tailWord_705412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705413 : List Nat := [1, 3, 1, 1, 3, 4, 1, 4, 1, 1, 3]
def baseStart_705413 : Nat := 118140960795 + 705413 * 2 ^ 59
def prefixEnd_705413 : Nat := 4983230072969 + 3 ^ 40 * 705413 * 2
def baseEnd_705413 : Nat := 362215928930153802093371

theorem tailTrace_705413 : CollatzResearch.WordTrace tailWord_705413 prefixEnd_705413 362215928930153802093371 := by
  unfold tailWord_705413
  simp only [CollatzResearch.WordTrace]
  refine ⟨25728525793416650794008893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17152350528944433862672595 25728525793416650794008893)
  ·
    refine ⟨9648197172531244047753335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25728525793416650794008893 9648197172531244047753335)
    ·
      refine ⟨14472295758796866071630003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9648197172531244047753335 14472295758796866071630003)
      ·
        refine ⟨21708443638195299107445005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14472295758796866071630003 21708443638195299107445005)
        ·
          refine ⟨8140666364323237165291877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21708443638195299107445005 8140666364323237165291877)
          ·
            refine ⟨1526374943310606968492227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8140666364323237165291877 1526374943310606968492227)
            ·
              refine ⟨2289562414965910452738341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1526374943310606968492227 2289562414965910452738341)
              ·
                refine ⟨429292952806108209888439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2289562414965910452738341 429292952806108209888439)
                ·
                  refine ⟨643939429209162314832659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429292952806108209888439 643939429209162314832659)
                  ·
                    refine ⟨965909143813743472248989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 643939429209162314832659 965909143813743472248989)
                    ·
                      refine ⟨362215928930153802093371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 965909143813743472248989 362215928930153802093371)
                      ·
                        rfl

theorem cell23_705413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 1, 1, 3].length) (baseStart_705413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705413 prefixEnd_705413 := by exact prefixLift 705413
  have htrace : WordTrace (prefixWord ++ tailWord_705413) baseStart_705413 baseEnd_705413 := by
    simpa [prefixWord, tailWord_705413, baseEnd_705413] using wordTrace_append hprefix tailTrace_705413
  have hstable : (prefixWord ++ tailWord_705413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705413).length < 2 ^ (prefixWord ++ tailWord_705413).sum := by decide
  have hdescent : baseEnd_705413 < baseStart_705413 := by decide
  rcases family_descends (prefixWord ++ tailWord_705413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705429 : List Nat := [1, 3, 2, 1, 1, 5, 2, 1, 1, 6]
def baseStart_705429 : Nat := 118140960795 + 705429 * 2 ^ 59
def prefixEnd_705429 : Nat := 4983230072969 + 3 ^ 40 * 705429 * 2
def baseEnd_705429 : Nat := 120741381540208579831099

theorem tailTrace_705429 : CollatzResearch.WordTrace tailWord_705429 prefixEnd_705429 120741381540208579831099 := by
  unfold tailWord_705429
  simp only [CollatzResearch.WordTrace]
  refine ⟨25729109361358685526591341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17152739574239123684394227 25729109361358685526591341)
  ·
    refine ⟨9648416010509507072471753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25729109361358685526591341 9648416010509507072471753)
    ·
      refine ⟨7236312007882130304353815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9648416010509507072471753 7236312007882130304353815)
      ·
        refine ⟨10854468011823195456530723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7236312007882130304353815 10854468011823195456530723)
        ·
          refine ⟨16281702017734793184796085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10854468011823195456530723 16281702017734793184796085)
          ·
            refine ⟨1526409564162636861074633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16281702017734793184796085 1526409564162636861074633)
            ·
              refine ⟨1144807173121977645805975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1526409564162636861074633 1144807173121977645805975)
              ·
                refine ⟨1717210759682966468708963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1144807173121977645805975 1717210759682966468708963)
                ·
                  refine ⟨2575816139524449703063445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1717210759682966468708963 2575816139524449703063445)
                  ·
                    refine ⟨120741381540208579831099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2575816139524449703063445 120741381540208579831099)
                    ·
                      rfl

theorem cell23_705429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_705429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705429 prefixEnd_705429 := by exact prefixLift 705429
  have htrace : WordTrace (prefixWord ++ tailWord_705429) baseStart_705429 baseEnd_705429 := by
    simpa [prefixWord, tailWord_705429, baseEnd_705429] using wordTrace_append hprefix tailTrace_705429
  have hstable : (prefixWord ++ tailWord_705429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705429).length < 2 ^ (prefixWord ++ tailWord_705429).sum := by decide
  have hdescent : baseEnd_705429 < baseStart_705429 := by decide
  rcases family_descends (prefixWord ++ tailWord_705429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705430 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_705430 : Nat := 118140960795 + 705430 * 2 ^ 59
def prefixEnd_705430 : Nat := 4983230072969 + 3 ^ 40 * 705430 * 2
def baseEnd_705430 : Nat := 362224658101280235580793

theorem tailTrace_705430 : CollatzResearch.WordTrace tailWord_705430 prefixEnd_705430 362224658101280235580793 := by
  unfold tailWord_705430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1608071614647191418586109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17152763889570041798251829 1608071614647191418586109)
  ·
    refine ⟨603026855492696781969791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1608071614647191418586109 603026855492696781969791)
    ·
      refine ⟨904540283239045172954687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 603026855492696781969791 904540283239045172954687)
      ·
        refine ⟨1356810424858567759432031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 904540283239045172954687 1356810424858567759432031)
        ·
          refine ⟨2035215637287851639148047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1356810424858567759432031 2035215637287851639148047)
          ·
            refine ⟨3052823455931777458722071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035215637287851639148047 3052823455931777458722071)
            ·
              refine ⟨4579235183897666188083107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3052823455931777458722071 4579235183897666188083107)
              ·
                refine ⟨6868852775846499282124661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4579235183897666188083107 6868852775846499282124661)
                ·
                  refine ⟨643954947735609307699187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6868852775846499282124661 643954947735609307699187)
                  ·
                    refine ⟨965932421603413961548781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 643954947735609307699187 965932421603413961548781)
                    ·
                      refine ⟨362224658101280235580793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 965932421603413961548781 362224658101280235580793)
                      ·
                        rfl

theorem cell23_705430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_705430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705430 prefixEnd_705430 := by exact prefixLift 705430
  have htrace : WordTrace (prefixWord ++ tailWord_705430) baseStart_705430 baseEnd_705430 := by
    simpa [prefixWord, tailWord_705430, baseEnd_705430] using wordTrace_append hprefix tailTrace_705430
  have hstable : (prefixWord ++ tailWord_705430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705430).length < 2 ^ (prefixWord ++ tailWord_705430).sum := by decide
  have hdescent : baseEnd_705430 < baseStart_705430 := by decide
  rcases family_descends (prefixWord ++ tailWord_705430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705470 : List Nat := [4, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2]
def baseStart_705470 : Nat := 118140960795 + 705470 * 2 ^ 59
def prefixEnd_705470 : Nat := 4983230072969 + 3 ^ 40 * 705470 * 2
def baseEnd_705470 : Nat := 362245197327460079080609

theorem tailTrace_705470 : CollatzResearch.WordTrace tailWord_705470 prefixEnd_705470 362245197327460079080609 := by
  unfold tailWord_705470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3216325594276268691104233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17153736502806766352555909 3216325594276268691104233)
  ·
    refine ⟨2412244195707201518328175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3216325594276268691104233 2412244195707201518328175)
    ·
      refine ⟨3618366293560802277492263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2412244195707201518328175 3618366293560802277492263)
      ·
        refine ⟨5427549440341203416238395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3618366293560802277492263 5427549440341203416238395)
        ·
          refine ⟨8141324160511805124357593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5427549440341203416238395 8141324160511805124357593)
          ·
            refine ⟨6105993120383853843268195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8141324160511805124357593 6105993120383853843268195)
            ·
              refine ⟨9158989680575780764902293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6105993120383853843268195 9158989680575780764902293)
              ·
                refine ⟨429327641276989723354795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9158989680575780764902293 429327641276989723354795)
                ·
                  refine ⟨643991461915484585032193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429327641276989723354795 643991461915484585032193)
                  ·
                    refine ⟨482993596436613438774145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 643991461915484585032193 482993596436613438774145)
                    ·
                      refine ⟨362245197327460079080609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 482993596436613438774145 362245197327460079080609)
                      ·
                        rfl

theorem cell23_705470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_705470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705470 prefixEnd_705470 := by exact prefixLift 705470
  have htrace : WordTrace (prefixWord ++ tailWord_705470) baseStart_705470 baseEnd_705470 := by
    simpa [prefixWord, tailWord_705470, baseEnd_705470] using wordTrace_append hprefix tailTrace_705470
  have hstable : (prefixWord ++ tailWord_705470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705470).length < 2 ^ (prefixWord ++ tailWord_705470).sum := by decide
  have hdescent : baseEnd_705470 < baseStart_705470 := by decide
  rcases family_descends (prefixWord ++ tailWord_705470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705486 : List Nat := [4, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3]
def baseStart_705486 : Nat := 118140960795 + 705486 * 2 ^ 59
def prefixEnd_705486 : Nat := 4983230072969 + 3 ^ 40 * 705486 * 2
def baseEnd_705486 : Nat := 362253413017932016480535

theorem tailTrace_705486 : CollatzResearch.WordTrace tailWord_705486 prefixEnd_705486 362253413017932016480535 := by
  unfold tailWord_705486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3216398540269023032677039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17154125548101456174277541 3216398540269023032677039)
  ·
    refine ⟨4824597810403534549015559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3216398540269023032677039 4824597810403534549015559)
    ·
      refine ⟨7236896715605301823523339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4824597810403534549015559 7236896715605301823523339)
      ·
        refine ⟨10855345073407952735285009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7236896715605301823523339 10855345073407952735285009)
        ·
          refine ⟨8141508805055964551463757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10855345073407952735285009 8141508805055964551463757)
          ·
            refine ⟨3053065801895986706798909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8141508805055964551463757 3053065801895986706798909)
            ·
              refine ⟨1144899675710995015049591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3053065801895986706798909 1144899675710995015049591)
              ·
                refine ⟨1717349513566492522574387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1144899675710995015049591 1717349513566492522574387)
                ·
                  refine ⟨2576024270349738783861581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1717349513566492522574387 2576024270349738783861581)
                  ·
                    refine ⟨966009101381152043948093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2576024270349738783861581 966009101381152043948093)
                    ·
                      refine ⟨362253413017932016480535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 966009101381152043948093 362253413017932016480535)
                      ·
                        rfl

theorem cell23_705486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_705486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705486 prefixEnd_705486 := by exact prefixLift 705486
  have htrace : WordTrace (prefixWord ++ tailWord_705486) baseStart_705486 baseEnd_705486 := by
    simpa [prefixWord, tailWord_705486, baseEnd_705486] using wordTrace_append hprefix tailTrace_705486
  have hstable : (prefixWord ++ tailWord_705486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705486).length < 2 ^ (prefixWord ++ tailWord_705486).sum := by decide
  have hdescent : baseEnd_705486 < baseStart_705486 := by decide
  rcases family_descends (prefixWord ++ tailWord_705486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705493 : List Nat := [1, 3, 2, 3, 4, 1, 2, 7]
def baseStart_705493 : Nat := 118140960795 + 705493 * 2 ^ 59
def prefixEnd_705493 : Nat := 4983230072969 + 3 ^ 40 * 705493 * 2
def baseEnd_705493 : Nat := 13416926199352351447889

theorem tailTrace_705493 : CollatzResearch.WordTrace tailWord_705493 prefixEnd_705493 13416926199352351447889 := by
  unfold tailWord_705493
  simp only [CollatzResearch.WordTrace]
  refine ⟨25731443633126824456921133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17154295755417882971280755 25731443633126824456921133)
  ·
    refine ⟨9649291362422559171345425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25731443633126824456921133 9649291362422559171345425)
    ·
      refine ⟨7236968521816919378509069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9649291362422559171345425 7236968521816919378509069)
      ·
        refine ⟨2713863195681344766940901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7236968521816919378509069 2713863195681344766940901)
        ·
          refine ⟨508849349190252143801419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2713863195681344766940901 508849349190252143801419)
          ·
            refine ⟨763274023785378215702129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508849349190252143801419 763274023785378215702129)
            ·
              refine ⟨572455517839033661776597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 763274023785378215702129 572455517839033661776597)
              ·
                refine ⟨13416926199352351447889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 572455517839033661776597 13416926199352351447889)
                ·
                  rfl

theorem cell23_705493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 7].length) (baseStart_705493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705493 prefixEnd_705493 := by exact prefixLift 705493
  have htrace : WordTrace (prefixWord ++ tailWord_705493) baseStart_705493 baseEnd_705493 := by
    simpa [prefixWord, tailWord_705493, baseEnd_705493] using wordTrace_append hprefix tailTrace_705493
  have hstable : (prefixWord ++ tailWord_705493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705493).length < 2 ^ (prefixWord ++ tailWord_705493).sum := by decide
  have hdescent : baseEnd_705493 < baseStart_705493 := by decide
  rcases family_descends (prefixWord ++ tailWord_705493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705529 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 2, 4, 3]
def baseStart_705529 : Nat := 118140960795 + 705529 * 2 ^ 59
def prefixEnd_705529 : Nat := 4983230072969 + 3 ^ 40 * 705529 * 2
def baseEnd_705529 : Nat := 362275492686075348242837

theorem tailTrace_705529 : CollatzResearch.WordTrace tailWord_705529 prefixEnd_705529 362275492686075348242837 := by
  unfold tailWord_705529
  simp only [CollatzResearch.WordTrace]
  refine ⟨25732756660996402605231641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17155171107330935070154427 25732756660996402605231641)
  ·
    refine ⟨19299567495747301953923731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25732756660996402605231641 19299567495747301953923731)
    ·
      refine ⟨28949351243620952930885597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19299567495747301953923731 28949351243620952930885597)
      ·
        refine ⟨10856006716357857349082099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28949351243620952930885597 10856006716357857349082099)
        ·
          refine ⟨16284010074536786023623149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10856006716357857349082099 16284010074536786023623149)
          ·
            refine ⟨6106503777951294758858681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16284010074536786023623149 6106503777951294758858681)
            ·
              refine ⟨4579877833463471069144011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6106503777951294758858681 4579877833463471069144011)
              ·
                refine ⟨6869816750195206603716017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4579877833463471069144011 6869816750195206603716017)
                ·
                  refine ⟨5152362562646404952787013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6869816750195206603716017 5152362562646404952787013)
                  ·
                    refine ⟨966067980496200928647565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5152362562646404952787013 966067980496200928647565)
                    ·
                      refine ⟨362275492686075348242837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 966067980496200928647565 362275492686075348242837)
                      ·
                        rfl

theorem cell23_705529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_705529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705529 prefixEnd_705529 := by exact prefixLift 705529
  have htrace : WordTrace (prefixWord ++ tailWord_705529) baseStart_705529 baseEnd_705529 := by
    simpa [prefixWord, tailWord_705529, baseEnd_705529] using wordTrace_append hprefix tailTrace_705529
  have hstable : (prefixWord ++ tailWord_705529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705529).length < 2 ^ (prefixWord ++ tailWord_705529).sum := by decide
  have hdescent : baseEnd_705529 < baseStart_705529 := by decide
  rcases family_descends (prefixWord ++ tailWord_705529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705579 : List Nat := [1, 1, 1, 1, 2, 1, 5, 4, 2, 5]
def baseStart_705579 : Nat := 118140960795 + 705579 * 2 ^ 59
def prefixEnd_705579 : Nat := 4983230072969 + 3 ^ 40 * 705579 * 2
def baseEnd_705579 : Nat := 120767055572933384205869

theorem tailTrace_705579 : CollatzResearch.WordTrace tailWord_705579 prefixEnd_705579 120767055572933384205869 := by
  unfold tailWord_705579
  simp only [CollatzResearch.WordTrace]
  refine ⟨25734580310815261144551791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17156386873876840763034527 25734580310815261144551791)
  ·
    refine ⟨38601870466222891716827687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25734580310815261144551791 38601870466222891716827687)
    ·
      refine ⟨57902805699334337575241531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38601870466222891716827687 57902805699334337575241531)
      ·
        refine ⟨86854208549001506362862297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57902805699334337575241531 86854208549001506362862297)
        ·
          refine ⟨65140656411751129772146723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86854208549001506362862297 65140656411751129772146723)
          ·
            refine ⟨97710984617626694658220085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65140656411751129772146723 97710984617626694658220085)
            ·
              refine ⟨9160404807902502624208133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97710984617626694658220085 9160404807902502624208133)
              ·
                refine ⟨1717575901481719242039025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9160404807902502624208133 1717575901481719242039025)
                ·
                  refine ⟨1288181926111289431529269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1717575901481719242039025 1288181926111289431529269)
                  ·
                    refine ⟨120767055572933384205869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1288181926111289431529269 120767055572933384205869)
                    ·
                      rfl

theorem cell23_705579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 5].length) (baseStart_705579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705579 prefixEnd_705579 := by exact prefixLift 705579
  have htrace : WordTrace (prefixWord ++ tailWord_705579) baseStart_705579 baseEnd_705579 := by
    simpa [prefixWord, tailWord_705579, baseEnd_705579] using wordTrace_append hprefix tailTrace_705579
  have hstable : (prefixWord ++ tailWord_705579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705579).length < 2 ^ (prefixWord ++ tailWord_705579).sum := by decide
  have hdescent : baseEnd_705579 < baseStart_705579 := by decide
  rcases family_descends (prefixWord ++ tailWord_705579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705586 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2]
def baseStart_705586 : Nat := 118140960795 + 705586 * 2 ^ 59
def prefixEnd_705586 : Nat := 4983230072969 + 3 ^ 40 * 705586 * 2
def baseEnd_705586 : Nat := 362304761083381625230075

theorem tailTrace_705586 : CollatzResearch.WordTrace tailWord_705586 prefixEnd_705586 362304761083381625230075 := by
  unfold tailWord_705586
  simp only [CollatzResearch.WordTrace]
  refine ⟨6433708905447475335014153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17156557081193267560037741 6433708905447475335014153)
  ·
    refine ⟨4825281679085606501260615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6433708905447475335014153 4825281679085606501260615)
    ·
      refine ⟨7237922518628409751890923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4825281679085606501260615 7237922518628409751890923)
      ·
        refine ⟨10856883777942614627836385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7237922518628409751890923 10856883777942614627836385)
        ·
          refine ⟨8142662833456960970877289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10856883777942614627836385 8142662833456960970877289)
          ·
            refine ⟨6106997125092720728157967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8142662833456960970877289 6106997125092720728157967)
            ·
              refine ⟨9160495687639081092236951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6106997125092720728157967 9160495687639081092236951)
              ·
                refine ⟨13740743531458621638355427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9160495687639081092236951 13740743531458621638355427)
                ·
                  refine ⟨20611115297187932457533141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13740743531458621638355427 20611115297187932457533141)
                  ·
                    refine ⟨483073014777842166973433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20611115297187932457533141 483073014777842166973433)
                    ·
                      refine ⟨362304761083381625230075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 483073014777842166973433 362304761083381625230075)
                      ·
                        rfl

theorem cell23_705586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2].length) (baseStart_705586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705586 prefixEnd_705586 := by exact prefixLift 705586
  have htrace : WordTrace (prefixWord ++ tailWord_705586) baseStart_705586 baseEnd_705586 := by
    simpa [prefixWord, tailWord_705586, baseEnd_705586] using wordTrace_append hprefix tailTrace_705586
  have hstable : (prefixWord ++ tailWord_705586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705586).length < 2 ^ (prefixWord ++ tailWord_705586).sum := by decide
  have hdescent : baseEnd_705586 < baseStart_705586 := by decide
  rcases family_descends (prefixWord ++ tailWord_705586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705599 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 4]
def baseStart_705599 : Nat := 118140960795 + 705599 * 2 ^ 59
def prefixEnd_705599 : Nat := 4983230072969 + 3 ^ 40 * 705599 * 2
def baseEnd_705599 : Nat := 362311436331890074367515

theorem tailTrace_705599 : CollatzResearch.WordTrace tailWord_705599 prefixEnd_705599 362311436331890074367515 := by
  unfold tailWord_705599
  simp only [CollatzResearch.WordTrace]
  refine ⟨25735309770742804560279851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17156873180495203040186567 25735309770742804560279851)
  ·
    refine ⟨38602964656114206840419777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25735309770742804560279851 38602964656114206840419777)
    ·
      refine ⟨28952223492085655130314833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38602964656114206840419777 28952223492085655130314833)
      ·
        refine ⟨21714167619064241347736125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28952223492085655130314833 21714167619064241347736125)
        ·
          refine ⟨8142812857149090505401047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21714167619064241347736125 8142812857149090505401047)
          ·
            refine ⟨12214219285723635758101571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8142812857149090505401047 12214219285723635758101571)
            ·
              refine ⟨18321328928585453637152357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12214219285723635758101571 18321328928585453637152357)
              ·
                refine ⟨3435249174109772556966067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18321328928585453637152357 3435249174109772556966067)
                ·
                  refine ⟨5152873761164658835449101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3435249174109772556966067 5152873761164658835449101)
                  ·
                    refine ⟨1932327660436747063293413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5152873761164658835449101 1932327660436747063293413)
                    ·
                      refine ⟨362311436331890074367515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1932327660436747063293413 362311436331890074367515)
                      ·
                        rfl

theorem cell23_705599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_705599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705599 prefixEnd_705599 := by exact prefixLift 705599
  have htrace : WordTrace (prefixWord ++ tailWord_705599) baseStart_705599 baseEnd_705599 := by
    simpa [prefixWord, tailWord_705599, baseEnd_705599] using wordTrace_append hprefix tailTrace_705599
  have hstable : (prefixWord ++ tailWord_705599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705599).length < 2 ^ (prefixWord ++ tailWord_705599).sum := by decide
  have hdescent : baseEnd_705599 < baseStart_705599 := by decide
  rcases family_descends (prefixWord ++ tailWord_705599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705613 : List Nat := [1, 6, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_705613 : Nat := 118140960795 + 705613 * 2 ^ 59
def prefixEnd_705613 : Nat := 4983230072969 + 3 ^ 40 * 705613 * 2
def baseEnd_705613 : Nat := 120772875020351006530817

theorem tailTrace_705613 : CollatzResearch.WordTrace tailWord_705613 prefixEnd_705613 120772875020351006530817 := by
  unfold tailWord_705613
  simp only [CollatzResearch.WordTrace]
  refine ⟨25735820392692084951289493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17157213595128056634192995 25735820392692084951289493)
  ·
    refine ⟨1206366580907441482091695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25735820392692084951289493 1206366580907441482091695)
    ·
      refine ⟨1809549871361162223137543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1206366580907441482091695 1809549871361162223137543)
      ·
        refine ⟨2714324807041743334706315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1809549871361162223137543 2714324807041743334706315)
        ·
          refine ⟨4071487210562615002059473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2714324807041743334706315 4071487210562615002059473)
          ·
            refine ⟨3053615407921961251544605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4071487210562615002059473 3053615407921961251544605)
            ·
              refine ⟨1145105777970735469329227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3053615407921961251544605 1145105777970735469329227)
              ·
                refine ⟨1717658666956103203993841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1145105777970735469329227 1717658666956103203993841)
                ·
                  refine ⟨1288244000217077402995381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1717658666956103203993841 1288244000217077402995381)
                  ·
                    refine ⟨120772875020351006530817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1288244000217077402995381 120772875020351006530817)
                    ·
                      rfl

theorem cell23_705613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_705613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705613 prefixEnd_705613 := by exact prefixLift 705613
  have htrace : WordTrace (prefixWord ++ tailWord_705613) baseStart_705613 baseEnd_705613 := by
    simpa [prefixWord, tailWord_705613, baseEnd_705613] using wordTrace_append hprefix tailTrace_705613
  have hstable : (prefixWord ++ tailWord_705613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705613).length < 2 ^ (prefixWord ++ tailWord_705613).sum := by decide
  have hdescent : baseEnd_705613 < baseStart_705613 := by decide
  rcases family_descends (prefixWord ++ tailWord_705613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705636 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 4, 2, 3]
def baseStart_705636 : Nat := 118140960795 + 705636 * 2 ^ 59
def prefixEnd_705636 : Nat := 4983230072969 + 3 ^ 40 * 705636 * 2
def baseEnd_705636 : Nat := 362330435116106429604845

theorem tailTrace_705636 : CollatzResearch.WordTrace tailWord_705636 prefixEnd_705636 362330435116106429604845 := by
  unfold tailWord_705636
  simp only [CollatzResearch.WordTrace]
  refine ⟨12868329635804379939688381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17157772847739173252917841 12868329635804379939688381)
  ·
    refine ⟨4825623613426642477383143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12868329635804379939688381 4825623613426642477383143)
    ·
      refine ⟨7238435420139963716074715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4825623613426642477383143 7238435420139963716074715)
      ·
        refine ⟨10857653130209945574112073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7238435420139963716074715 10857653130209945574112073)
        ·
          refine ⟨8143239847657459180584055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10857653130209945574112073 8143239847657459180584055)
          ·
            refine ⟨12214859771486188770876083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8143239847657459180584055 12214859771486188770876083)
            ·
              refine ⟨18322289657229283156314125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12214859771486188770876083 18322289657229283156314125)
              ·
                refine ⟨6870858621460981183617797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18322289657229283156314125 6870858621460981183617797)
                ·
                  refine ⟨1288285991523933971928337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6870858621460981183617797 1288285991523933971928337)
                  ·
                    refine ⟨966214493642950478946253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1288285991523933971928337 966214493642950478946253)
                    ·
                      refine ⟨362330435116106429604845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 966214493642950478946253 362330435116106429604845)
                      ·
                        rfl

theorem cell23_705636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_705636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705636 prefixEnd_705636 := by exact prefixLift 705636
  have htrace : WordTrace (prefixWord ++ tailWord_705636) baseStart_705636 baseEnd_705636 := by
    simpa [prefixWord, tailWord_705636, baseEnd_705636] using wordTrace_append hprefix tailTrace_705636
  have hstable : (prefixWord ++ tailWord_705636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705636).length < 2 ^ (prefixWord ++ tailWord_705636).sum := by decide
  have hdescent : baseEnd_705636 < baseStart_705636 := by decide
  rcases family_descends (prefixWord ++ tailWord_705636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705694 : List Nat := [4, 3, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_705694 : Nat := 118140960795 + 705694 * 2 ^ 59
def prefixEnd_705694 : Nat := 4983230072969 + 3 ^ 40 * 705694 * 2
def baseEnd_705694 : Nat := 120786738998022400893193

theorem tailTrace_705694 : CollatzResearch.WordTrace tailWord_705694 prefixEnd_705694 120786738998022400893193 := by
  unfold tailWord_705694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3217346838174829473123517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17159183136932423856658757 3217346838174829473123517)
  ·
    refine ⟨1206505064315561052421319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3217346838174829473123517 1206505064315561052421319)
    ·
      refine ⟨1809757596473341578631979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1206505064315561052421319 1809757596473341578631979)
      ·
        refine ⟨2714636394710012367947969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1809757596473341578631979 2714636394710012367947969)
        ·
          refine ⟨2035977296032509275960977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2714636394710012367947969 2035977296032509275960977)
          ·
            refine ⟨1526982972024381956970733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2035977296032509275960977 1526982972024381956970733)
            ·
              refine ⟨572618614509143233864025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1526982972024381956970733 572618614509143233864025)
              ·
                refine ⟨429463960881857425398019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572618614509143233864025 429463960881857425398019)
                ·
                  refine ⟨644195941322786138097029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429463960881857425398019 644195941322786138097029)
                  ·
                    refine ⟨120786738998022400893193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 644195941322786138097029 120786738998022400893193)
                    ·
                      rfl

theorem cell23_705694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_705694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705694 prefixEnd_705694 := by exact prefixLift 705694
  have htrace : WordTrace (prefixWord ++ tailWord_705694) baseStart_705694 baseEnd_705694 := by
    simpa [prefixWord, tailWord_705694, baseEnd_705694] using wordTrace_append hprefix tailTrace_705694
  have hstable : (prefixWord ++ tailWord_705694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705694).length < 2 ^ (prefixWord ++ tailWord_705694).sum := by decide
  have hdescent : baseEnd_705694 < baseStart_705694 := by decide
  rcases family_descends (prefixWord ++ tailWord_705694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705700 : List Nat := [2, 3, 1, 2, 3, 1, 3, 1, 3, 1, 3]
def baseStart_705700 : Nat := 118140960795 + 705700 * 2 ^ 59
def prefixEnd_705700 : Nat := 4983230072969 + 3 ^ 40 * 705700 * 2
def baseEnd_705700 : Nat := 362363297877994179204551

theorem tailTrace_705700 : CollatzResearch.WordTrace tailWord_705700 prefixEnd_705700 362363297877994179204551 := by
  unfold tailWord_705700
  simp only [CollatzResearch.WordTrace]
  refine ⟨12869496771688449404853277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17159329028917932539804369 12869496771688449404853277)
  ·
    refine ⟨4826061289383168526819979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12869496771688449404853277 4826061289383168526819979)
    ·
      refine ⟨7239091934074752790229969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4826061289383168526819979 7239091934074752790229969)
      ·
        refine ⟨5429318950556064592672477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7239091934074752790229969 5429318950556064592672477)
        ·
          refine ⟨2035994606458524222252179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5429318950556064592672477 2035994606458524222252179)
          ·
            refine ⟨3053991909687786333378269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035994606458524222252179 3053991909687786333378269)
            ·
              refine ⟨1145246966132919875016851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3053991909687786333378269 1145246966132919875016851)
              ·
                refine ⟨1717870449199379812525277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1145246966132919875016851 1717870449199379812525277)
                ·
                  refine ⟨644201418449767429696979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1717870449199379812525277 644201418449767429696979)
                  ·
                    refine ⟨966302127674651144545469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 644201418449767429696979 966302127674651144545469)
                    ·
                      refine ⟨362363297877994179204551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 966302127674651144545469 362363297877994179204551)
                      ·
                        rfl

theorem cell23_705700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_705700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705700 prefixEnd_705700 := by exact prefixLift 705700
  have htrace : WordTrace (prefixWord ++ tailWord_705700) baseStart_705700 baseEnd_705700 := by
    simpa [prefixWord, tailWord_705700, baseEnd_705700] using wordTrace_append hprefix tailTrace_705700
  have hstable : (prefixWord ++ tailWord_705700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705700).length < 2 ^ (prefixWord ++ tailWord_705700).sum := by decide
  have hdescent : baseEnd_705700 < baseStart_705700 := by decide
  rcases family_descends (prefixWord ++ tailWord_705700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705736 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 3, 2, 4]
def baseStart_705736 : Nat := 118140960795 + 705736 * 2 ^ 59
def prefixEnd_705736 : Nat := 4983230072969 + 3 ^ 40 * 705736 * 2
def baseEnd_705736 : Nat := 362381783181556038354385

theorem tailTrace_705736 : CollatzResearch.WordTrace tailWord_705736 prefixEnd_705736 362381783181556038354385 := by
  unfold tailWord_705736
  simp only [CollatzResearch.WordTrace]
  refine ⟨12870153285623238479008531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17160204380830984638678041 12870153285623238479008531)
  ·
    refine ⟨19305229928434857718512797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12870153285623238479008531 19305229928434857718512797)
    ·
      refine ⟨7239461223163071644442299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19305229928434857718512797 7239461223163071644442299)
      ·
        refine ⟨10859191834744607466663449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7239461223163071644442299 10859191834744607466663449)
        ·
          refine ⟨8144393876058455599997587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10859191834744607466663449 8144393876058455599997587)
          ·
            refine ⟨12216590814087683399996381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8144393876058455599997587 12216590814087683399996381)
            ·
              refine ⟨4581221555282881274998643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12216590814087683399996381 4581221555282881274998643)
              ·
                refine ⟨6871832332924321912497965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4581221555282881274998643 6871832332924321912497965)
                ·
                  refine ⟨2576937124846620717186737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6871832332924321912497965 2576937124846620717186737)
                  ·
                    refine ⟨1932702843634965537890053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2576937124846620717186737 1932702843634965537890053)
                    ·
                      refine ⟨362381783181556038354385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1932702843634965537890053 362381783181556038354385)
                      ·
                        rfl

theorem cell23_705736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_705736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705736 prefixEnd_705736 := by exact prefixLift 705736
  have htrace : WordTrace (prefixWord ++ tailWord_705736) baseStart_705736 baseEnd_705736 := by
    simpa [prefixWord, tailWord_705736, baseEnd_705736] using wordTrace_append hprefix tailTrace_705736
  have hstable : (prefixWord ++ tailWord_705736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705736).length < 2 ^ (prefixWord ++ tailWord_705736).sum := by decide
  have hdescent : baseEnd_705736 < baseStart_705736 := by decide
  rcases family_descends (prefixWord ++ tailWord_705736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705786 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5]
def baseStart_705786 : Nat := 118140960795 + 705786 * 2 ^ 59
def prefixEnd_705786 : Nat := 4983230072969 + 3 ^ 40 * 705786 * 2
def baseEnd_705786 : Nat := 362407457214280842729155

theorem tailTrace_705786 : CollatzResearch.WordTrace tailWord_705786 prefixEnd_705786 362407457214280842729155 := by
  unfold tailWord_705786
  simp only [CollatzResearch.WordTrace]
  refine ⟨6435532555266333874334303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17161420147376890331558141 6435532555266333874334303)
  ·
    refine ⟨9653298832899500811501455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6435532555266333874334303 9653298832899500811501455)
    ·
      refine ⟨14479948249349251217252183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9653298832899500811501455 14479948249349251217252183)
      ·
        refine ⟨21719922374023876825878275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14479948249349251217252183 21719922374023876825878275)
        ·
          refine ⟨32579883561035815238817413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21719922374023876825878275 32579883561035815238817413)
          ·
            refine ⟨6108728167694215357278265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32579883561035815238817413 6108728167694215357278265)
            ·
              refine ⟨4581546125770661517958699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6108728167694215357278265 4581546125770661517958699)
              ·
                refine ⟨6872319188655992276938049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4581546125770661517958699 6872319188655992276938049)
                ·
                  refine ⟨5154239391491994207703537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6872319188655992276938049 5154239391491994207703537)
                  ·
                    refine ⟨3865679543618995655777653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5154239391491994207703537 3865679543618995655777653)
                    ·
                      refine ⟨362407457214280842729155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3865679543618995655777653 362407457214280842729155)
                      ·
                        rfl

theorem cell23_705786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_705786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705786 prefixEnd_705786 := by exact prefixLift 705786
  have htrace : WordTrace (prefixWord ++ tailWord_705786) baseStart_705786 baseEnd_705786 := by
    simpa [prefixWord, tailWord_705786, baseEnd_705786] using wordTrace_append hprefix tailTrace_705786
  have hstable : (prefixWord ++ tailWord_705786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705786).length < 2 ^ (prefixWord ++ tailWord_705786).sum := by decide
  have hdescent : baseEnd_705786 < baseStart_705786 := by decide
  rcases family_descends (prefixWord ++ tailWord_705786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705790 : List Nat := [4, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_705790 : Nat := 118140960795 + 705790 * 2 ^ 59
def prefixEnd_705790 : Nat := 4983230072969 + 3 ^ 40 * 705790 * 2
def baseEnd_705790 : Nat := 362409511136898827079137

theorem tailTrace_705790 : CollatzResearch.WordTrace tailWord_705790 prefixEnd_705790 362409511136898827079137 := by
  unfold tailWord_705790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3217784514131355522560353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17161517408700562786988549 3217784514131355522560353)
  ·
    refine ⟨2413338385598516641920265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3217784514131355522560353 2413338385598516641920265)
    ·
      refine ⟨1810003789198887481440199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2413338385598516641920265 1810003789198887481440199)
      ·
        refine ⟨2715005683798331222160299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1810003789198887481440199 2715005683798331222160299)
        ·
          refine ⟨4072508525697496833240449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2715005683798331222160299 4072508525697496833240449)
          ·
            refine ⟨3054381394273122624930337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4072508525697496833240449 3054381394273122624930337)
            ·
              refine ⟨2290786045704841968697753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3054381394273122624930337 2290786045704841968697753)
              ·
                refine ⟨1718089534278631476523315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2290786045704841968697753 1718089534278631476523315)
                ·
                  refine ⟨2577134301417947214784973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1718089534278631476523315 2577134301417947214784973)
                  ·
                    refine ⟨966425363031730205544365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2577134301417947214784973 966425363031730205544365)
                    ·
                      refine ⟨362409511136898827079137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 966425363031730205544365 362409511136898827079137)
                      ·
                        rfl

theorem cell23_705790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_705790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705790 prefixEnd_705790 := by exact prefixLift 705790
  have htrace : WordTrace (prefixWord ++ tailWord_705790) baseStart_705790 baseEnd_705790 := by
    simpa [prefixWord, tailWord_705790, baseEnd_705790] using wordTrace_append hprefix tailTrace_705790
  have hstable : (prefixWord ++ tailWord_705790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705790).length < 2 ^ (prefixWord ++ tailWord_705790).sum := by decide
  have hdescent : baseEnd_705790 < baseStart_705790 := by decide
  rcases family_descends (prefixWord ++ tailWord_705790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705824 : List Nat := [2, 1, 1, 5, 3, 1, 3, 1, 2, 1, 3]
def baseStart_705824 : Nat := 118140960795 + 705824 * 2 ^ 59
def prefixEnd_705824 : Nat := 4983230072969 + 3 ^ 40 * 705824 * 2
def baseEnd_705824 : Nat := 362426969479151694053981

theorem tailTrace_705824 : CollatzResearch.WordTrace tailWord_705824 prefixEnd_705824 362426969479151694053981 := by
  unfold tailWord_705824
  simp only [CollatzResearch.WordTrace]
  refine ⟨12871758097463833993610263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17162344129951778658147017 12871758097463833993610263)
  ·
    refine ⟨19307637146195750990415395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12871758097463833993610263 19307637146195750990415395)
    ·
      refine ⟨28961455719293626485623093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19307637146195750990415395 28961455719293626485623093)
      ·
        refine ⟨2715136473683777483027165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28961455719293626485623093 2715136473683777483027165)
        ·
          refine ⟨1018176177631416556135187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2715136473683777483027165 1018176177631416556135187)
          ·
            refine ⟨1527264266447124834202781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1018176177631416556135187 1527264266447124834202781)
            ·
              refine ⟨572724099917671812826043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1527264266447124834202781 572724099917671812826043)
              ·
                refine ⟨859086149876507719239065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 572724099917671812826043 859086149876507719239065)
                ·
                  refine ⟨644314612407380789429299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 859086149876507719239065 644314612407380789429299)
                  ·
                    refine ⟨966471918611071184143949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 644314612407380789429299 966471918611071184143949)
                    ·
                      refine ⟨362426969479151694053981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 966471918611071184143949 362426969479151694053981)
                      ·
                        rfl

theorem cell23_705824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_705824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705824 prefixEnd_705824 := by exact prefixLift 705824
  have htrace : WordTrace (prefixWord ++ tailWord_705824) baseStart_705824 baseEnd_705824 := by
    simpa [prefixWord, tailWord_705824, baseEnd_705824] using wordTrace_append hprefix tailTrace_705824
  have hstable : (prefixWord ++ tailWord_705824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705824).length < 2 ^ (prefixWord ++ tailWord_705824).sum := by decide
  have hdescent : baseEnd_705824 < baseStart_705824 := by decide
  rcases family_descends (prefixWord ++ tailWord_705824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705834 : List Nat := [3, 1, 4, 2, 1, 2, 2, 2, 1, 3, 2]
def baseStart_705834 : Nat := 118140960795 + 705834 * 2 ^ 59
def prefixEnd_705834 : Nat := 4983230072969 + 3 ^ 40 * 705834 * 2
def baseEnd_705834 : Nat := 362432104285696654928935

theorem tailTrace_705834 : CollatzResearch.WordTrace tailWord_705834 prefixEnd_705834 362432104285696654928935 := by
  unfold tailWord_705834
  simp only [CollatzResearch.WordTrace]
  refine ⟨6435970231222859923771139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17162587283260959796723037 6435970231222859923771139)
  ·
    refine ⟨9653955346834289885656709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6435970231222859923771139 9653955346834289885656709)
    ·
      refine ⟨1810116627531429353560633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9653955346834289885656709 1810116627531429353560633)
      ·
        refine ⟨1357587470648572015170475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1810116627531429353560633 1357587470648572015170475)
        ·
          refine ⟨2036381205972858022755713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1357587470648572015170475 2036381205972858022755713)
          ·
            refine ⟨1527285904479643517066785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2036381205972858022755713 1527285904479643517066785)
            ·
              refine ⟨1145464428359732637800089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1527285904479643517066785 1145464428359732637800089)
              ·
                refine ⟨859098321269799478350067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1145464428359732637800089 859098321269799478350067)
                ·
                  refine ⟨1288647481904699217525101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 859098321269799478350067 1288647481904699217525101)
                  ·
                    refine ⟨483242805714262206571913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1288647481904699217525101 483242805714262206571913)
                    ·
                      refine ⟨362432104285696654928935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 483242805714262206571913 362432104285696654928935)
                      ·
                        rfl

theorem cell23_705834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_705834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705834 prefixEnd_705834 := by exact prefixLift 705834
  have htrace : WordTrace (prefixWord ++ tailWord_705834) baseStart_705834 baseEnd_705834 := by
    simpa [prefixWord, tailWord_705834, baseEnd_705834] using wordTrace_append hprefix tailTrace_705834
  have hstable : (prefixWord ++ tailWord_705834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705834).length < 2 ^ (prefixWord ++ tailWord_705834).sum := by decide
  have hdescent : baseEnd_705834 < baseStart_705834 := by decide
  rcases family_descends (prefixWord ++ tailWord_705834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705885 : List Nat := [1, 4, 5, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_705885 : Nat := 118140960795 + 705885 * 2 ^ 59
def prefixEnd_705885 : Nat := 4983230072969 + 3 ^ 40 * 705885 * 2
def baseEnd_705885 : Nat := 362458291799075955391201

theorem tailTrace_705885 : CollatzResearch.WordTrace tailWord_705885 prefixEnd_705885 362458291799075955391201 := by
  unfold tailWord_705885
  simp only [CollatzResearch.WordTrace]
  refine ⟨25745741047706675405191109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17163827365137783603460739 25745741047706675405191109)
  ·
    refine ⟨4827326446445001638473333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25745741047706675405191109 4827326446445001638473333)
    ·
      refine ⟨452561854354218903606875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4827326446445001638473333 452561854354218903606875)
      ·
        refine ⟨678842781531328355410313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452561854354218903606875 678842781531328355410313)
        ·
          refine ⟨509132086148496266557735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 678842781531328355410313 509132086148496266557735)
          ·
            refine ⟨763698129222744399836603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509132086148496266557735 763698129222744399836603)
            ·
              refine ⟨1145547193834116599754905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 763698129222744399836603 1145547193834116599754905)
              ·
                refine ⟨859160395375587449816179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1145547193834116599754905 859160395375587449816179)
                ·
                  refine ⟨1288740593063381174724269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 859160395375587449816179 1288740593063381174724269)
                  ·
                    refine ⟨483277722398767940521601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1288740593063381174724269 483277722398767940521601)
                    ·
                      refine ⟨362458291799075955391201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 483277722398767940521601 362458291799075955391201)
                      ·
                        rfl

theorem cell23_705885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_705885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705885 prefixEnd_705885 := by exact prefixLift 705885
  have htrace : WordTrace (prefixWord ++ tailWord_705885) baseStart_705885 baseEnd_705885 := by
    simpa [prefixWord, tailWord_705885, baseEnd_705885] using wordTrace_append hprefix tailTrace_705885
  have hstable : (prefixWord ++ tailWord_705885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705885).length < 2 ^ (prefixWord ++ tailWord_705885).sum := by decide
  have hdescent : baseEnd_705885 < baseStart_705885 := by decide
  rcases family_descends (prefixWord ++ tailWord_705885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705900 : List Nat := [2, 2, 1, 1, 5, 2, 2, 1, 2, 5]
def baseStart_705900 : Nat := 118140960795 + 705900 * 2 ^ 59
def prefixEnd_705900 : Nat := 4983230072969 + 3 ^ 40 * 705900 * 2
def baseEnd_705900 : Nat := 120821998002964465567877

theorem tailTrace_705900 : CollatzResearch.WordTrace tailWord_705900 prefixEnd_705900 120821998002964465567877 := by
  unfold tailWord_705900
  simp only [CollatzResearch.WordTrace]
  refine ⟨12873144071326166483493577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17164192095101555311324769 12873144071326166483493577)
  ·
    refine ⟨9654858053494624862620183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12873144071326166483493577 9654858053494624862620183)
    ·
      refine ⟨14482287080241937293930275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9654858053494624862620183 14482287080241937293930275)
      ·
        refine ⟨21723430620362905940895413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14482287080241937293930275 21723430620362905940895413)
        ·
          refine ⟨2036571620659022431958945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21723430620362905940895413 2036571620659022431958945)
          ·
            refine ⟨1527428715494266823969209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2036571620659022431958945 1527428715494266823969209)
            ·
              refine ⟨1145571536620700117976907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1527428715494266823969209 1145571536620700117976907)
              ·
                refine ⟨1718357304931050176965361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1145571536620700117976907 1718357304931050176965361)
                ·
                  refine ⟨1288767978698287632724021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1718357304931050176965361 1288767978698287632724021)
                  ·
                    refine ⟨120821998002964465567877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1288767978698287632724021 120821998002964465567877)
                    ·
                      rfl

theorem cell23_705900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 5].length) (baseStart_705900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705900 prefixEnd_705900 := by exact prefixLift 705900
  have htrace : WordTrace (prefixWord ++ tailWord_705900) baseStart_705900 baseEnd_705900 := by
    simpa [prefixWord, tailWord_705900, baseEnd_705900] using wordTrace_append hprefix tailTrace_705900
  have hstable : (prefixWord ++ tailWord_705900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705900).length < 2 ^ (prefixWord ++ tailWord_705900).sum := by decide
  have hdescent : baseEnd_705900 < baseStart_705900 := by decide
  rcases family_descends (prefixWord ++ tailWord_705900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705921 : List Nat := [1, 2, 4, 3, 3, 1, 2, 2, 5]
def baseStart_705921 : Nat := 118140960795 + 705921 * 2 ^ 59
def prefixEnd_705921 : Nat := 4983230072969 + 3 ^ 40 * 705921 * 2
def baseEnd_705921 : Nat := 40275197455848646060115

theorem tailTrace_705921 : CollatzResearch.WordTrace tailWord_705921 prefixEnd_705921 40275197455848646060115 := by
  unfold tailWord_705921
  simp only [CollatzResearch.WordTrace]
  refine ⟨25747054075576253553501617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17164702717050835702334411 25747054075576253553501617)
  ·
    refine ⟨19310290556682190165126213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25747054075576253553501617 19310290556682190165126213)
    ·
      refine ⟨3620679479377910655961165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19310290556682190165126213 3620679479377910655961165)
      ·
        refine ⟨1357754804766716495985437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3620679479377910655961165 1357754804766716495985437)
        ·
          refine ⟨509158051787518685994539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1357754804766716495985437 509158051787518685994539)
          ·
            refine ⟨763737077681278028991809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509158051787518685994539 763737077681278028991809)
            ·
              refine ⟨572802808260958521743857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 763737077681278028991809 572802808260958521743857)
              ·
                refine ⟨429602106195718891307893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572802808260958521743857 429602106195718891307893)
                ·
                  refine ⟨40275197455848646060115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 429602106195718891307893 40275197455848646060115)
                  ·
                    rfl

theorem cell23_705921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 5].length) (baseStart_705921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705921 prefixEnd_705921 := by exact prefixLift 705921
  have htrace : WordTrace (prefixWord ++ tailWord_705921) baseStart_705921 baseEnd_705921 := by
    simpa [prefixWord, tailWord_705921, baseEnd_705921] using wordTrace_append hprefix tailTrace_705921
  have hstable : (prefixWord ++ tailWord_705921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705921).length < 2 ^ (prefixWord ++ tailWord_705921).sum := by decide
  have hdescent : baseEnd_705921 < baseStart_705921 := by decide
  rcases family_descends (prefixWord ++ tailWord_705921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705977 : List Nat := [1, 2, 1, 4, 4, 2, 1, 2, 6]
def baseStart_705977 : Nat := 118140960795 + 705977 * 2 ^ 59
def prefixEnd_705977 : Nat := 4983230072969 + 3 ^ 40 * 705977 * 2
def baseEnd_705977 : Nat := 40278392446587732826753

theorem tailTrace_705977 : CollatzResearch.WordTrace tailWord_705977 prefixEnd_705977 40278392446587732826753 := by
  unfold tailWord_705977
  simp only [CollatzResearch.WordTrace]
  refine ⟨25749096563373375117540185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17166064375582250078360123 25749096563373375117540185)
  ·
    refine ⟨19311822422530031338155139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25749096563373375117540185 19311822422530031338155139)
    ·
      refine ⟨28967733633795047007232709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19311822422530031338155139 28967733633795047007232709)
      ·
        refine ⟨5431450056336571313856133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28967733633795047007232709 5431450056336571313856133)
        ·
          refine ⟨1018396885563107121348025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5431450056336571313856133 1018396885563107121348025)
          ·
            refine ⟨763797664172330341011019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1018396885563107121348025 763797664172330341011019)
            ·
              refine ⟨1145696496258495511516529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 763797664172330341011019 1145696496258495511516529)
              ·
                refine ⟨859272372193871633637397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1145696496258495511516529 859272372193871633637397)
                ·
                  refine ⟨40278392446587732826753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 859272372193871633637397 40278392446587732826753)
                  ·
                    rfl

theorem cell23_705977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 6].length) (baseStart_705977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_705977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_705977 prefixEnd_705977 := by exact prefixLift 705977
  have htrace : WordTrace (prefixWord ++ tailWord_705977) baseStart_705977 baseEnd_705977 := by
    simpa [prefixWord, tailWord_705977, baseEnd_705977] using wordTrace_append hprefix tailTrace_705977
  have hstable : (prefixWord ++ tailWord_705977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705977).length < 2 ^ (prefixWord ++ tailWord_705977).sum := by decide
  have hdescent : baseEnd_705977 < baseStart_705977 := by decide
  rcases family_descends (prefixWord ++ tailWord_705977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706021 : List Nat := [1, 3, 1, 5, 1, 1, 3, 3, 1, 1, 3]
def baseStart_706021 : Nat := 118140960795 + 706021 * 2 ^ 59
def prefixEnd_706021 : Nat := 4983230072969 + 3 ^ 40 * 706021 * 2
def baseEnd_706021 : Nat := 362528125168087423290575

theorem tailTrace_706021 : CollatzResearch.WordTrace tailWord_706021 prefixEnd_706021 362528125168087423290575 := by
  unfold tailWord_706021
  simp only [CollatzResearch.WordTrace]
  refine ⟨25750701375213970632141917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17167134250142647088094611 25750701375213970632141917)
  ·
    refine ⟨9656513015705238987053219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25750701375213970632141917 9656513015705238987053219)
    ·
      refine ⟨14484769523557858480579829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9656513015705238987053219 14484769523557858480579829)
      ·
        refine ⟨1357947142833549232554359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14484769523557858480579829 1357947142833549232554359)
        ·
          refine ⟨2036920714250323848831539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1357947142833549232554359 2036920714250323848831539)
          ·
            refine ⟨3055381071375485773247309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2036920714250323848831539 3055381071375485773247309)
            ·
              refine ⟨1145767901765807164967741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3055381071375485773247309 1145767901765807164967741)
              ·
                refine ⟨429662963162177686862903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1145767901765807164967741 429662963162177686862903)
                ·
                  refine ⟨644494444743266530294355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429662963162177686862903 644494444743266530294355)
                  ·
                    refine ⟨966741667114899795441533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 644494444743266530294355 966741667114899795441533)
                    ·
                      refine ⟨362528125168087423290575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 966741667114899795441533 362528125168087423290575)
                      ·
                        rfl

theorem cell23_706021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_706021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706021 prefixEnd_706021 := by exact prefixLift 706021
  have htrace : WordTrace (prefixWord ++ tailWord_706021) baseStart_706021 baseEnd_706021 := by
    simpa [prefixWord, tailWord_706021, baseEnd_706021] using wordTrace_append hprefix tailTrace_706021
  have hstable : (prefixWord ++ tailWord_706021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706021).length < 2 ^ (prefixWord ++ tailWord_706021).sum := by decide
  have hdescent : baseEnd_706021 < baseStart_706021 := by decide
  rcases family_descends (prefixWord ++ tailWord_706021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706033 : List Nat := [1, 2, 2, 2, 3, 2, 11]
def baseStart_706033 : Nat := 118140960795 + 706033 * 2 ^ 59
def prefixEnd_706033 : Nat := 4983230072969 + 3 ^ 40 * 706033 * 2
def baseEnd_706033 : Nat := 4475731937480757732599

theorem tailTrace_706033 : CollatzResearch.WordTrace tailWord_706033 prefixEnd_706033 4475731937480757732599 := by
  unfold tailWord_706033
  simp only [CollatzResearch.WordTrace]
  refine ⟨25751139051170496681578753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17167426034113664454385835 25751139051170496681578753)
  ·
    refine ⟨19313354288377872511184065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25751139051170496681578753 19313354288377872511184065)
    ·
      refine ⟨14485015716283404383388049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19313354288377872511184065 14485015716283404383388049)
      ·
        refine ⟨10863761787212553287541037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14485015716283404383388049 10863761787212553287541037)
        ·
          refine ⟨4073910670204707482827889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10863761787212553287541037 4073910670204707482827889)
          ·
            refine ⟨3055433002653530612120917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4073910670204707482827889 3055433002653530612120917)
            ·
              refine ⟨4475731937480757732599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 3055433002653530612120917 4475731937480757732599)
              ·
                rfl

theorem cell23_706033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 11].length) (baseStart_706033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706033 prefixEnd_706033 := by exact prefixLift 706033
  have htrace : WordTrace (prefixWord ++ tailWord_706033) baseStart_706033 baseEnd_706033 := by
    simpa [prefixWord, tailWord_706033, baseEnd_706033] using wordTrace_append hprefix tailTrace_706033
  have hstable : (prefixWord ++ tailWord_706033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706033).length < 2 ^ (prefixWord ++ tailWord_706033).sum := by decide
  have hdescent : baseEnd_706033 < baseStart_706033 := by decide
  rcases family_descends (prefixWord ++ tailWord_706033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706038 : List Nat := [5, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3]
def baseStart_706038 : Nat := 118140960795 + 706038 * 2 ^ 59
def prefixEnd_706038 : Nat := 4983230072969 + 3 ^ 40 * 706038 * 2
def baseEnd_706038 : Nat := 362536854339213856777997

theorem tailTrace_706038 : CollatzResearch.WordTrace tailWord_706038 prefixEnd_706038 362536854339213856777997 := by
  unfold tailWord_706038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1609457588509523908469423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17167547610768255023673845 1609457588509523908469423)
  ·
    refine ⟨2414186382764285862704135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1609457588509523908469423 2414186382764285862704135)
    ·
      refine ⟨3621279574146428794056203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2414186382764285862704135 3621279574146428794056203)
      ·
        refine ⟨5431919361219643191084305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3621279574146428794056203 5431919361219643191084305)
        ·
          refine ⟨4073939520914732393313229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5431919361219643191084305 4073939520914732393313229)
          ·
            refine ⟨1527727320343024647492461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4073939520914732393313229 1527727320343024647492461)
            ·
              refine ⟨572897745128634242809673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1527727320343024647492461 572897745128634242809673)
              ·
                refine ⟨429673308846475682107255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572897745128634242809673 429673308846475682107255)
                ·
                  refine ⟨644509963269713523160883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429673308846475682107255 644509963269713523160883)
                  ·
                    refine ⟨966764944904570284741325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 644509963269713523160883 966764944904570284741325)
                    ·
                      refine ⟨362536854339213856777997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 966764944904570284741325 362536854339213856777997)
                      ·
                        rfl

theorem cell23_706038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_706038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706038 prefixEnd_706038 := by exact prefixLift 706038
  have htrace : WordTrace (prefixWord ++ tailWord_706038) baseStart_706038 baseEnd_706038 := by
    simpa [prefixWord, tailWord_706038, baseEnd_706038] using wordTrace_append hprefix tailTrace_706038
  have hstable : (prefixWord ++ tailWord_706038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706038).length < 2 ^ (prefixWord ++ tailWord_706038).sum := by decide
  have hdescent : baseEnd_706038 < baseStart_706038 := by decide
  rcases family_descends (prefixWord ++ tailWord_706038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706044 : List Nat := [2, 2, 2, 1, 2, 1, 5, 1, 3, 2, 2]
def baseStart_706044 : Nat := 118140960795 + 706044 * 2 ^ 59
def prefixEnd_706044 : Nat := 4983230072969 + 3 ^ 40 * 706044 * 2
def baseEnd_706044 : Nat := 362539935223140833302969

theorem tailTrace_706044 : CollatzResearch.WordTrace tailWord_706044 prefixEnd_706044 362539935223140833302969 := by
  unfold tailWord_706044
  simp only [CollatzResearch.WordTrace]
  refine ⟨12875770127065322780114593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17167693502753763706819457 12875770127065322780114593)
  ·
    refine ⟨9656827595298992085085945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12875770127065322780114593 9656827595298992085085945)
    ·
      refine ⟨7242620696474244063814459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9656827595298992085085945 7242620696474244063814459)
      ·
        refine ⟨10863931044711366095721689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7242620696474244063814459 10863931044711366095721689)
        ·
          refine ⟨8147948283533524571791267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10863931044711366095721689 8147948283533524571791267)
          ·
            refine ⟨12221922425300286857686901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8147948283533524571791267 12221922425300286857686901)
            ·
              refine ⟨1145805227371901892908147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12221922425300286857686901 1145805227371901892908147)
              ·
                refine ⟨1718707841057852839362221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1145805227371901892908147 1718707841057852839362221)
                ·
                  refine ⟨644515440396694814760833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1718707841057852839362221 644515440396694814760833)
                  ·
                    refine ⟨483386580297521111070625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 644515440396694814760833 483386580297521111070625)
                    ·
                      refine ⟨362539935223140833302969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 483386580297521111070625 362539935223140833302969)
                      ·
                        rfl

theorem cell23_706044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 3, 2, 2].length) (baseStart_706044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706044 prefixEnd_706044 := by exact prefixLift 706044
  have htrace : WordTrace (prefixWord ++ tailWord_706044) baseStart_706044 baseEnd_706044 := by
    simpa [prefixWord, tailWord_706044, baseEnd_706044] using wordTrace_append hprefix tailTrace_706044
  have hstable : (prefixWord ++ tailWord_706044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706044).length < 2 ^ (prefixWord ++ tailWord_706044).sum := by decide
  have hdescent : baseEnd_706044 < baseStart_706044 := by decide
  rcases family_descends (prefixWord ++ tailWord_706044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706053 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 1, 4, 6]
def baseStart_706053 : Nat := 118140960795 + 706053 * 2 ^ 59
def prefixEnd_706053 : Nat := 4983230072969 + 3 ^ 40 * 706053 * 2
def baseEnd_706053 : Nat := 362544556549031298090427

theorem tailTrace_706053 : CollatzResearch.WordTrace tailWord_706053 prefixEnd_706053 362544556549031298090427 := by
  unfold tailWord_706053
  simp only [CollatzResearch.WordTrace]
  refine ⟨25751868511098040097306813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17167912340732026731537875 25751868511098040097306813)
  ·
    refine ⟨9656950691661765036490055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25751868511098040097306813 9656950691661765036490055)
    ·
      refine ⟨14485426037492647554735083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9656950691661765036490055 14485426037492647554735083)
      ·
        refine ⟨21728139056238971332102625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14485426037492647554735083 21728139056238971332102625)
        ·
          refine ⟨16296104292179228499076969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21728139056238971332102625 16296104292179228499076969)
          ·
            refine ⟨12222078219134421374307727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16296104292179228499076969 12222078219134421374307727)
            ·
              refine ⟨18333117328701632061461591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12222078219134421374307727 18333117328701632061461591)
              ·
                refine ⟨27499675993052448092192387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18333117328701632061461591 27499675993052448092192387)
                ·
                  refine ⟨41249513989578672138288581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27499675993052448092192387 41249513989578672138288581)
                  ·
                    refine ⟨7734283873046001025929109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41249513989578672138288581 7734283873046001025929109)
                    ·
                      refine ⟨362544556549031298090427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7734283873046001025929109 362544556549031298090427)
                      ·
                        rfl

theorem cell23_706053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_706053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706053 prefixEnd_706053 := by exact prefixLift 706053
  have htrace : WordTrace (prefixWord ++ tailWord_706053) baseStart_706053 baseEnd_706053 := by
    simpa [prefixWord, tailWord_706053, baseEnd_706053] using wordTrace_append hprefix tailTrace_706053
  have hstable : (prefixWord ++ tailWord_706053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706053).length < 2 ^ (prefixWord ++ tailWord_706053).sum := by decide
  have hdescent : baseEnd_706053 < baseStart_706053 := by decide
  rcases family_descends (prefixWord ++ tailWord_706053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706061 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_706061 : Nat := 118140960795 + 706061 * 2 ^ 59
def prefixEnd_706061 : Nat := 4983230072969 + 3 ^ 40 * 706061 * 2
def baseEnd_706061 : Nat := 362548664394267266790391

theorem tailTrace_706061 : CollatzResearch.WordTrace tailWord_706061 prefixEnd_706061 362548664394267266790391 := by
  unfold tailWord_706061
  simp only [CollatzResearch.WordTrace]
  refine ⟨25752160295069057463598037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17168106863379371642398691 25752160295069057463598037)
  ·
    refine ⟨603566256915681034303079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 25752160295069057463598037 603566256915681034303079)
    ·
      refine ⟨905349385373521551454619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 603566256915681034303079 905349385373521551454619)
      ·
        refine ⟨1358024078060282327181929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 905349385373521551454619 1358024078060282327181929)
        ·
          refine ⟨1018518058545211745386447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1358024078060282327181929 1018518058545211745386447)
          ·
            refine ⟨1527777087817817618079671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1018518058545211745386447 1527777087817817618079671)
            ·
              refine ⟨2291665631726726427119507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1527777087817817618079671 2291665631726726427119507)
              ·
                refine ⟨3437498447590089640679261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2291665631726726427119507 3437498447590089640679261)
                ·
                  refine ⟨1289061917846283615254723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3437498447590089640679261 1289061917846283615254723)
                  ·
                    refine ⟨1933592876769425422882085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1289061917846283615254723 1933592876769425422882085)
                    ·
                      refine ⟨362548664394267266790391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1933592876769425422882085 362548664394267266790391)
                      ·
                        rfl

theorem cell23_706061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_706061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706061 prefixEnd_706061 := by exact prefixLift 706061
  have htrace : WordTrace (prefixWord ++ tailWord_706061) baseStart_706061 baseEnd_706061 := by
    simpa [prefixWord, tailWord_706061, baseEnd_706061] using wordTrace_append hprefix tailTrace_706061
  have hstable : (prefixWord ++ tailWord_706061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706061).length < 2 ^ (prefixWord ++ tailWord_706061).sum := by decide
  have hdescent : baseEnd_706061 < baseStart_706061 := by decide
  rcases family_descends (prefixWord ++ tailWord_706061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706077 : List Nat := [1, 4, 2, 2, 1, 1, 3, 2, 1, 3, 3]
def baseStart_706077 : Nat := 118140960795 + 706077 * 2 ^ 59
def prefixEnd_706077 : Nat := 4983230072969 + 3 ^ 40 * 706077 * 2
def baseEnd_706077 : Nat := 362556880084739204190317

theorem tailTrace_706077 : CollatzResearch.WordTrace tailWord_706077 prefixEnd_706077 362556880084739204190317 := by
  unfold tailWord_706077
  simp only [CollatzResearch.WordTrace]
  refine ⟨25752743863011092196180485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17168495908674061464120323 25752743863011092196180485)
  ·
    refine ⟨4828639474314579786783841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25752743863011092196180485 4828639474314579786783841)
    ·
      refine ⟨3621479605735934840087881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4828639474314579786783841 3621479605735934840087881)
      ·
        refine ⟨2716109704301951130065911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3621479605735934840087881 2716109704301951130065911)
        ·
          refine ⟨4074164556452926695098867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2716109704301951130065911 4074164556452926695098867)
          ·
            refine ⟨6111246834679390042648301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4074164556452926695098867 6111246834679390042648301)
            ·
              refine ⟨2291717563004771265993113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6111246834679390042648301 2291717563004771265993113)
              ·
                refine ⟨1718788172253578449494835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2291717563004771265993113 1718788172253578449494835)
                ·
                  refine ⟨2578182258380367674242253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1718788172253578449494835 2578182258380367674242253)
                  ·
                    refine ⟨966818346892637877840845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2578182258380367674242253 966818346892637877840845)
                    ·
                      refine ⟨362556880084739204190317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 966818346892637877840845 362556880084739204190317)
                      ·
                        rfl

theorem cell23_706077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_706077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706077 prefixEnd_706077 := by exact prefixLift 706077
  have htrace : WordTrace (prefixWord ++ tailWord_706077) baseStart_706077 baseEnd_706077 := by
    simpa [prefixWord, tailWord_706077, baseEnd_706077] using wordTrace_append hprefix tailTrace_706077
  have hstable : (prefixWord ++ tailWord_706077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706077).length < 2 ^ (prefixWord ++ tailWord_706077).sum := by decide
  have hdescent : baseEnd_706077 < baseStart_706077 := by decide
  rcases family_descends (prefixWord ++ tailWord_706077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706151 : List Nat := [1, 1, 5, 1, 1, 1, 5, 2, 2, 2, 2]
def baseStart_706151 : Nat := 118140960795 + 706151 * 2 ^ 59
def prefixEnd_706151 : Nat := 4983230072969 + 3 ^ 40 * 706151 * 2
def baseEnd_706151 : Nat := 362594877653171914664977

theorem tailTrace_706151 : CollatzResearch.WordTrace tailWord_706151 prefixEnd_706151 362594877653171914664977 := by
  unfold tailWord_706151
  simp only [CollatzResearch.WordTrace]
  refine ⟨25755442864743002834374307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17170295243162001889582871 25755442864743002834374307)
  ·
    refine ⟨38633164297114504251561461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25755442864743002834374307 38633164297114504251561461)
    ·
      refine ⟨3621859152854484773583887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38633164297114504251561461 3621859152854484773583887)
      ·
        refine ⟨5432788729281727160375831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3621859152854484773583887 5432788729281727160375831)
        ·
          refine ⟨8149183093922590740563747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5432788729281727160375831 8149183093922590740563747)
          ·
            refine ⟨12223774640883886110845621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8149183093922590740563747 12223774640883886110845621)
            ·
              refine ⟨1145978872582864322891777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12223774640883886110845621 1145978872582864322891777)
              ·
                refine ⟨859484154437148242168833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1145978872582864322891777 859484154437148242168833)
                ·
                  refine ⟨644613115827861181626625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 859484154437148242168833 644613115827861181626625)
                  ·
                    refine ⟨483459836870895886219969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 644613115827861181626625 483459836870895886219969)
                    ·
                      refine ⟨362594877653171914664977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 483459836870895886219969 362594877653171914664977)
                      ·
                        rfl

theorem cell23_706151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_706151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706151 prefixEnd_706151 := by exact prefixLift 706151
  have htrace : WordTrace (prefixWord ++ tailWord_706151) baseStart_706151 baseEnd_706151 := by
    simpa [prefixWord, tailWord_706151, baseEnd_706151] using wordTrace_append hprefix tailTrace_706151
  have hstable : (prefixWord ++ tailWord_706151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706151).length < 2 ^ (prefixWord ++ tailWord_706151).sum := by decide
  have hdescent : baseEnd_706151 < baseStart_706151 := by decide
  rcases family_descends (prefixWord ++ tailWord_706151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706170 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 6, 5]
def baseStart_706170 : Nat := 118140960795 + 706170 * 2 ^ 59
def prefixEnd_706170 : Nat := 4983230072969 + 3 ^ 40 * 706170 * 2
def baseEnd_706170 : Nat := 120868211261869113442463

theorem tailTrace_706170 : CollatzResearch.WordTrace tailWord_706170 prefixEnd_706170 120868211261869113442463 := by
  unfold tailWord_706170
  simp only [CollatzResearch.WordTrace]
  refine ⟨6439033962918542269828991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17170757234449446052877309 6439033962918542269828991)
  ·
    refine ⟨9658550944377813404743487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6439033962918542269828991 9658550944377813404743487)
    ·
      refine ⟨14487826416566720107115231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9658550944377813404743487 14487826416566720107115231)
      ·
        refine ⟨21731739624850080160672847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14487826416566720107115231 21731739624850080160672847)
        ·
          refine ⟨32597609437275120241009271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21731739624850080160672847 32597609437275120241009271)
          ·
            refine ⟨48896414155912680361513907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32597609437275120241009271 48896414155912680361513907)
            ·
              refine ⟨73344621233869020542270861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48896414155912680361513907 73344621233869020542270861)
              ·
                refine ⟨27504232962700882703351573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73344621233869020542270861 27504232962700882703351573)
                ·
                  refine ⟨1289260920126603876719605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27504232962700882703351573 1289260920126603876719605)
                  ·
                    refine ⟨120868211261869113442463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1289260920126603876719605 120868211261869113442463)
                    ·
                      rfl

theorem cell23_706170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_706170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706170 prefixEnd_706170 := by exact prefixLift 706170
  have htrace : WordTrace (prefixWord ++ tailWord_706170) baseStart_706170 baseEnd_706170 := by
    simpa [prefixWord, tailWord_706170, baseEnd_706170] using wordTrace_append hprefix tailTrace_706170
  have hstable : (prefixWord ++ tailWord_706170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706170).length < 2 ^ (prefixWord ++ tailWord_706170).sum := by decide
  have hdescent : baseEnd_706170 < baseStart_706170 := by decide
  rcases family_descends (prefixWord ++ tailWord_706170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706204 : List Nat := [2, 2, 3, 2, 3, 1, 1, 2, 2, 5]
def baseStart_706204 : Nat := 118140960795 + 706204 * 2 ^ 59
def prefixEnd_706204 : Nat := 4983230072969 + 3 ^ 40 * 706204 * 2
def baseEnd_706204 : Nat := 120874030709286735767411

theorem tailTrace_706204 : CollatzResearch.WordTrace tailWord_706204 prefixEnd_706204 120874030709286735767411 := by
  unfold tailWord_706204
  simp only [CollatzResearch.WordTrace]
  refine ⟨12878687966775496443026833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17171583955700661924035777 12878687966775496443026833)
  ·
    refine ⟨9659015975081622332270125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12878687966775496443026833 9659015975081622332270125)
    ·
      refine ⟨3622130990655608374601297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9659015975081622332270125 3622130990655608374601297)
      ·
        refine ⟨2716598242991706280950973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3622130990655608374601297 2716598242991706280950973)
        ·
          refine ⟨1018724341121889855356615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2716598242991706280950973 1018724341121889855356615)
          ·
            refine ⟨1528086511682834783034923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1018724341121889855356615 1528086511682834783034923)
            ·
              refine ⟨2292129767524252174552385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1528086511682834783034923 2292129767524252174552385)
              ·
                refine ⟨1719097325643189130914289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2292129767524252174552385 1719097325643189130914289)
                ·
                  refine ⟨1289322994232391848185717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1719097325643189130914289 1289322994232391848185717)
                  ·
                    refine ⟨120874030709286735767411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1289322994232391848185717 120874030709286735767411)
                    ·
                      rfl

theorem cell23_706204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_706204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706204 prefixEnd_706204 := by exact prefixLift 706204
  have htrace : WordTrace (prefixWord ++ tailWord_706204) baseStart_706204 baseEnd_706204 := by
    simpa [prefixWord, tailWord_706204, baseEnd_706204] using wordTrace_append hprefix tailTrace_706204
  have hstable : (prefixWord ++ tailWord_706204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706204).length < 2 ^ (prefixWord ++ tailWord_706204).sum := by decide
  have hdescent : baseEnd_706204 < baseStart_706204 := by decide
  rcases family_descends (prefixWord ++ tailWord_706204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706227 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 3]
def baseStart_706227 : Nat := 118140960795 + 706227 * 2 ^ 59
def prefixEnd_706227 : Nat := 4983230072969 + 3 ^ 40 * 706227 * 2
def baseEnd_706227 : Nat := 362633902182913617314627

theorem tailTrace_706227 : CollatzResearch.WordTrace tailWord_706227 prefixEnd_706227 362633902182913617314627 := by
  unfold tailWord_706227
  simp only [CollatzResearch.WordTrace]
  refine ⟨25758214812467667814140935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17172143208311778542760623 25758214812467667814140935)
  ·
    refine ⟨38637322218701501721211403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25758214812467667814140935 38637322218701501721211403)
    ·
      refine ⟨57955983328052252581817105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38637322218701501721211403 57955983328052252581817105)
      ·
        refine ⟨43466987496039189436362829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57955983328052252581817105 43466987496039189436362829)
        ·
          refine ⟨16300120311014696038636061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43466987496039189436362829 16300120311014696038636061)
          ·
            refine ⟨6112545116630511014488523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16300120311014696038636061 6112545116630511014488523)
            ·
              refine ⟨9168817674945766521732785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6112545116630511014488523 9168817674945766521732785)
              ·
                refine ⟨6876613256209324891299589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9168817674945766521732785 6876613256209324891299589)
                ·
                  refine ⟨1289364985539248417118673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6876613256209324891299589 1289364985539248417118673)
                  ·
                    refine ⟨967023739154436312839005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1289364985539248417118673 967023739154436312839005)
                    ·
                      refine ⟨362633902182913617314627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 967023739154436312839005 362633902182913617314627)
                      ·
                        rfl

theorem cell23_706227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 3].length) (baseStart_706227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706227 prefixEnd_706227 := by exact prefixLift 706227
  have htrace : WordTrace (prefixWord ++ tailWord_706227) baseStart_706227 baseEnd_706227 := by
    simpa [prefixWord, tailWord_706227, baseEnd_706227] using wordTrace_append hprefix tailTrace_706227
  have hstable : (prefixWord ++ tailWord_706227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706227).length < 2 ^ (prefixWord ++ tailWord_706227).sum := by decide
  have hdescent : baseEnd_706227 < baseStart_706227 := by decide
  rcases family_descends (prefixWord ++ tailWord_706227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706277 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 5, 5]
def baseStart_706277 : Nat := 118140960795 + 706277 * 2 ^ 59
def prefixEnd_706277 : Nat := 4983230072969 + 3 ^ 40 * 706277 * 2
def baseEnd_706277 : Nat := 120886525405212807229799

theorem tailTrace_706277 : CollatzResearch.WordTrace tailWord_706277 prefixEnd_706277 120886525405212807229799 := by
  unfold tailWord_706277
  simp only [CollatzResearch.WordTrace]
  refine ⟨25760038462286526353461085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17173358974857684235640723 25760038462286526353461085)
  ·
    refine ⟨9660014423357447382547907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25760038462286526353461085 9660014423357447382547907)
    ·
      refine ⟨14490021635036171073821861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9660014423357447382547907 14490021635036171073821861)
      ·
        refine ⟨2716879056569282076341599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14490021635036171073821861 2716879056569282076341599)
        ·
          refine ⟨4075318584853923114512399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2716879056569282076341599 4075318584853923114512399)
          ·
            refine ⟨6112977877280884671768599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4075318584853923114512399 6112977877280884671768599)
            ·
              refine ⟨9169466815921327007652899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6112977877280884671768599 9169466815921327007652899)
              ·
                refine ⟨13754200223881990511479349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9169466815921327007652899 13754200223881990511479349)
                ·
                  refine ⟨1289456270988936610451189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13754200223881990511479349 1289456270988936610451189)
                  ·
                    refine ⟨120886525405212807229799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1289456270988936610451189 120886525405212807229799)
                    ·
                      rfl

theorem cell23_706277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_706277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706277 prefixEnd_706277 := by exact prefixLift 706277
  have htrace : WordTrace (prefixWord ++ tailWord_706277) baseStart_706277 baseEnd_706277 := by
    simpa [prefixWord, tailWord_706277, baseEnd_706277] using wordTrace_append hprefix tailTrace_706277
  have hstable : (prefixWord ++ tailWord_706277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706277).length < 2 ^ (prefixWord ++ tailWord_706277).sum := by decide
  have hdescent : baseEnd_706277 < baseStart_706277 := by decide
  rcases family_descends (prefixWord ++ tailWord_706277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706284 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 4, 3, 2]
def baseStart_706284 : Nat := 118140960795 + 706284 * 2 ^ 59
def prefixEnd_706284 : Nat := 4983230072969 + 3 ^ 40 * 706284 * 2
def baseEnd_706284 : Nat := 362663170580219894301865

theorem tailTrace_706284 : CollatzResearch.WordTrace tailWord_706284 prefixEnd_706284 362663170580219894301865 := by
  unfold tailWord_706284
  simp only [CollatzResearch.WordTrace]
  refine ⟨12880146886630583274482953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17173529182174111032643937 12880146886630583274482953)
  ·
    refine ⟨9660110164972937455862215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12880146886630583274482953 9660110164972937455862215)
    ·
      refine ⟨14490165247459406183793323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9660110164972937455862215 14490165247459406183793323)
      ·
        refine ⟨21735247871189109275689985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14490165247459406183793323 21735247871189109275689985)
        ·
          refine ⟨16301435903391831956767489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21735247871189109275689985 16301435903391831956767489)
          ·
            refine ⟨12226076927543873967575617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16301435903391831956767489 12226076927543873967575617)
            ·
              refine ⟨9169557695657905475681713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12226076927543873967575617 9169557695657905475681713)
              ·
                refine ⟨6877168271743429106761285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9169557695657905475681713 6877168271743429106761285)
                ·
                  refine ⟨1289469050951892957517741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6877168271743429106761285 1289469050951892957517741)
                  ·
                    refine ⟨483550894106959859069153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1289469050951892957517741 483550894106959859069153)
                    ·
                      refine ⟨362663170580219894301865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 483550894106959859069153 362663170580219894301865)
                      ·
                        rfl

theorem cell23_706284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 3, 2].length) (baseStart_706284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706284 prefixEnd_706284 := by exact prefixLift 706284
  have htrace : WordTrace (prefixWord ++ tailWord_706284) baseStart_706284 baseEnd_706284 := by
    simpa [prefixWord, tailWord_706284, baseEnd_706284] using wordTrace_append hprefix tailTrace_706284
  have hstable : (prefixWord ++ tailWord_706284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706284).length < 2 ^ (prefixWord ++ tailWord_706284).sum := by decide
  have hdescent : baseEnd_706284 < baseStart_706284 := by decide
  rcases family_descends (prefixWord ++ tailWord_706284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706294 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 3, 5]
def baseStart_706294 : Nat := 118140960795 + 706294 * 2 ^ 59
def prefixEnd_706294 : Nat := 4983230072969 + 3 ^ 40 * 706294 * 2
def baseEnd_706294 : Nat := 120889435128921618392273

theorem tailTrace_706294 : CollatzResearch.WordTrace tailWord_706294 prefixEnd_706294 120889435128921618392273 := by
  unfold tailWord_706294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1610041156451558641051871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17173772335483292171219957 1610041156451558641051871)
  ·
    refine ⟨2415061734677337961577807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1610041156451558641051871 2415061734677337961577807)
    ·
      refine ⟨3622592602016006942366711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2415061734677337961577807 3622592602016006942366711)
      ·
        refine ⟨5433888903024010413550067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3622592602016006942366711 5433888903024010413550067)
        ·
          refine ⟨8150833354536015620325101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5433888903024010413550067 8150833354536015620325101)
          ·
            refine ⟨3056562507951005857621913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8150833354536015620325101 3056562507951005857621913)
            ·
              refine ⟨2292421880963254393216435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3056562507951005857621913 2292421880963254393216435)
              ·
                refine ⟨3438632821444881589824653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2292421880963254393216435 3438632821444881589824653)
                ·
                  refine ⟨1289487308041830596184245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3438632821444881589824653 1289487308041830596184245)
                  ·
                    refine ⟨120889435128921618392273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1289487308041830596184245 120889435128921618392273)
                    ·
                      rfl

theorem cell23_706294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_706294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706294 prefixEnd_706294 := by exact prefixLift 706294
  have htrace : WordTrace (prefixWord ++ tailWord_706294) baseStart_706294 baseEnd_706294 := by
    simpa [prefixWord, tailWord_706294, baseEnd_706294] using wordTrace_append hprefix tailTrace_706294
  have hstable : (prefixWord ++ tailWord_706294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706294).length < 2 ^ (prefixWord ++ tailWord_706294).sum := by decide
  have hdescent : baseEnd_706294 < baseStart_706294 := by decide
  rcases family_descends (prefixWord ++ tailWord_706294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706307 : List Nat := [1, 1, 1, 3, 2, 2, 4, 2, 1, 6]
def baseStart_706307 : Nat := 118140960795 + 706307 * 2 ^ 59
def prefixEnd_706307 : Nat := 4983230072969 + 3 ^ 40 * 706307 * 2
def baseEnd_706307 : Nat := 120891660211757768104753

theorem tailTrace_706307 : CollatzResearch.WordTrace tailWord_706307 prefixEnd_706307 120891660211757768104753 := by
  unfold tailWord_706307
  simp only [CollatzResearch.WordTrace]
  refine ⟨25761132652177841477053175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17174088434785227651368783 25761132652177841477053175)
  ·
    refine ⟨38641698978266762215579763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25761132652177841477053175 38641698978266762215579763)
    ·
      refine ⟨57962548467400143323369645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38641698978266762215579763 57962548467400143323369645)
      ·
        refine ⟨21735955675275053746263617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57962548467400143323369645 21735955675275053746263617)
        ·
          refine ⟨16301966756456290309697713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21735955675275053746263617 16301966756456290309697713)
          ·
            refine ⟨12226475067342217732273285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16301966756456290309697713 12226475067342217732273285)
            ·
              refine ⟨2292464075126665824801241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12226475067342217732273285 2292464075126665824801241)
              ·
                refine ⟨1719348056344999368600931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2292464075126665824801241 1719348056344999368600931)
                ·
                  refine ⟨2579022084517499052901397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1719348056344999368600931 2579022084517499052901397)
                  ·
                    refine ⟨120891660211757768104753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2579022084517499052901397 120891660211757768104753)
                    ·
                      rfl

theorem cell23_706307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 6].length) (baseStart_706307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706307 prefixEnd_706307 := by exact prefixLift 706307
  have htrace : WordTrace (prefixWord ++ tailWord_706307) baseStart_706307 baseEnd_706307 := by
    simpa [prefixWord, tailWord_706307, baseEnd_706307] using wordTrace_append hprefix tailTrace_706307
  have hstable : (prefixWord ++ tailWord_706307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706307).length < 2 ^ (prefixWord ++ tailWord_706307).sum := by decide
  have hdescent : baseEnd_706307 < baseStart_706307 := by decide
  rcases family_descends (prefixWord ++ tailWord_706307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706308 : List Nat := [2, 3, 2, 2, 1, 2, 1, 5, 1, 1, 3]
def baseStart_706308 : Nat := 118140960795 + 706308 * 2 ^ 59
def prefixEnd_706308 : Nat := 4983230072969 + 3 ^ 40 * 706308 * 2
def baseEnd_706308 : Nat := 362675494115927800401755

theorem tailTrace_706308 : CollatzResearch.WordTrace tailWord_706308 prefixEnd_706308 362675494115927800401755 := by
  unfold tailWord_706308
  simp only [CollatzResearch.WordTrace]
  refine ⟨12880584562587109323919789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17174112750116145765226385 12880584562587109323919789)
  ·
    refine ⟨4830219210970165996469921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12880584562587109323919789 4830219210970165996469921)
    ·
      refine ⟨3622664408227624497352441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4830219210970165996469921 3622664408227624497352441)
      ·
        refine ⟨2716998306170718373014331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3622664408227624497352441 2716998306170718373014331)
        ·
          refine ⟨4075497459256077559521497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2716998306170718373014331 4075497459256077559521497)
          ·
            refine ⟨3056623094442058169641123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4075497459256077559521497 3056623094442058169641123)
            ·
              refine ⟨4584934641663087254461685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3056623094442058169641123 4584934641663087254461685)
              ·
                refine ⟨429837622655914430105783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4584934641663087254461685 429837622655914430105783)
                ·
                  refine ⟨644756433983871645158675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429837622655914430105783 644756433983871645158675)
                  ·
                    refine ⟨967134650975807467738013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 644756433983871645158675 967134650975807467738013)
                    ·
                      refine ⟨362675494115927800401755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 967134650975807467738013 362675494115927800401755)
                      ·
                        rfl

theorem cell23_706308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_706308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706308 prefixEnd_706308 := by exact prefixLift 706308
  have htrace : WordTrace (prefixWord ++ tailWord_706308) baseStart_706308 baseEnd_706308 := by
    simpa [prefixWord, tailWord_706308, baseEnd_706308] using wordTrace_append hprefix tailTrace_706308
  have hstable : (prefixWord ++ tailWord_706308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706308).length < 2 ^ (prefixWord ++ tailWord_706308).sum := by decide
  have hdescent : baseEnd_706308 < baseStart_706308 := by decide
  rcases family_descends (prefixWord ++ tailWord_706308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706311 : List Nat := [1, 1, 4, 4, 2, 1, 1, 3, 1, 5]
def baseStart_706311 : Nat := 118140960795 + 706311 * 2 ^ 59
def prefixEnd_706311 : Nat := 4983230072969 + 3 ^ 40 * 706311 * 2
def baseEnd_706311 : Nat := 120892344852630429554747

theorem tailTrace_706311 : CollatzResearch.WordTrace tailWord_706311 prefixEnd_706311 120892344852630429554747 := by
  unfold tailWord_706311
  simp only [CollatzResearch.WordTrace]
  refine ⟨25761278544163350160198787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17174185696108900106799191 25761278544163350160198787)
  ·
    refine ⟨38641917816245025240298181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25761278544163350160198787 38641917816245025240298181)
    ·
      refine ⟨7245359590545942232555909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38641917816245025240298181 7245359590545942232555909)
      ·
        refine ⟨1358504923227364168604233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7245359590545942232555909 1358504923227364168604233)
        ·
          refine ⟨1018878692420523126453175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1358504923227364168604233 1018878692420523126453175)
          ·
            refine ⟨1528318038630784689679763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1018878692420523126453175 1528318038630784689679763)
            ·
              refine ⟨2292477057946177034519645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1528318038630784689679763 2292477057946177034519645)
              ·
                refine ⟨859678896729816387944867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2292477057946177034519645 859678896729816387944867)
                ·
                  refine ⟨1289518345094724581917301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 859678896729816387944867 1289518345094724581917301)
                  ·
                    refine ⟨120892344852630429554747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1289518345094724581917301 120892344852630429554747)
                    ·
                      rfl

theorem cell23_706311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_706311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706311 prefixEnd_706311 := by exact prefixLift 706311
  have htrace : WordTrace (prefixWord ++ tailWord_706311) baseStart_706311 baseEnd_706311 := by
    simpa [prefixWord, tailWord_706311, baseEnd_706311] using wordTrace_append hprefix tailTrace_706311
  have hstable : (prefixWord ++ tailWord_706311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706311).length < 2 ^ (prefixWord ++ tailWord_706311).sum := by decide
  have hdescent : baseEnd_706311 < baseStart_706311 := by decide
  rcases family_descends (prefixWord ++ tailWord_706311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706344 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_706344 : Nat := 118140960795 + 706344 * 2 ^ 59
def prefixEnd_706344 : Nat := 4983230072969 + 3 ^ 40 * 706344 * 2
def baseEnd_706344 : Nat := 362693979419489659551589

theorem tailTrace_706344 : CollatzResearch.WordTrace tailWord_706344 prefixEnd_706344 362693979419489659551589 := by
  unfold tailWord_706344
  simp only [CollatzResearch.WordTrace]
  refine ⟨12881241076521898398075043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17174988102029197864100057 12881241076521898398075043)
  ·
    refine ⟨19321861614782847597112565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12881241076521898398075043 19321861614782847597112565)
    ·
      refine ⟨1811424526385891962229303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19321861614782847597112565 1811424526385891962229303)
      ·
        refine ⟨2717136789578837943343955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1811424526385891962229303 2717136789578837943343955)
        ·
          refine ⟨4075705184368256915015933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2717136789578837943343955 4075705184368256915015933)
          ·
            refine ⟨1528389444138096343130975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4075705184368256915015933 1528389444138096343130975)
            ·
              refine ⟨2292584166207144514696463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1528389444138096343130975 2292584166207144514696463)
              ·
                refine ⟨3438876249310716772044695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2292584166207144514696463 3438876249310716772044695)
                ·
                  refine ⟨5158314373966075158067043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3438876249310716772044695 5158314373966075158067043)
                  ·
                    refine ⟨7737471560949112737100565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5158314373966075158067043 7737471560949112737100565)
                    ·
                      refine ⟨362693979419489659551589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7737471560949112737100565 362693979419489659551589)
                      ·
                        rfl

theorem cell23_706344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_706344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706344 prefixEnd_706344 := by exact prefixLift 706344
  have htrace : WordTrace (prefixWord ++ tailWord_706344) baseStart_706344 baseEnd_706344 := by
    simpa [prefixWord, tailWord_706344, baseEnd_706344] using wordTrace_append hprefix tailTrace_706344
  have hstable : (prefixWord ++ tailWord_706344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706344).length < 2 ^ (prefixWord ++ tailWord_706344).sum := by decide
  have hdescent : baseEnd_706344 < baseStart_706344 := by decide
  rcases family_descends (prefixWord ++ tailWord_706344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706354 : List Nat := [3, 2, 1, 1, 3, 2, 4, 7]
def baseStart_706354 : Nat := 118140960795 + 706354 * 2 ^ 59
def prefixEnd_706354 : Nat := 4983230072969 + 3 ^ 40 * 706354 * 2
def baseEnd_706354 : Nat := 13433300526890171126909

theorem tailTrace_706354 : CollatzResearch.WordTrace tailWord_706354 prefixEnd_706354 13433300526890171126909 := by
  unfold tailWord_706354
  simp only [CollatzResearch.WordTrace]
  refine ⟨6440711720751892126003529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17175231255338379002676077 6440711720751892126003529)
  ·
    refine ⟨4830533790563919094502647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6440711720751892126003529 4830533790563919094502647)
    ·
      refine ⟨7245800685845878641753971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4830533790563919094502647 7245800685845878641753971)
      ·
        refine ⟨10868701028768817962630957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7245800685845878641753971 10868701028768817962630957)
        ·
          refine ⟨4075762885788306735986609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10868701028768817962630957 4075762885788306735986609)
          ·
            refine ⟨3056822164341230051989957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4075762885788306735986609 3056822164341230051989957)
            ·
              refine ⟨573154155813980634748117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3056822164341230051989957 573154155813980634748117)
              ·
                refine ⟨13433300526890171126909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 573154155813980634748117 13433300526890171126909)
                ·
                  rfl

theorem cell23_706354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 7].length) (baseStart_706354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706354 prefixEnd_706354 := by exact prefixLift 706354
  have htrace : WordTrace (prefixWord ++ tailWord_706354) baseStart_706354 baseEnd_706354 := by
    simpa [prefixWord, tailWord_706354, baseEnd_706354] using wordTrace_append hprefix tailTrace_706354
  have hstable : (prefixWord ++ tailWord_706354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706354).length < 2 ^ (prefixWord ++ tailWord_706354).sum := by decide
  have hdescent : baseEnd_706354 < baseStart_706354 := by decide
  rcases family_descends (prefixWord ++ tailWord_706354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706364 : List Nat := [2, 2, 2, 2, 1, 1, 2, 4, 1, 3, 3]
def baseStart_706364 : Nat := 118140960795 + 706364 * 2 ^ 59
def prefixEnd_706364 : Nat := 4983230072969 + 3 ^ 40 * 706364 * 2
def baseEnd_706364 : Nat := 362704249032579581301497

theorem tailTrace_706364 : CollatzResearch.WordTrace tailWord_706364 prefixEnd_706364 362704249032579581301497 := by
  unfold tailWord_706364
  simp only [CollatzResearch.WordTrace]
  refine ⟨12881605806485670105939073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17175474408647560141252097 12881605806485670105939073)
  ·
    refine ⟨9661204354864252579454305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12881605806485670105939073 9661204354864252579454305)
    ·
      refine ⟨7245903266148189434590729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9661204354864252579454305 7245903266148189434590729)
      ·
        refine ⟨5434427449611142075943047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7245903266148189434590729 5434427449611142075943047)
        ·
          refine ⟨8151641174416713113914571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5434427449611142075943047 8151641174416713113914571)
          ·
            refine ⟨12227461761625069670871857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8151641174416713113914571 12227461761625069670871857)
            ·
              refine ⟨9170596321218802253153893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12227461761625069670871857 9170596321218802253153893)
              ·
                refine ⟨1719486810228525422466355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9170596321218802253153893 1719486810228525422466355)
                ·
                  refine ⟨2579230215342788133699533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1719486810228525422466355 2579230215342788133699533)
                  ·
                    refine ⟨967211330753545550137325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2579230215342788133699533 967211330753545550137325)
                    ·
                      refine ⟨362704249032579581301497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 967211330753545550137325 362704249032579581301497)
                      ·
                        rfl

theorem cell23_706364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_706364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706364 prefixEnd_706364 := by exact prefixLift 706364
  have htrace : WordTrace (prefixWord ++ tailWord_706364) baseStart_706364 baseEnd_706364 := by
    simpa [prefixWord, tailWord_706364, baseEnd_706364] using wordTrace_append hprefix tailTrace_706364
  have hstable : (prefixWord ++ tailWord_706364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706364).length < 2 ^ (prefixWord ++ tailWord_706364).sum := by decide
  have hdescent : baseEnd_706364 < baseStart_706364 := by decide
  rcases family_descends (prefixWord ++ tailWord_706364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706377 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 2, 2, 5]
def baseStart_706377 : Nat := 118140960795 + 706377 * 2 ^ 59
def prefixEnd_706377 : Nat := 4983230072969 + 3 ^ 40 * 706377 * 2
def baseEnd_706377 : Nat := 362710924281088030438937

theorem tailTrace_706377 : CollatzResearch.WordTrace tailWord_706377 prefixEnd_706377 362710924281088030438937 := by
  unfold tailWord_706377
  simp only [CollatzResearch.WordTrace]
  refine ⟨25763685761924243432101385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17175790507949495621400923 25763685761924243432101385)
  ·
    refine ⟨19322764321443182574076039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25763685761924243432101385 19322764321443182574076039)
    ·
      refine ⟨28984146482164773861114059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19322764321443182574076039 28984146482164773861114059)
      ·
        refine ⟨43476219723247160791671089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28984146482164773861114059 43476219723247160791671089)
        ·
          refine ⟨32607164792435370593753317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43476219723247160791671089 32607164792435370593753317)
          ·
            refine ⟨6113843398581631986328747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32607164792435370593753317 6113843398581631986328747)
            ·
              refine ⟨9170765097872447979493121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6113843398581631986328747 9170765097872447979493121)
              ·
                refine ⟨6878073823404335984619841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9170765097872447979493121 6878073823404335984619841)
                ·
                  refine ⟨5158555367553251988464881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6878073823404335984619841 5158555367553251988464881)
                  ·
                    refine ⟨3868916525664938991348661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5158555367553251988464881 3868916525664938991348661)
                    ·
                      refine ⟨362710924281088030438937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3868916525664938991348661 362710924281088030438937)
                      ·
                        rfl

theorem cell23_706377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_706377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706377 prefixEnd_706377 := by exact prefixLift 706377
  have htrace : WordTrace (prefixWord ++ tailWord_706377) baseStart_706377 baseEnd_706377 := by
    simpa [prefixWord, tailWord_706377, baseEnd_706377] using wordTrace_append hprefix tailTrace_706377
  have hstable : (prefixWord ++ tailWord_706377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706377).length < 2 ^ (prefixWord ++ tailWord_706377).sum := by decide
  have hdescent : baseEnd_706377 < baseStart_706377 := by decide
  rcases family_descends (prefixWord ++ tailWord_706377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706511 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 2, 4, 2]
def baseStart_706511 : Nat := 118140960795 + 706511 * 2 ^ 59
def prefixEnd_706511 : Nat := 4983230072969 + 3 ^ 40 * 706511 * 2
def baseEnd_706511 : Nat := 362779730688790506163321

theorem tailTrace_706511 : CollatzResearch.WordTrace tailWord_706511 prefixEnd_706511 362779730688790506163321 := by
  unfold tailWord_706511
  simp only [CollatzResearch.WordTrace]
  refine ⟨25768573143438784317479387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17179048762292522878319591 25768573143438784317479387)
  ·
    refine ⟨38652859715158176476219081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25768573143438784317479387 38652859715158176476219081)
    ·
      refine ⟨28989644786368632357164311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38652859715158176476219081 28989644786368632357164311)
      ·
        refine ⟨43484467179552948535746467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28989644786368632357164311 43484467179552948535746467)
        ·
          refine ⟨65226700769329422803619701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43484467179552948535746467 65226700769329422803619701)
          ·
            refine ⟨6115003197124633387839347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65226700769329422803619701 6115003197124633387839347)
            ·
              refine ⟨9172504795686950081759021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6115003197124633387839347 9172504795686950081759021)
              ·
                refine ⟨3439689298382606280659633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9172504795686950081759021 3439689298382606280659633)
                ·
                  refine ⟨2579766973786954710494725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3439689298382606280659633 2579766973786954710494725)
                  ·
                    refine ⟨483706307585054008217761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2579766973786954710494725 483706307585054008217761)
                    ·
                      refine ⟨362779730688790506163321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 483706307585054008217761 362779730688790506163321)
                      ·
                        rfl

theorem cell23_706511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 4, 2].length) (baseStart_706511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706511 prefixEnd_706511 := by exact prefixLift 706511
  have htrace : WordTrace (prefixWord ++ tailWord_706511) baseStart_706511 baseEnd_706511 := by
    simpa [prefixWord, tailWord_706511, baseEnd_706511] using wordTrace_append hprefix tailTrace_706511
  have hstable : (prefixWord ++ tailWord_706511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706511).length < 2 ^ (prefixWord ++ tailWord_706511).sum := by decide
  have hdescent : baseEnd_706511 < baseStart_706511 := by decide
  rcases family_descends (prefixWord ++ tailWord_706511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706531 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 3]
def baseStart_706531 : Nat := 118140960795 + 706531 * 2 ^ 59
def prefixEnd_706531 : Nat := 4983230072969 + 3 ^ 40 * 706531 * 2
def baseEnd_706531 : Nat := 362790000301880427913229

theorem tailTrace_706531 : CollatzResearch.WordTrace tailWord_706531 prefixEnd_706531 362790000301880427913229 := by
  unfold tailWord_706531
  simp only [CollatzResearch.WordTrace]
  refine ⟨25769302603366327733207447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17179535068910885155471631 25769302603366327733207447)
  ·
    refine ⟨38653953905049491599811171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25769302603366327733207447 38653953905049491599811171)
    ·
      refine ⟨57980930857574237399716757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38653953905049491599811171 57980930857574237399716757)
      ·
        refine ⟨2717856133948792378111723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 57980930857574237399716757 2717856133948792378111723)
        ·
          refine ⟨4076784200923188567167585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2717856133948792378111723 4076784200923188567167585)
          ·
            refine ⟨3057588150692391425375689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4076784200923188567167585 3057588150692391425375689)
            ·
              refine ⟨2293191113019293569031767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3057588150692391425375689 2293191113019293569031767)
              ·
                refine ⟨3439786669528940353547651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2293191113019293569031767 3439786669528940353547651)
                ·
                  refine ⟨5159680004293410530321477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3439786669528940353547651 5159680004293410530321477)
                  ·
                    refine ⟨967440000805014474435277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5159680004293410530321477 967440000805014474435277)
                    ·
                      refine ⟨362790000301880427913229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 967440000805014474435277 362790000301880427913229)
                      ·
                        rfl

theorem cell23_706531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_706531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706531 prefixEnd_706531 := by exact prefixLift 706531
  have htrace : WordTrace (prefixWord ++ tailWord_706531) baseStart_706531 baseEnd_706531 := by
    simpa [prefixWord, tailWord_706531, baseEnd_706531] using wordTrace_append hprefix tailTrace_706531
  have hstable : (prefixWord ++ tailWord_706531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706531).length < 2 ^ (prefixWord ++ tailWord_706531).sum := by decide
  have hdescent : baseEnd_706531 < baseStart_706531 := by decide
  rcases family_descends (prefixWord ++ tailWord_706531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706595 : List Nat := [1, 1, 1, 4, 3, 1, 2, 5, 1, 1, 3]
def baseStart_706595 : Nat := 118140960795 + 706595 * 2 ^ 59
def prefixEnd_706595 : Nat := 4983230072969 + 3 ^ 40 * 706595 * 2
def baseEnd_706595 : Nat := 362822863063768177512935

theorem tailTrace_706595 : CollatzResearch.WordTrace tailWord_706595 prefixEnd_706595 362822863063768177512935 := by
  unfold tailWord_706595
  simp only [CollatzResearch.WordTrace]
  refine ⟨25771636875134466663537239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17181091250089644442358159 25771636875134466663537239)
  ·
    refine ⟨38657455312701699995305859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25771636875134466663537239 38657455312701699995305859)
    ·
      refine ⟨57986182969052549992958789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38657455312701699995305859 57986182969052549992958789)
      ·
        refine ⟨10872409306697353123679773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57986182969052549992958789 10872409306697353123679773)
        ·
          refine ⟨4077153490011507421379915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10872409306697353123679773 4077153490011507421379915)
          ·
            refine ⟨6115730235017261132069873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4077153490011507421379915 6115730235017261132069873)
            ·
              refine ⟨4586797676262945849052405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6115730235017261132069873 4586797676262945849052405)
              ·
                refine ⟨430012282149651173348663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4586797676262945849052405 430012282149651173348663)
                ·
                  refine ⟨645018423224476760022995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 430012282149651173348663 645018423224476760022995)
                  ·
                    refine ⟨967527634836715140034493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 645018423224476760022995 967527634836715140034493)
                    ·
                      refine ⟨362822863063768177512935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 967527634836715140034493 362822863063768177512935)
                      ·
                        rfl

theorem cell23_706595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 1, 1, 3].length) (baseStart_706595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706595 prefixEnd_706595 := by exact prefixLift 706595
  have htrace : WordTrace (prefixWord ++ tailWord_706595) baseStart_706595 baseEnd_706595 := by
    simpa [prefixWord, tailWord_706595, baseEnd_706595] using wordTrace_append hprefix tailTrace_706595
  have hstable : (prefixWord ++ tailWord_706595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706595).length < 2 ^ (prefixWord ++ tailWord_706595).sum := by decide
  have hdescent : baseEnd_706595 < baseStart_706595 := by decide
  rcases family_descends (prefixWord ++ tailWord_706595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706601 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 6, 6, 2]
def baseStart_706601 : Nat := 118140960795 + 706601 * 2 ^ 59
def prefixEnd_706601 : Nat := 4983230072969 + 3 ^ 40 * 706601 * 2
def baseEnd_706601 : Nat := 362825943947695154037907

theorem tailTrace_706601 : CollatzResearch.WordTrace tailWord_706601 prefixEnd_706601 362825943947695154037907 := by
  unfold tailWord_706601
  simp only [CollatzResearch.WordTrace]
  refine ⟨25771855713112729688255657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17181237142075153125503771 25771855713112729688255657)
  ·
    refine ⟨19328891784834547266191743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25771855713112729688255657 19328891784834547266191743)
    ·
      refine ⟨28993337677251820899287615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19328891784834547266191743 28993337677251820899287615)
      ·
        refine ⟨43490006515877731348931423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28993337677251820899287615 43490006515877731348931423)
        ·
          refine ⟨65235009773816597023397135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43490006515877731348931423 65235009773816597023397135)
          ·
            refine ⟨97852514660724895535095703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65235009773816597023397135 97852514660724895535095703)
            ·
              refine ⟨146778771991087343302643555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97852514660724895535095703 146778771991087343302643555)
              ·
                refine ⟨220168157986631014953965333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146778771991087343302643555 220168157986631014953965333)
                ·
                  refine ⟨10320382405623328825967125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 220168157986631014953965333 10320382405623328825967125)
                  ·
                    refine ⟨483767925263593538717209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10320382405623328825967125 483767925263593538717209)
                    ·
                      refine ⟨362825943947695154037907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 483767925263593538717209 362825943947695154037907)
                      ·
                        rfl

theorem cell23_706601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 6, 2].length) (baseStart_706601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706601 prefixEnd_706601 := by exact prefixLift 706601
  have htrace : WordTrace (prefixWord ++ tailWord_706601) baseStart_706601 baseEnd_706601 := by
    simpa [prefixWord, tailWord_706601, baseEnd_706601] using wordTrace_append hprefix tailTrace_706601
  have hstable : (prefixWord ++ tailWord_706601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706601).length < 2 ^ (prefixWord ++ tailWord_706601).sum := by decide
  have hdescent : baseEnd_706601 < baseStart_706601 := by decide
  rcases family_descends (prefixWord ++ tailWord_706601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706611 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 4, 4]
def baseStart_706611 : Nat := 118140960795 + 706611 * 2 ^ 59
def prefixEnd_706611 : Nat := 4983230072969 + 3 ^ 40 * 706611 * 2
def baseEnd_706611 : Nat := 120943692918080038304287

theorem tailTrace_706611 : CollatzResearch.WordTrace tailWord_706611 prefixEnd_706611 120943692918080038304287 := by
  unfold tailWord_706611
  simp only [CollatzResearch.WordTrace]
  refine ⟨25772220443076501396119687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17181480295384334264079791 25772220443076501396119687)
  ·
    refine ⟨38658330664614752094179531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25772220443076501396119687 38658330664614752094179531)
    ·
      refine ⟨57987495996922128141269297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38658330664614752094179531 57987495996922128141269297)
      ·
        refine ⟨43490621997691596105951973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57987495996922128141269297 43490621997691596105951973)
        ·
          refine ⟨8154491624567174269865995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43490621997691596105951973 8154491624567174269865995)
          ·
            refine ⟨12231737436850761404798993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8154491624567174269865995 12231737436850761404798993)
            ·
              refine ⟨9173803077638071053599245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12231737436850761404798993 9173803077638071053599245)
              ·
                refine ⟨3440176154114276645099717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9173803077638071053599245 3440176154114276645099717)
                ·
                  refine ⟨645033028896426870956197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3440176154114276645099717 645033028896426870956197)
                  ·
                    refine ⟨120943692918080038304287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 645033028896426870956197 120943692918080038304287)
                    ·
                      rfl

theorem cell23_706611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 4].length) (baseStart_706611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706611 prefixEnd_706611 := by exact prefixLift 706611
  have htrace : WordTrace (prefixWord ++ tailWord_706611) baseStart_706611 baseEnd_706611 := by
    simpa [prefixWord, tailWord_706611, baseEnd_706611] using wordTrace_append hprefix tailTrace_706611
  have hstable : (prefixWord ++ tailWord_706611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706611).length < 2 ^ (prefixWord ++ tailWord_706611).sum := by decide
  have hdescent : baseEnd_706611 < baseStart_706611 := by decide
  rcases family_descends (prefixWord ++ tailWord_706611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706621 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 3, 1, 5]
def baseStart_706621 : Nat := 118140960795 + 706621 * 2 ^ 59
def prefixEnd_706621 : Nat := 4983230072969 + 3 ^ 40 * 706621 * 2
def baseEnd_706621 : Nat := 362836213560785075787815

theorem tailTrace_706621 : CollatzResearch.WordTrace tailWord_706621 prefixEnd_706621 362836213560785075787815 := by
  unfold tailWord_706621
  simp only [CollatzResearch.WordTrace]
  refine ⟨25772585173040273103983717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17181723448693515402655811 25772585173040273103983717)
  ·
    refine ⟨4832359719945051206996947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25772585173040273103983717 4832359719945051206996947)
    ·
      refine ⟨7248539579917576810495421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4832359719945051206996947 7248539579917576810495421)
      ·
        refine ⟨2718202342469091303935783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7248539579917576810495421 2718202342469091303935783)
        ·
          refine ⟨4077303513703636955903675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2718202342469091303935783 4077303513703636955903675)
          ·
            refine ⟨6115955270555455433855513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4077303513703636955903675 6115955270555455433855513)
            ·
              refine ⟨4586966452916591575391635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6115955270555455433855513 4586966452916591575391635)
              ·
                refine ⟨6880449679374887363087453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4586966452916591575391635 6880449679374887363087453)
                ·
                  refine ⟨2580168629765582761157795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6880449679374887363087453 2580168629765582761157795)
                  ·
                    refine ⟨3870252944648374141736693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2580168629765582761157795 3870252944648374141736693)
                    ·
                      refine ⟨362836213560785075787815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3870252944648374141736693 362836213560785075787815)
                      ·
                        rfl

theorem cell23_706621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_706621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706621 prefixEnd_706621 := by exact prefixLift 706621
  have htrace : WordTrace (prefixWord ++ tailWord_706621) baseStart_706621 baseEnd_706621 := by
    simpa [prefixWord, tailWord_706621, baseEnd_706621] using wordTrace_append hprefix tailTrace_706621
  have hstable : (prefixWord ++ tailWord_706621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706621).length < 2 ^ (prefixWord ++ tailWord_706621).sum := by decide
  have hdescent : baseEnd_706621 < baseStart_706621 := by decide
  rcases family_descends (prefixWord ++ tailWord_706621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706638 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3]
def baseStart_706638 : Nat := 118140960795 + 706638 * 2 ^ 59
def prefixEnd_706638 : Nat := 4983230072969 + 3 ^ 40 * 706638 * 2
def baseEnd_706638 : Nat := 362844942731911509275237

theorem tailTrace_706638 : CollatzResearch.WordTrace tailWord_706638 prefixEnd_706638 362844942731911509275237 := by
  unfold tailWord_706638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3221650651747335625919071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17182136809319123338235045 3221650651747335625919071)
  ·
    refine ⟨4832475977621003438878607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3221650651747335625919071 4832475977621003438878607)
    ·
      refine ⟨7248713966431505158317911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4832475977621003438878607 7248713966431505158317911)
      ·
        refine ⟨10873070949647257737476867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7248713966431505158317911 10873070949647257737476867)
        ·
          refine ⟨16309606424470886606215301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10873070949647257737476867 16309606424470886606215301)
          ·
            refine ⟨3058051204588291238665369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16309606424470886606215301 3058051204588291238665369)
            ·
              refine ⟨2293538403441218428999027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3058051204588291238665369 2293538403441218428999027)
              ·
                refine ⟨3440307605161827643498541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2293538403441218428999027 3440307605161827643498541)
                ·
                  refine ⟨1290115351935685366311953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3440307605161827643498541 1290115351935685366311953)
                  ·
                    refine ⟨967586513951764024733965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1290115351935685366311953 967586513951764024733965)
                    ·
                      refine ⟨362844942731911509275237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 967586513951764024733965 362844942731911509275237)
                      ·
                        rfl

theorem cell23_706638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_706638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706638 prefixEnd_706638 := by exact prefixLift 706638
  have htrace : WordTrace (prefixWord ++ tailWord_706638) baseStart_706638 baseEnd_706638 := by
    simpa [prefixWord, tailWord_706638, baseEnd_706638] using wordTrace_append hprefix tailTrace_706638
  have hstable : (prefixWord ++ tailWord_706638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706638).length < 2 ^ (prefixWord ++ tailWord_706638).sum := by decide
  have hdescent : baseEnd_706638 < baseStart_706638 := by decide
  rcases family_descends (prefixWord ++ tailWord_706638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706646 : List Nat := [5, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_706646 : Nat := 118140960795 + 706646 * 2 ^ 59
def prefixEnd_706646 : Nat := 4983230072969 + 3 ^ 40 * 706646 * 2
def baseEnd_706646 : Nat := 362849050577147477975201

theorem tailTrace_706646 : CollatzResearch.WordTrace tailWord_706646 prefixEnd_706646 362849050577147477975201 := by
  unfold tailWord_706646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1610843562371856398352737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17182331331966468249095861 1610843562371856398352737)
  ·
    refine ⟨1208132671778892298764553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1610843562371856398352737 1208132671778892298764553)
    ·
      refine ⟨906099503834169224073415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1208132671778892298764553 906099503834169224073415)
      ·
        refine ⟨1359149255751253836110123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 906099503834169224073415 1359149255751253836110123)
        ·
          refine ⟨2038723883626880754165185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1359149255751253836110123 2038723883626880754165185)
          ·
            refine ⟨1529042912720160565623889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2038723883626880754165185 1529042912720160565623889)
            ·
              refine ⟨1146782184540120424217917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1529042912720160565623889 1146782184540120424217917)
              ·
                refine ⟨430043319202545159081719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1146782184540120424217917 430043319202545159081719)
                ·
                  refine ⟨645064978803817738622579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 430043319202545159081719 645064978803817738622579)
                  ·
                    refine ⟨967597468205726607933869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 645064978803817738622579 967597468205726607933869)
                    ·
                      refine ⟨362849050577147477975201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 967597468205726607933869 362849050577147477975201)
                      ·
                        rfl

theorem cell23_706646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_706646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706646 prefixEnd_706646 := by exact prefixLift 706646
  have htrace : WordTrace (prefixWord ++ tailWord_706646) baseStart_706646 baseEnd_706646 := by
    simpa [prefixWord, tailWord_706646, baseEnd_706646] using wordTrace_append hprefix tailTrace_706646
  have hstable : (prefixWord ++ tailWord_706646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706646).length < 2 ^ (prefixWord ++ tailWord_706646).sum := by decide
  have hdescent : baseEnd_706646 < baseStart_706646 := by decide
  rcases family_descends (prefixWord ++ tailWord_706646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706652 : List Nat := [2, 2, 4, 1, 1, 4, 2, 1, 1, 1, 4]
def baseStart_706652 : Nat := 118140960795 + 706652 * 2 ^ 59
def prefixEnd_706652 : Nat := 4983230072969 + 3 ^ 40 * 706652 * 2
def baseEnd_706652 : Nat := 362852131461074454500173

theorem tailTrace_706652 : CollatzResearch.WordTrace tailWord_706652 prefixEnd_706652 362852131461074454500173 := by
  unfold tailWord_706652
  simp only [CollatzResearch.WordTrace]
  refine ⟨12886857917963982699181105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17182477223951976932241473 12886857917963982699181105)
  ·
    refine ⟨9665143438472987024385829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12886857917963982699181105 9665143438472987024385829)
    ·
      refine ⟨1812214394713685067072343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9665143438472987024385829 1812214394713685067072343)
      ·
        refine ⟨2718321592070527600608515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1812214394713685067072343 2718321592070527600608515)
        ·
          refine ⟨4077482388105791400912773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2718321592070527600608515 4077482388105791400912773)
          ·
            refine ⟨764527947769835887671145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4077482388105791400912773 764527947769835887671145)
            ·
              refine ⟨573395960827376915753359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 764527947769835887671145 573395960827376915753359)
              ·
                refine ⟨860093941241065373630039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573395960827376915753359 860093941241065373630039)
                ·
                  refine ⟨1290140911861598060445059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 860093941241065373630039 1290140911861598060445059)
                  ·
                    refine ⟨1935211367792397090667589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1290140911861598060445059 1935211367792397090667589)
                    ·
                      refine ⟨362852131461074454500173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1935211367792397090667589 362852131461074454500173)
                      ·
                        rfl

theorem cell23_706652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_706652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706652 prefixEnd_706652 := by exact prefixLift 706652
  have htrace : WordTrace (prefixWord ++ tailWord_706652) baseStart_706652 baseEnd_706652 := by
    simpa [prefixWord, tailWord_706652, baseEnd_706652] using wordTrace_append hprefix tailTrace_706652
  have hstable : (prefixWord ++ tailWord_706652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706652).length < 2 ^ (prefixWord ++ tailWord_706652).sum := by decide
  have hdescent : baseEnd_706652 < baseStart_706652 := by decide
  rcases family_descends (prefixWord ++ tailWord_706652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706658 : List Nat := [3, 3, 2, 2, 2, 1, 10]
def baseStart_706658 : Nat := 118140960795 + 706658 * 2 ^ 59
def prefixEnd_706658 : Nat := 4983230072969 + 3 ^ 40 * 706658 * 2
def baseEnd_706658 : Nat := 4479693979567918901545

theorem tailTrace_706658 : CollatzResearch.WordTrace tailWord_706658 prefixEnd_706658 4479693979567918901545 := by
  unfold tailWord_706658
  simp only [CollatzResearch.WordTrace]
  refine ⟨6443483668476557105770157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17182623115937485615387085 6443483668476557105770157)
  ·
    refine ⟨2416306375678708914663809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6443483668476557105770157 2416306375678708914663809)
    ·
      refine ⟨1812229781759031685997857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2416306375678708914663809 1812229781759031685997857)
      ·
        refine ⟨1359172336319273764498393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1812229781759031685997857 1359172336319273764498393)
        ·
          refine ⟨1019379252239455323373795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1359172336319273764498393 1019379252239455323373795)
          ·
            refine ⟨1529068878359182985060693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019379252239455323373795 1529068878359182985060693)
            ·
              refine ⟨4479693979567918901545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1529068878359182985060693 4479693979567918901545)
              ·
                rfl

theorem cell23_706658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 10].length) (baseStart_706658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706658 prefixEnd_706658 := by exact prefixLift 706658
  have htrace : WordTrace (prefixWord ++ tailWord_706658) baseStart_706658 baseEnd_706658 := by
    simpa [prefixWord, tailWord_706658, baseEnd_706658] using wordTrace_append hprefix tailTrace_706658
  have hstable : (prefixWord ++ tailWord_706658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706658).length < 2 ^ (prefixWord ++ tailWord_706658).sum := by decide
  have hdescent : baseEnd_706658 < baseStart_706658 := by decide
  rcases family_descends (prefixWord ++ tailWord_706658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706685 : List Nat := [1, 4, 1, 1, 3, 4, 1, 1, 1, 3, 3]
def baseStart_706685 : Nat := 118140960795 + 706685 * 2 ^ 59
def prefixEnd_706685 : Nat := 4983230072969 + 3 ^ 40 * 706685 * 2
def baseEnd_706685 : Nat := 362869076322672825387521

theorem tailTrace_706685 : CollatzResearch.WordTrace tailWord_706685 prefixEnd_706685 362869076322672825387521 := by
  unfold tailWord_706685
  simp only [CollatzResearch.WordTrace]
  refine ⟨25774919444808412034313509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17183279629872274689542339 25774919444808412034313509)
  ·
    refine ⟨4832797395901577256433783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25774919444808412034313509 4832797395901577256433783)
    ·
      refine ⟨7249196093852365884650675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4832797395901577256433783 7249196093852365884650675)
      ·
        refine ⟨10873794140778548826976013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7249196093852365884650675 10873794140778548826976013)
        ·
          refine ⟨4077672802791955810116005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10873794140778548826976013 4077672802791955810116005)
          ·
            refine ⟨764563650523491714396751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4077672802791955810116005 764563650523491714396751)
            ·
              refine ⟨1146845475785237571595127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 764563650523491714396751 1146845475785237571595127)
              ·
                refine ⟨1720268213677856357392691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1146845475785237571595127 1720268213677856357392691)
                ·
                  refine ⟨2580402320516784536089037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1720268213677856357392691 2580402320516784536089037)
                  ·
                    refine ⟨967650870193794201033389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2580402320516784536089037 967650870193794201033389)
                    ·
                      refine ⟨362869076322672825387521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 967650870193794201033389 362869076322672825387521)
                      ·
                        rfl

theorem cell23_706685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_706685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706685 prefixEnd_706685 := by exact prefixLift 706685
  have htrace : WordTrace (prefixWord ++ tailWord_706685) baseStart_706685 baseEnd_706685 := by
    simpa [prefixWord, tailWord_706685, baseEnd_706685] using wordTrace_append hprefix tailTrace_706685
  have hstable : (prefixWord ++ tailWord_706685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706685).length < 2 ^ (prefixWord ++ tailWord_706685).sum := by decide
  have hdescent : baseEnd_706685 < baseStart_706685 := by decide
  rcases family_descends (prefixWord ++ tailWord_706685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706695 : List Nat := [1, 1, 4, 2, 1, 1, 3, 4, 1, 3, 2]
def baseStart_706695 : Nat := 118140960795 + 706695 * 2 ^ 59
def prefixEnd_706695 : Nat := 4983230072969 + 3 ^ 40 * 706695 * 2
def baseEnd_706695 : Nat := 362874211129217786262475

theorem tailTrace_706695 : CollatzResearch.WordTrace tailWord_706695 prefixEnd_706695 362874211129217786262475 := by
  unfold tailWord_706695
  simp only [CollatzResearch.WordTrace]
  refine ⟨25775284174772183742177539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17183522783181455828118359 25775284174772183742177539)
  ·
    refine ⟨38662926262158275613266309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25775284174772183742177539 38662926262158275613266309)
    ·
      refine ⟨7249298674154676677487433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38662926262158275613266309 7249298674154676677487433)
      ·
        refine ⟨5436974005616007508115575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7249298674154676677487433 5436974005616007508115575)
        ·
          refine ⟨8155461008424011262173363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5436974005616007508115575 8155461008424011262173363)
          ·
            refine ⟨12233191512636016893260045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8155461008424011262173363 12233191512636016893260045)
            ·
              refine ⟨4587446817238506334972517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12233191512636016893260045 4587446817238506334972517)
              ·
                refine ⟨860146278232219937807347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4587446817238506334972517 860146278232219937807347)
                ·
                  refine ⟨1290219417348329906711021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 860146278232219937807347 1290219417348329906711021)
                  ·
                    refine ⟨483832281505623715016633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1290219417348329906711021 483832281505623715016633)
                    ·
                      refine ⟨362874211129217786262475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 483832281505623715016633 362874211129217786262475)
                      ·
                        rfl

theorem cell23_706695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_706695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706695 prefixEnd_706695 := by exact prefixLift 706695
  have htrace : WordTrace (prefixWord ++ tailWord_706695) baseStart_706695 baseEnd_706695 := by
    simpa [prefixWord, tailWord_706695, baseEnd_706695] using wordTrace_append hprefix tailTrace_706695
  have hstable : (prefixWord ++ tailWord_706695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706695).length < 2 ^ (prefixWord ++ tailWord_706695).sum := by decide
  have hdescent : baseEnd_706695 < baseStart_706695 := by decide
  rcases family_descends (prefixWord ++ tailWord_706695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706725 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 4, 2, 2]
def baseStart_706725 : Nat := 118140960795 + 706725 * 2 ^ 59
def prefixEnd_706725 : Nat := 4983230072969 + 3 ^ 40 * 706725 * 2
def baseEnd_706725 : Nat := 362889615548852668887337

theorem tailTrace_706725 : CollatzResearch.WordTrace tailWord_706725 prefixEnd_706725 362889615548852668887337 := by
  unfold tailWord_706725
  simp only [CollatzResearch.WordTrace]
  refine ⟨25776378364663498865769629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17184252243108999243846419 25776378364663498865769629)
  ·
    refine ⟨9666141886748812074663611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25776378364663498865769629 9666141886748812074663611)
    ·
      refine ⟨14499212830123218111995417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9666141886748812074663611 14499212830123218111995417)
      ·
        refine ⟨10874409622592413583996563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14499212830123218111995417 10874409622592413583996563)
        ·
          refine ⟨16311614433888620375994845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10874409622592413583996563 16311614433888620375994845)
          ·
            refine ⟨6116855412708232640998067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16311614433888620375994845 6116855412708232640998067)
            ·
              refine ⟨9175283119062348961497101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6116855412708232640998067 9175283119062348961497101)
              ·
                refine ⟨3440731169648380860561413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9175283119062348961497101 3440731169648380860561413)
                ·
                  refine ⟨645137094309071411355265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3440731169648380860561413 645137094309071411355265)
                  ·
                    refine ⟨483852820731803558516449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 645137094309071411355265 483852820731803558516449)
                    ·
                      refine ⟨362889615548852668887337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 483852820731803558516449 362889615548852668887337)
                      ·
                        rfl

theorem cell23_706725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 2, 2].length) (baseStart_706725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706725 prefixEnd_706725 := by exact prefixLift 706725
  have htrace : WordTrace (prefixWord ++ tailWord_706725) baseStart_706725 baseEnd_706725 := by
    simpa [prefixWord, tailWord_706725, baseEnd_706725] using wordTrace_append hprefix tailTrace_706725
  have hstable : (prefixWord ++ tailWord_706725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706725).length < 2 ^ (prefixWord ++ tailWord_706725).sum := by decide
  have hdescent : baseEnd_706725 < baseStart_706725 := by decide
  rcases family_descends (prefixWord ++ tailWord_706725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706768 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 6, 5, 2]
def baseStart_706768 : Nat := 118140960795 + 706768 * 2 ^ 59
def prefixEnd_706768 : Nat := 4983230072969 + 3 ^ 40 * 706768 * 2
def baseEnd_706768 : Nat := 362911695216996000649639

theorem tailTrace_706768 : CollatzResearch.WordTrace tailWord_706768 prefixEnd_706768 362911695216996000649639 := by
  unfold tailWord_706768
  simp only [CollatzResearch.WordTrace]
  refine ⟨12888973351753858604792479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17185297802338478139723305 12888973351753858604792479)
  ·
    refine ⟨19333460027630787907188719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12888973351753858604792479 19333460027630787907188719)
    ·
      refine ⟨29000190041446181860783079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19333460027630787907188719 29000190041446181860783079)
      ·
        refine ⟨43500285062169272791174619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29000190041446181860783079 43500285062169272791174619)
        ·
          refine ⟨65250427593253909186761929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43500285062169272791174619 65250427593253909186761929)
          ·
            refine ⟨48937820694940431890071447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65250427593253909186761929 48937820694940431890071447)
            ·
              refine ⟨73406731042410647835107171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48937820694940431890071447 73406731042410647835107171)
              ·
                refine ⟨110110096563615971752660757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73406731042410647835107171 110110096563615971752660757)
                ·
                  refine ⟨5161410776419498675905973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110110096563615971752660757 5161410776419498675905973)
                  ·
                    refine ⟨483882260289328000866185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5161410776419498675905973 483882260289328000866185)
                    ·
                      refine ⟨362911695216996000649639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 483882260289328000866185 362911695216996000649639)
                      ·
                        rfl

theorem cell23_706768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 6, 5, 2].length) (baseStart_706768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706768 prefixEnd_706768 := by exact prefixLift 706768
  have htrace : WordTrace (prefixWord ++ tailWord_706768) baseStart_706768 baseEnd_706768 := by
    simpa [prefixWord, tailWord_706768, baseEnd_706768] using wordTrace_append hprefix tailTrace_706768
  have hstable : (prefixWord ++ tailWord_706768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706768).length < 2 ^ (prefixWord ++ tailWord_706768).sum := by decide
  have hdescent : baseEnd_706768 < baseStart_706768 := by decide
  rcases family_descends (prefixWord ++ tailWord_706768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706778 : List Nat := [3, 1, 1, 2, 2, 1, 4, 2, 2, 5]
def baseStart_706778 : Nat := 118140960795 + 706778 * 2 ^ 59
def prefixEnd_706778 : Nat := 4983230072969 + 3 ^ 40 * 706778 * 2
def baseEnd_706778 : Nat := 120972276674513653841531

theorem tailTrace_706778 : CollatzResearch.WordTrace tailWord_706778 prefixEnd_706778 120972276674513653841531 := by
  unfold tailWord_706778
  simp only [CollatzResearch.WordTrace]
  refine ⟨6444577858367872229362247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17185540955647659278299325 6444577858367872229362247)
  ·
    refine ⟨9666866787551808344043371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6444577858367872229362247 9666866787551808344043371)
    ·
      refine ⟨14500300181327712516065057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9666866787551808344043371 14500300181327712516065057)
      ·
        refine ⟨10875225135995784387048793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14500300181327712516065057 10875225135995784387048793)
        ·
          refine ⟨8156418851996838290286595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10875225135995784387048793 8156418851996838290286595)
          ·
            refine ⟨12234628277995257435429893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8156418851996838290286595 12234628277995257435429893)
            ·
              refine ⟨2293992802124110769143105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12234628277995257435429893 2293992802124110769143105)
              ·
                refine ⟨1720494601593083076857329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2293992802124110769143105 1720494601593083076857329)
                ·
                  refine ⟨1290370951194812307642997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1720494601593083076857329 1290370951194812307642997)
                  ·
                    refine ⟨120972276674513653841531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1290370951194812307642997 120972276674513653841531)
                    ·
                      rfl

theorem cell23_706778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_706778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706778 prefixEnd_706778 := by exact prefixLift 706778
  have htrace : WordTrace (prefixWord ++ tailWord_706778) baseStart_706778 baseEnd_706778 := by
    simpa [prefixWord, tailWord_706778, baseEnd_706778] using wordTrace_append hprefix tailTrace_706778
  have hstable : (prefixWord ++ tailWord_706778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706778).length < 2 ^ (prefixWord ++ tailWord_706778).sum := by decide
  have hdescent : baseEnd_706778 < baseStart_706778 := by decide
  rcases family_descends (prefixWord ++ tailWord_706778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706798 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_706798 : Nat := 118140960795 + 706798 * 2 ^ 59
def prefixEnd_706798 : Nat := 4983230072969 + 3 ^ 40 * 706798 * 2
def baseEnd_706798 : Nat := 362927099636630883274501

theorem tailTrace_706798 : CollatzResearch.WordTrace tailWord_706798 prefixEnd_706798 362927099636630883274501 := by
  unfold tailWord_706798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3222380111674879041647131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17186027262266021555451365 3222380111674879041647131)
  ·
    refine ⟨4833570167512318562470697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3222380111674879041647131 4833570167512318562470697)
    ·
      refine ⟨3625177625634238921853023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4833570167512318562470697 3625177625634238921853023)
      ·
        refine ⟨5437766438451358382779535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3625177625634238921853023 5437766438451358382779535)
        ·
          refine ⟨8156649657677037574169303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5437766438451358382779535 8156649657677037574169303)
          ·
            refine ⟨12234974486515556361253955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8156649657677037574169303 12234974486515556361253955)
            ·
              refine ⟨18352461729773334541880933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12234974486515556361253955 18352461729773334541880933)
              ·
                refine ⟨3441086574332500226602675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18352461729773334541880933 3441086574332500226602675)
                ·
                  refine ⟨5161629861498750339904013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3441086574332500226602675 5161629861498750339904013)
                  ·
                    refine ⟨1935611198062031377464005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5161629861498750339904013 1935611198062031377464005)
                    ·
                      refine ⟨362927099636630883274501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1935611198062031377464005 362927099636630883274501)
                      ·
                        rfl

theorem cell23_706798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_706798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706798 prefixEnd_706798 := by exact prefixLift 706798
  have htrace : WordTrace (prefixWord ++ tailWord_706798) baseStart_706798 baseEnd_706798 := by
    simpa [prefixWord, tailWord_706798, baseEnd_706798] using wordTrace_append hprefix tailTrace_706798
  have hstable : (prefixWord ++ tailWord_706798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706798).length < 2 ^ (prefixWord ++ tailWord_706798).sum := by decide
  have hdescent : baseEnd_706798 < baseStart_706798 := by decide
  rcases family_descends (prefixWord ++ tailWord_706798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706811 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 6]
def baseStart_706811 : Nat := 118140960795 + 706811 * 2 ^ 59
def prefixEnd_706811 : Nat := 4983230072969 + 3 ^ 40 * 706811 * 2
def baseEnd_706811 : Nat := 362933774885139332411941

theorem tailTrace_706811 : CollatzResearch.WordTrace tailWord_706811 prefixEnd_706811 362933774885139332411941 := by
  unfold tailWord_706811
  simp only [CollatzResearch.WordTrace]
  refine ⟨25779515042351935553400287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17186343361567957035600191 25779515042351935553400287)
  ·
    refine ⟨38669272563527903330100431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25779515042351935553400287 38669272563527903330100431)
    ·
      refine ⟨58003908845291854995150647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38669272563527903330100431 58003908845291854995150647)
      ·
        refine ⟨87005863267937782492725971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58003908845291854995150647 87005863267937782492725971)
        ·
          refine ⟨130508794901906673739088957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87005863267937782492725971 130508794901906673739088957)
          ·
            refine ⟨48940798088215002652158359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130508794901906673739088957 48940798088215002652158359)
            ·
              refine ⟨73411197132322503978237539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48940798088215002652158359 73411197132322503978237539)
              ·
                refine ⟨110116795698483755967356309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73411197132322503978237539 110116795698483755967356309)
                ·
                  refine ⟨5161724798366426060969827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110116795698483755967356309 5161724798366426060969827)
                  ·
                    refine ⟨7742587197549639091454741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5161724798366426060969827 7742587197549639091454741)
                    ·
                      refine ⟨362933774885139332411941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7742587197549639091454741 362933774885139332411941)
                      ·
                        rfl

theorem cell23_706811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 6].length) (baseStart_706811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706811 prefixEnd_706811 := by exact prefixLift 706811
  have htrace : WordTrace (prefixWord ++ tailWord_706811) baseStart_706811 baseEnd_706811 := by
    simpa [prefixWord, tailWord_706811, baseEnd_706811] using wordTrace_append hprefix tailTrace_706811
  have hstable : (prefixWord ++ tailWord_706811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706811).length < 2 ^ (prefixWord ++ tailWord_706811).sum := by decide
  have hdescent : baseEnd_706811 < baseStart_706811 := by decide
  rcases family_descends (prefixWord ++ tailWord_706811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706842 : List Nat := [3, 1, 1, 3, 4, 1, 2, 1, 3, 4]
def baseStart_706842 : Nat := 118140960795 + 706842 * 2 ^ 59
def prefixEnd_706842 : Nat := 4983230072969 + 3 ^ 40 * 706842 * 2
def baseEnd_706842 : Nat := 120983230928476237041433

theorem tailTrace_706842 : CollatzResearch.WordTrace tailWord_706842 prefixEnd_706842 120983230928476237041433 := by
  unfold tailWord_706842
  simp only [CollatzResearch.WordTrace]
  refine ⟨6445161426309906961944695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17187097136826418565185853 6445161426309906961944695)
  ·
    refine ⟨9667742139464860442917043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6445161426309906961944695 9667742139464860442917043)
    ·
      refine ⟨14501613209197290664375565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9667742139464860442917043 14501613209197290664375565)
      ·
        refine ⟨5438104953448983999140837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14501613209197290664375565 5438104953448983999140837)
        ·
          refine ⟨1019644678771684499838907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5438104953448983999140837 1019644678771684499838907)
          ·
            refine ⟨1529467018157526749758361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019644678771684499838907 1529467018157526749758361)
            ·
              refine ⟨1147100263618145062318771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1529467018157526749758361 1147100263618145062318771)
              ·
                refine ⟨1720650395427217593478157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1147100263618145062318771 1720650395427217593478157)
                ·
                  refine ⟨645243898285206597554309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1720650395427217593478157 645243898285206597554309)
                  ·
                    refine ⟨120983230928476237041433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 645243898285206597554309 120983230928476237041433)
                    ·
                      rfl

theorem cell23_706842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 3, 4].length) (baseStart_706842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706842 prefixEnd_706842 := by exact prefixLift 706842
  have htrace : WordTrace (prefixWord ++ tailWord_706842) baseStart_706842 baseEnd_706842 := by
    simpa [prefixWord, tailWord_706842, baseEnd_706842] using wordTrace_append hprefix tailTrace_706842
  have hstable : (prefixWord ++ tailWord_706842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706842).length < 2 ^ (prefixWord ++ tailWord_706842).sum := by decide
  have hdescent : baseEnd_706842 < baseStart_706842 := by decide
  rcases family_descends (prefixWord ++ tailWord_706842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706892 : List Nat := [2, 2, 1, 3, 2, 1, 3, 2, 2, 3, 2]
def baseStart_706892 : Nat := 118140960795 + 706892 * 2 ^ 59
def prefixEnd_706892 : Nat := 4983230072969 + 3 ^ 40 * 706892 * 2
def baseEnd_706892 : Nat := 362975366818153515499069

theorem tailTrace_706892 : CollatzResearch.WordTrace tailWord_706892 prefixEnd_706892 362975366818153515499069 := by
  unfold tailWord_706892
  simp only [CollatzResearch.WordTrace]
  refine ⟨12891234677529243193549465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17188312903372324258065953 12891234677529243193549465)
  ·
    refine ⟨9668426008146932395162099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12891234677529243193549465 9668426008146932395162099)
    ·
      refine ⟨14502639012220398592743149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9668426008146932395162099 14502639012220398592743149)
      ·
        refine ⟨5438489629582649472278681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14502639012220398592743149 5438489629582649472278681)
        ·
          refine ⟨4078867222186987104209011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5438489629582649472278681 4078867222186987104209011)
          ·
            refine ⟨6118300833280480656313517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4078867222186987104209011 6118300833280480656313517)
            ·
              refine ⟨2294362812480180246117569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6118300833280480656313517 2294362812480180246117569)
              ·
                refine ⟨1720772109360135184588177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2294362812480180246117569 1720772109360135184588177)
                ·
                  refine ⟨1290579082020101388441133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1720772109360135184588177 1290579082020101388441133)
                  ·
                    refine ⟨483967155757538020665425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1290579082020101388441133 483967155757538020665425)
                    ·
                      refine ⟨362975366818153515499069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 483967155757538020665425 362975366818153515499069)
                      ·
                        rfl

theorem cell23_706892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_706892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706892 prefixEnd_706892 := by exact prefixLift 706892
  have htrace : WordTrace (prefixWord ++ tailWord_706892) baseStart_706892 baseEnd_706892 := by
    simpa [prefixWord, tailWord_706892, baseEnd_706892] using wordTrace_append hprefix tailTrace_706892
  have hstable : (prefixWord ++ tailWord_706892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706892).length < 2 ^ (prefixWord ++ tailWord_706892).sum := by decide
  have hdescent : baseEnd_706892 < baseStart_706892 := by decide
  rcases family_descends (prefixWord ++ tailWord_706892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706922 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_706922 : Nat := 118140960795 + 706922 * 2 ^ 59
def prefixEnd_706922 : Nat := 4983230072969 + 3 ^ 40 * 706922 * 2
def baseEnd_706922 : Nat := 362990771237788398123931

theorem tailTrace_706922 : CollatzResearch.WordTrace tailWord_706922 prefixEnd_706922 362990771237788398123931 := by
  unfold tailWord_706922
  simp only [CollatzResearch.WordTrace]
  refine ⟨6445890886237450377672755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17189042363299867673794013 6445890886237450377672755)
  ·
    refine ⟨9668836329356175566509133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6445890886237450377672755 9668836329356175566509133)
    ·
      refine ⟨3625813623508565837440925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9668836329356175566509133 3625813623508565837440925)
      ·
        refine ⟨1359680108815712189040347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3625813623508565837440925 1359680108815712189040347)
        ·
          refine ⟨2039520163223568283560521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1359680108815712189040347 2039520163223568283560521)
          ·
            refine ⟨1529640122417676212670391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2039520163223568283560521 1529640122417676212670391)
            ·
              refine ⟨2294460183626514319005587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529640122417676212670391 2294460183626514319005587)
              ·
                refine ⟨3441690275439771478508381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2294460183626514319005587 3441690275439771478508381)
                ·
                  refine ⟨1290633853289914304440643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3441690275439771478508381 1290633853289914304440643)
                  ·
                    refine ⟨1935950779934871456660965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1290633853289914304440643 1935950779934871456660965)
                    ·
                      refine ⟨362990771237788398123931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1935950779934871456660965 362990771237788398123931)
                      ·
                        rfl

theorem cell23_706922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_706922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706922 prefixEnd_706922 := by exact prefixLift 706922
  have htrace : WordTrace (prefixWord ++ tailWord_706922) baseStart_706922 baseEnd_706922 := by
    simpa [prefixWord, tailWord_706922, baseEnd_706922] using wordTrace_append hprefix tailTrace_706922
  have hstable : (prefixWord ++ tailWord_706922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706922).length < 2 ^ (prefixWord ++ tailWord_706922).sum := by decide
  have hdescent : baseEnd_706922 < baseStart_706922 := by decide
  rcases family_descends (prefixWord ++ tailWord_706922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706928 : List Nat := [2, 1, 1, 1, 4, 3, 2, 9]
def baseStart_706928 : Nat := 118140960795 + 706928 * 2 ^ 59
def prefixEnd_706928 : Nat := 4983230072969 + 3 ^ 40 * 706928 * 2
def baseEnd_706928 : Nat := 13444216745248717579589

theorem tailTrace_706928 : CollatzResearch.WordTrace tailWord_706928 prefixEnd_706928 13444216745248717579589 := by
  unfold tailWord_706928
  simp only [CollatzResearch.WordTrace]
  refine ⟨12891891191464032267704719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17189188255285376356939625 12891891191464032267704719)
  ·
    refine ⟨19337836787196048401557079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12891891191464032267704719 19337836787196048401557079)
    ·
      refine ⟨29006755180794072602335619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19337836787196048401557079 29006755180794072602335619)
      ·
        refine ⟨43510132771191108903503429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29006755180794072602335619 43510132771191108903503429)
        ·
          refine ⟨8158149894598332919406893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43510132771191108903503429 8158149894598332919406893)
          ·
            refine ⟨3059306210474374844777585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8158149894598332919406893 3059306210474374844777585)
            ·
              refine ⟨2294479657855781133583189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3059306210474374844777585 2294479657855781133583189)
              ·
                refine ⟨13444216745248717579589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2294479657855781133583189 13444216745248717579589)
                ·
                  rfl

theorem cell23_706928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 9].length) (baseStart_706928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706928 prefixEnd_706928 := by exact prefixLift 706928
  have htrace : WordTrace (prefixWord ++ tailWord_706928) baseStart_706928 baseEnd_706928 := by
    simpa [prefixWord, tailWord_706928, baseEnd_706928] using wordTrace_append hprefix tailTrace_706928
  have hstable : (prefixWord ++ tailWord_706928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706928).length < 2 ^ (prefixWord ++ tailWord_706928).sum := by decide
  have hdescent : baseEnd_706928 < baseStart_706928 := by decide
  rcases family_descends (prefixWord ++ tailWord_706928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706956 : List Nat := [2, 2, 1, 2, 1, 5, 1, 4, 1, 2, 2]
def baseStart_706956 : Nat := 118140960795 + 706956 * 2 ^ 59
def prefixEnd_706956 : Nat := 4983230072969 + 3 ^ 40 * 706956 * 2
def baseEnd_706956 : Nat := 363008229580041265098775

theorem tailTrace_706956 : CollatzResearch.WordTrace tailWord_706956 prefixEnd_706956 363008229580041265098775 := by
  unfold tailWord_706956
  simp only [CollatzResearch.WordTrace]
  refine ⟨12892401813413312658714361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17189869084551083544952481 12892401813413312658714361)
  ·
    refine ⟨9669301360059984494035771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12892401813413312658714361 9669301360059984494035771)
    ·
      refine ⟨14503952040089976741053657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9669301360059984494035771 14503952040089976741053657)
      ·
        refine ⟨10877964030067482555790243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14503952040089976741053657 10877964030067482555790243)
        ·
          refine ⟨16316946045101223833685365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10877964030067482555790243 16316946045101223833685365)
          ·
            refine ⟨1529713691728239734408003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16316946045101223833685365 1529713691728239734408003)
            ·
              refine ⟨2294570537592359601612005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529713691728239734408003 2294570537592359601612005)
              ·
                refine ⟨430231975798567425302251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2294570537592359601612005 430231975798567425302251)
                ·
                  refine ⟨645347963697851137953377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 430231975798567425302251 645347963697851137953377)
                  ·
                    refine ⟨484010972773388353465033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 645347963697851137953377 484010972773388353465033)
                    ·
                      refine ⟨363008229580041265098775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 484010972773388353465033 363008229580041265098775)
                      ·
                        rfl

theorem cell23_706956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 1, 2, 2].length) (baseStart_706956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706956 prefixEnd_706956 := by exact prefixLift 706956
  have htrace : WordTrace (prefixWord ++ tailWord_706956) baseStart_706956 baseEnd_706956 := by
    simpa [prefixWord, tailWord_706956, baseEnd_706956] using wordTrace_append hprefix tailTrace_706956
  have hstable : (prefixWord ++ tailWord_706956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706956).length < 2 ^ (prefixWord ++ tailWord_706956).sum := by decide
  have hdescent : baseEnd_706956 < baseStart_706956 := by decide
  rcases family_descends (prefixWord ++ tailWord_706956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706988 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 3, 8]
def baseStart_706988 : Nat := 118140960795 + 706988 * 2 ^ 59
def prefixEnd_706988 : Nat := 4983230072969 + 3 ^ 40 * 706988 * 2
def baseEnd_706988 : Nat := 121008220320328379966209

theorem tailTrace_706988 : CollatzResearch.WordTrace tailWord_706988 prefixEnd_706988 121008220320328379966209 := by
  unfold tailWord_706988
  simp only [CollatzResearch.WordTrace]
  refine ⟨12892985381355347391296809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17190647175140463188395745 12892985381355347391296809)
  ·
    refine ⟨9669739036016510543472607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12892985381355347391296809 9669739036016510543472607)
    ·
      refine ⟨14504608554024765815208911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9669739036016510543472607 14504608554024765815208911)
      ·
        refine ⟨21756912831037148722813367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14504608554024765815208911 21756912831037148722813367)
        ·
          refine ⟨32635369246555723084220051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21756912831037148722813367 32635369246555723084220051)
          ·
            refine ⟨48953053869833584626330077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32635369246555723084220051 48953053869833584626330077)
            ·
              refine ⟨18357395201187594234873779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48953053869833584626330077 18357395201187594234873779)
              ·
                refine ⟨27536092801781391352310669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18357395201187594234873779 27536092801781391352310669)
                ·
                  refine ⟨10326034800668021757116501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27536092801781391352310669 10326034800668021757116501)
                  ·
                    refine ⟨121008220320328379966209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10326034800668021757116501 121008220320328379966209)
                    ·
                      rfl

theorem cell23_706988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_706988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706988 prefixEnd_706988 := by exact prefixLift 706988
  have htrace : WordTrace (prefixWord ++ tailWord_706988) baseStart_706988 baseEnd_706988 := by
    simpa [prefixWord, tailWord_706988, baseEnd_706988] using wordTrace_append hprefix tailTrace_706988
  have hstable : (prefixWord ++ tailWord_706988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706988).length < 2 ^ (prefixWord ++ tailWord_706988).sum := by decide
  have hdescent : baseEnd_706988 < baseStart_706988 := by decide
  rcases family_descends (prefixWord ++ tailWord_706988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706999 : List Nat := [1, 1, 3, 1, 3, 4, 1, 3, 1, 3, 2]
def baseStart_706999 : Nat := 118140960795 + 706999 * 2 ^ 59
def prefixEnd_706999 : Nat := 4983230072969 + 3 ^ 40 * 706999 * 2
def baseEnd_706999 : Nat := 363030309248184596861077

theorem tailTrace_706999 : CollatzResearch.WordTrace tailWord_706999 prefixEnd_706999 363030309248184596861077 := by
  unfold tailWord_706999
  simp only [CollatzResearch.WordTrace]
  refine ⟨25786371965670843661244051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17190914643780562440829367 25786371965670843661244051)
  ·
    refine ⟨38679557948506265491866077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25786371965670843661244051 38679557948506265491866077)
    ·
      refine ⟨14504834230689849559449779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38679557948506265491866077 14504834230689849559449779)
      ·
        refine ⟨21757251346034774339174669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14504834230689849559449779 21757251346034774339174669)
        ·
          refine ⟨8158969254763040377190501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21757251346034774339174669 8158969254763040377190501)
          ·
            refine ⟨1529806735268070070723219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8158969254763040377190501 1529806735268070070723219)
            ·
              refine ⟨2294710102902105106084829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529806735268070070723219 2294710102902105106084829)
              ·
                refine ⟨860516288588289414781811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2294710102902105106084829 860516288588289414781811)
                ·
                  refine ⟨1290774432882434122172717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 860516288588289414781811 1290774432882434122172717)
                  ·
                    refine ⟨484040412330912795814769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1290774432882434122172717 484040412330912795814769)
                    ·
                      refine ⟨363030309248184596861077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 484040412330912795814769 363030309248184596861077)
                      ·
                        rfl

theorem cell23_706999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 3, 2].length) (baseStart_706999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_706999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_706999 prefixEnd_706999 := by exact prefixLift 706999
  have htrace : WordTrace (prefixWord ++ tailWord_706999) baseStart_706999 baseEnd_706999 := by
    simpa [prefixWord, tailWord_706999, baseEnd_706999] using wordTrace_append hprefix tailTrace_706999
  have hstable : (prefixWord ++ tailWord_706999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706999).length < 2 ^ (prefixWord ++ tailWord_706999).sum := by decide
  have hdescent : baseEnd_706999 < baseStart_706999 := by decide
  rcases family_descends (prefixWord ++ tailWord_706999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707005 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 2, 6]
def baseStart_707005 : Nat := 118140960795 + 707005 * 2 ^ 59
def prefixEnd_707005 : Nat := 4983230072969 + 3 ^ 40 * 707005 * 2
def baseEnd_707005 : Nat := 121011130044037191128683

theorem tailTrace_707005 : CollatzResearch.WordTrace tailWord_707005 prefixEnd_707005 121011130044037191128683 := by
  unfold tailWord_707005
  simp only [CollatzResearch.WordTrace]
  refine ⟨25786590803649106685962469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17191060535766071123974979 25786590803649106685962469)
  ·
    refine ⟨4834985775684207503617963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25786590803649106685962469 4834985775684207503617963)
    ·
      refine ⟨7252478663526311255426945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4834985775684207503617963 7252478663526311255426945)
      ·
        refine ⟨5439358997644733441570209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7252478663526311255426945 5439358997644733441570209)
        ·
          refine ⟨4079519248233550081177657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5439358997644733441570209 4079519248233550081177657)
          ·
            refine ⟨3059639436175162560883243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4079519248233550081177657 3059639436175162560883243)
            ·
              refine ⟨4589459154262743841324865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3059639436175162560883243 4589459154262743841324865)
              ·
                refine ⟨3442094365697057880993649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4589459154262743841324865 3442094365697057880993649)
                ·
                  refine ⟨2581570774272793410745237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3442094365697057880993649 2581570774272793410745237)
                  ·
                    refine ⟨121011130044037191128683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2581570774272793410745237 121011130044037191128683)
                    ·
                      rfl

theorem cell23_707005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_707005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707005 prefixEnd_707005 := by exact prefixLift 707005
  have htrace : WordTrace (prefixWord ++ tailWord_707005) baseStart_707005 baseEnd_707005 := by
    simpa [prefixWord, tailWord_707005, baseEnd_707005] using wordTrace_append hprefix tailTrace_707005
  have hstable : (prefixWord ++ tailWord_707005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707005).length < 2 ^ (prefixWord ++ tailWord_707005).sum := by decide
  have hdescent : baseEnd_707005 < baseStart_707005 := by decide
  rcases family_descends (prefixWord ++ tailWord_707005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707029 : List Nat := [1, 3, 2, 3, 1, 2, 3, 1, 1, 4, 2]
def baseStart_707029 : Nat := 118140960795 + 707029 * 2 ^ 59
def prefixEnd_707029 : Nat := 4983230072969 + 3 ^ 40 * 707029 * 2
def baseEnd_707029 : Nat := 363045713667819479485939

theorem tailTrace_707029 : CollatzResearch.WordTrace tailWord_707029 prefixEnd_707029 363045713667819479485939 := by
  unfold tailWord_707029
  simp only [CollatzResearch.WordTrace]
  refine ⟨25787466155562158784836141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17191644103708105856557427 25787466155562158784836141)
  ·
    refine ⟨9670299808335809544313553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25787466155562158784836141 9670299808335809544313553)
    ·
      refine ⟨7252724856251857158235165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9670299808335809544313553 7252724856251857158235165)
      ·
        refine ⟨2719771821094446434338187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7252724856251857158235165 2719771821094446434338187)
        ·
          refine ⟨4079657731641669651507281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2719771821094446434338187 4079657731641669651507281)
          ·
            refine ⟨3059743298731252238630461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4079657731641669651507281 3059743298731252238630461)
            ·
              refine ⟨1147403737024219589486423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3059743298731252238630461 1147403737024219589486423)
              ·
                refine ⟨1721105605536329384229635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1147403737024219589486423 1721105605536329384229635)
                ·
                  refine ⟨2581658408304494076344453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1721105605536329384229635 2581658408304494076344453)
                  ·
                    refine ⟨484060951557092639314585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2581658408304494076344453 484060951557092639314585)
                    ·
                      refine ⟨363045713667819479485939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 484060951557092639314585 363045713667819479485939)
                      ·
                        rfl

theorem cell23_707029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_707029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707029 prefixEnd_707029 := by exact prefixLift 707029
  have htrace : WordTrace (prefixWord ++ tailWord_707029) baseStart_707029 baseEnd_707029 := by
    simpa [prefixWord, tailWord_707029, baseEnd_707029] using wordTrace_append hprefix tailTrace_707029
  have hstable : (prefixWord ++ tailWord_707029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707029).length < 2 ^ (prefixWord ++ tailWord_707029).sum := by decide
  have hdescent : baseEnd_707029 < baseStart_707029 := by decide
  rcases family_descends (prefixWord ++ tailWord_707029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707065 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 4, 5]
def baseStart_707065 : Nat := 118140960795 + 707065 * 2 ^ 59
def prefixEnd_707065 : Nat := 4983230072969 + 3 ^ 40 * 707065 * 2
def baseEnd_707065 : Nat := 121021399657127112878591

theorem tailTrace_707065 : CollatzResearch.WordTrace tailWord_707065 prefixEnd_707065 121021399657127112878591 := by
  unfold tailWord_707065
  simp only [CollatzResearch.WordTrace]
  refine ⟨25788779183431736933146649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17192519455621157955431099 25788779183431736933146649)
  ·
    refine ⟨19341584387573802699859987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25788779183431736933146649 19341584387573802699859987)
    ·
      refine ⟨29012376581360704049789981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19341584387573802699859987 29012376581360704049789981)
      ·
        refine ⟨10879641218010264018671243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29012376581360704049789981 10879641218010264018671243)
        ·
          refine ⟨16319461827015396028006865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10879641218010264018671243 16319461827015396028006865)
          ·
            refine ⟨12239596370261547021005149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16319461827015396028006865 12239596370261547021005149)
            ·
              refine ⟨4589848638848080132876931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12239596370261547021005149 4589848638848080132876931)
              ·
                refine ⟨6884772958272120199315397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4589848638848080132876931 6884772958272120199315397)
                ·
                  refine ⟨1290894929676022537371637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6884772958272120199315397 1290894929676022537371637)
                  ·
                    refine ⟨121021399657127112878591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1290894929676022537371637 121021399657127112878591)
                    ·
                      rfl

theorem cell23_707065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 5].length) (baseStart_707065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707065 prefixEnd_707065 := by exact prefixLift 707065
  have htrace : WordTrace (prefixWord ++ tailWord_707065) baseStart_707065 baseEnd_707065 := by
    simpa [prefixWord, tailWord_707065, baseEnd_707065] using wordTrace_append hprefix tailTrace_707065
  have hstable : (prefixWord ++ tailWord_707065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707065).length < 2 ^ (prefixWord ++ tailWord_707065).sum := by decide
  have hdescent : baseEnd_707065 < baseStart_707065 := by decide
  rcases family_descends (prefixWord ++ tailWord_707065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707069 : List Nat := [1, 4, 1, 1, 1, 3, 5, 2, 5]
def baseStart_707069 : Nat := 118140960795 + 707069 * 2 ^ 59
def prefixEnd_707069 : Nat := 4983230072969 + 3 ^ 40 * 707069 * 2
def baseEnd_707069 : Nat := 40340694765999924776195

theorem tailTrace_707069 : CollatzResearch.WordTrace tailWord_707069 prefixEnd_707069 40340694765999924776195 := by
  unfold tailWord_707069
  simp only [CollatzResearch.WordTrace]
  refine ⟨25788925075417245616292261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17192616716944830410861507 25788925075417245616292261)
  ·
    refine ⟨4835423451640733553054799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25788925075417245616292261 4835423451640733553054799)
    ·
      refine ⟨7253135177461100329582199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4835423451640733553054799 7253135177461100329582199)
      ·
        refine ⟨10879702766191650494373299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7253135177461100329582199 10879702766191650494373299)
        ·
          refine ⟨16319554149287475741559949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10879702766191650494373299 16319554149287475741559949)
          ·
            refine ⟨6119832805982803403084981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16319554149287475741559949 6119832805982803403084981)
            ·
              refine ⟨573734325560887819039217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6119832805982803403084981 573734325560887819039217)
              ·
                refine ⟨430300744170665864279413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 573734325560887819039217 430300744170665864279413)
                ·
                  refine ⟨40340694765999924776195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 430300744170665864279413 40340694765999924776195)
                  ·
                    rfl

theorem cell23_707069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_707069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707069 prefixEnd_707069 := by exact prefixLift 707069
  have htrace : WordTrace (prefixWord ++ tailWord_707069) baseStart_707069 baseEnd_707069 := by
    simpa [prefixWord, tailWord_707069, baseEnd_707069] using wordTrace_append hprefix tailTrace_707069
  have hstable : (prefixWord ++ tailWord_707069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707069).length < 2 ^ (prefixWord ++ tailWord_707069).sum := by decide
  have hdescent : baseEnd_707069 < baseStart_707069 := by decide
  rcases family_descends (prefixWord ++ tailWord_707069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707075 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 5]
def baseStart_707075 : Nat := 118140960795 + 707075 * 2 ^ 59
def prefixEnd_707075 : Nat := 4983230072969 + 3 ^ 40 * 707075 * 2
def baseEnd_707075 : Nat := 363069333777926299510727

theorem tailTrace_707075 : CollatzResearch.WordTrace tailWord_707075 prefixEnd_707075 363069333777926299510727 := by
  unfold tailWord_707075
  simp only [CollatzResearch.WordTrace]
  refine ⟨25789143913395508641010679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17192762608930339094007119 25789143913395508641010679)
  ·
    refine ⟨38683715870093262961516019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25789143913395508641010679 38683715870093262961516019)
    ·
      refine ⟨58025573805139894442274029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38683715870093262961516019 58025573805139894442274029)
      ·
        refine ⟨21759590176927460415852761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58025573805139894442274029 21759590176927460415852761)
        ·
          refine ⟨16319692632695595311889571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21759590176927460415852761 16319692632695595311889571)
          ·
            refine ⟨24479538949043392967834357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16319692632695595311889571 24479538949043392967834357)
            ·
              refine ⟨2294956776472818090734471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24479538949043392967834357 2294956776472818090734471)
              ·
                refine ⟨3442435164709227136101707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2294956776472818090734471 3442435164709227136101707)
                ·
                  refine ⟨5163652747063840704152561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3442435164709227136101707 5163652747063840704152561)
                  ·
                    refine ⟨3872739560297880528114421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5163652747063840704152561 3872739560297880528114421)
                    ·
                      refine ⟨363069333777926299510727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3872739560297880528114421 363069333777926299510727)
                      ·
                        rfl

theorem cell23_707075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_707075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707075 prefixEnd_707075 := by exact prefixLift 707075
  have htrace : WordTrace (prefixWord ++ tailWord_707075) baseStart_707075 baseEnd_707075 := by
    simpa [prefixWord, tailWord_707075, baseEnd_707075] using wordTrace_append hprefix tailTrace_707075
  have hstable : (prefixWord ++ tailWord_707075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707075).length < 2 ^ (prefixWord ++ tailWord_707075).sum := by decide
  have hdescent : baseEnd_707075 < baseStart_707075 := by decide
  rcases family_descends (prefixWord ++ tailWord_707075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707156 : List Nat := [2, 4, 1, 1, 1, 5, 1, 1, 2, 2, 3]
def baseStart_707156 : Nat := 118140960795 + 707156 * 2 ^ 59
def prefixEnd_707156 : Nat := 4983230072969 + 3 ^ 40 * 707156 * 2
def baseEnd_707156 : Nat := 363110925710940482597855

theorem tailTrace_707156 : CollatzResearch.WordTrace tailWord_707156 prefixEnd_707156 363110925710940482597855 := by
  unfold tailWord_707156
  simp only [CollatzResearch.WordTrace]
  refine ⟨12896049113051029737354661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17194732150734706316472881 12896049113051029737354661)
  ·
    refine ⟨2418009208697068075753999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12896049113051029737354661 2418009208697068075753999)
    ·
      refine ⟨3627013813045602113630999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2418009208697068075753999 3627013813045602113630999)
      ·
        refine ⟨5440520719568403170446499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3627013813045602113630999 5440520719568403170446499)
        ·
          refine ⟨8160781079352604755669749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5440520719568403170446499 8160781079352604755669749)
          ·
            refine ⟨765073226189306695844039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8160781079352604755669749 765073226189306695844039)
            ·
              refine ⟨1147609839283960043766059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 765073226189306695844039 1147609839283960043766059)
              ·
                refine ⟨1721414758925940065649089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1147609839283960043766059 1721414758925940065649089)
                ·
                  refine ⟨1291061069194455049236817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1721414758925940065649089 1291061069194455049236817)
                  ·
                    refine ⟨968295801895841286927613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1291061069194455049236817 968295801895841286927613)
                    ·
                      refine ⟨363110925710940482597855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 968295801895841286927613 363110925710940482597855)
                      ·
                        rfl

theorem cell23_707156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_707156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707156 prefixEnd_707156 := by exact prefixLift 707156
  have htrace : WordTrace (prefixWord ++ tailWord_707156) baseStart_707156 baseEnd_707156 := by
    simpa [prefixWord, tailWord_707156, baseEnd_707156] using wordTrace_append hprefix tailTrace_707156
  have hstable : (prefixWord ++ tailWord_707156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707156).length < 2 ^ (prefixWord ++ tailWord_707156).sum := by decide
  have hdescent : baseEnd_707156 < baseStart_707156 := by decide
  rcases family_descends (prefixWord ++ tailWord_707156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707176 : List Nat := [2, 1, 4, 3, 2, 2, 1, 2, 6]
def baseStart_707176 : Nat := 118140960795 + 707176 * 2 ^ 59
def prefixEnd_707176 : Nat := 4983230072969 + 3 ^ 40 * 707176 * 2
def baseEnd_707176 : Nat := 40346799480447822705307

theorem tailTrace_707176 : CollatzResearch.WordTrace tailWord_707176 prefixEnd_707176 40346799480447822705307 := by
  unfold tailWord_707176
  simp only [CollatzResearch.WordTrace]
  refine ⟨12896413843014801445218691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17195218457353068593624921 12896413843014801445218691)
  ·
    refine ⟨19344620764522202167828037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12896413843014801445218691 19344620764522202167828037)
    ·
      refine ⟨3627116393347912906467757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19344620764522202167828037 3627116393347912906467757)
      ·
        refine ⟨1360168647505467339925409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3627116393347912906467757 1360168647505467339925409)
        ·
          refine ⟨1020126485629100504944057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1360168647505467339925409 1020126485629100504944057)
          ·
            refine ⟨765094864221825378708043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1020126485629100504944057 765094864221825378708043)
            ·
              refine ⟨1147642296332738068062065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 765094864221825378708043 1147642296332738068062065)
              ·
                refine ⟨860731722249553551046549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1147642296332738068062065 860731722249553551046549)
                ·
                  refine ⟨40346799480447822705307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 860731722249553551046549 40346799480447822705307)
                  ·
                    rfl

theorem cell23_707176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 6].length) (baseStart_707176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707176 prefixEnd_707176 := by exact prefixLift 707176
  have htrace : WordTrace (prefixWord ++ tailWord_707176) baseStart_707176 baseEnd_707176 := by
    simpa [prefixWord, tailWord_707176, baseEnd_707176] using wordTrace_append hprefix tailTrace_707176
  have hstable : (prefixWord ++ tailWord_707176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707176).length < 2 ^ (prefixWord ++ tailWord_707176).sum := by decide
  have hdescent : baseEnd_707176 < baseStart_707176 := by decide
  rcases family_descends (prefixWord ++ tailWord_707176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707185 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 2, 10]
def baseStart_707185 : Nat := 118140960795 + 707185 * 2 ^ 59
def prefixEnd_707185 : Nat := 4983230072969 + 3 ^ 40 * 707185 * 2
def baseEnd_707185 : Nat := 121041938883306956378407

theorem tailTrace_707185 : CollatzResearch.WordTrace tailWord_707185 prefixEnd_707185 121041938883306956378407 := by
  unfold tailWord_707185
  simp only [CollatzResearch.WordTrace]
  refine ⟨25793155942996997427515009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17195437295331331618343339 25793155942996997427515009)
  ·
    refine ⟨19344866957247748070636257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25793155942996997427515009 19344866957247748070636257)
    ·
      refine ⟨14508650217935811052977193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19344866957247748070636257 14508650217935811052977193)
      ·
        refine ⟨10881487663451858289732895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14508650217935811052977193 10881487663451858289732895)
        ·
          refine ⟨16322231495177787434599343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10881487663451858289732895 16322231495177787434599343)
          ·
            refine ⟨24483347242766681151899015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16322231495177787434599343 24483347242766681151899015)
            ·
              refine ⟨36725020864150021727848523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24483347242766681151899015 36725020864150021727848523)
              ·
                refine ⟨55087531296225032591772785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36725020864150021727848523 55087531296225032591772785)
                ·
                  refine ⟨41315648472168774443829589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55087531296225032591772785 41315648472168774443829589)
                  ·
                    refine ⟨121041938883306956378407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 41315648472168774443829589 121041938883306956378407)
                    ·
                      rfl

theorem cell23_707185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_707185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707185 prefixEnd_707185 := by exact prefixLift 707185
  have htrace : WordTrace (prefixWord ++ tailWord_707185) baseStart_707185 baseEnd_707185 := by
    simpa [prefixWord, tailWord_707185, baseEnd_707185] using wordTrace_append hprefix tailTrace_707185
  have hstable : (prefixWord ++ tailWord_707185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707185).length < 2 ^ (prefixWord ++ tailWord_707185).sum := by decide
  have hdescent : baseEnd_707185 < baseStart_707185 := by decide
  rcases family_descends (prefixWord ++ tailWord_707185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707215 : List Nat := [1, 1, 2, 1, 1, 1, 1, 15]
def baseStart_707215 : Nat := 118140960795 + 707215 * 2 ^ 59
def prefixEnd_707215 : Nat := 4983230072969 + 3 ^ 40 * 707215 * 2
def baseEnd_707215 : Nat := 13449674854427990805929

theorem tailTrace_707215 : CollatzResearch.WordTrace tailWord_707215 prefixEnd_707215 13449674854427990805929 := by
  unfold tailWord_707215
  simp only [CollatzResearch.WordTrace]
  refine ⟨25794250132888312551107099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17196166755258875034071399 25794250132888312551107099)
  ·
    refine ⟨38691375199332468826660649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25794250132888312551107099 38691375199332468826660649)
    ·
      refine ⟨29018531399499351619995487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38691375199332468826660649 29018531399499351619995487)
      ·
        refine ⟨43527797099249027429993231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29018531399499351619995487 43527797099249027429993231)
        ·
          refine ⟨65291695648873541144989847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43527797099249027429993231 65291695648873541144989847)
          ·
            refine ⟨97937543473310311717484771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65291695648873541144989847 97937543473310311717484771)
            ·
              refine ⟨146906315209965467576227157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97937543473310311717484771 146906315209965467576227157)
              ·
                refine ⟨13449674854427990805929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 15 146906315209965467576227157 13449674854427990805929)
                ·
                  rfl

theorem cell23_707215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 15].length) (baseStart_707215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707215 prefixEnd_707215 := by exact prefixLift 707215
  have htrace : WordTrace (prefixWord ++ tailWord_707215) baseStart_707215 baseEnd_707215 := by
    simpa [prefixWord, tailWord_707215, baseEnd_707215] using wordTrace_append hprefix tailTrace_707215
  have hstable : (prefixWord ++ tailWord_707215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707215).length < 2 ^ (prefixWord ++ tailWord_707215).sum := by decide
  have hdescent : baseEnd_707215 < baseStart_707215 := by decide
  rcases family_descends (prefixWord ++ tailWord_707215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707220 : List Nat := [2, 4, 2, 2, 1, 1, 3, 3, 1, 1, 3]
def baseStart_707220 : Nat := 118140960795 + 707220 * 2 ^ 59
def prefixEnd_707220 : Nat := 4983230072969 + 3 ^ 40 * 707220 * 2
def baseEnd_707220 : Nat := 363143788472828232197561

theorem tailTrace_707220 : CollatzResearch.WordTrace tailWord_707220 prefixEnd_707220 363143788472828232197561 := by
  unfold tailWord_707220
  simp only [CollatzResearch.WordTrace]
  refine ⟨12897216248935099202519557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17196288331913465603359409 12897216248935099202519557)
  ·
    refine ⟨2418228046675331100472417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12897216248935099202519557 2418228046675331100472417)
    ·
      refine ⟨1813671035006498325354313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2418228046675331100472417 1813671035006498325354313)
      ·
        refine ⟨1360253276254873744015735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1813671035006498325354313 1360253276254873744015735)
        ·
          refine ⟨2040379914382310616023603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1360253276254873744015735 2040379914382310616023603)
          ·
            refine ⟨3060569871573465924035405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2040379914382310616023603 3060569871573465924035405)
            ·
              refine ⟨1147713701840049721513277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3060569871573465924035405 1147713701840049721513277)
              ·
                refine ⟨430392638190018645567479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1147713701840049721513277 430392638190018645567479)
                ·
                  refine ⟨645588957285027968351219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 430392638190018645567479 645588957285027968351219)
                  ·
                    refine ⟨968383435927541952526829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 645588957285027968351219 968383435927541952526829)
                    ·
                      refine ⟨363143788472828232197561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 968383435927541952526829 363143788472828232197561)
                      ·
                        rfl

theorem cell23_707220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_707220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707220 prefixEnd_707220 := by exact prefixLift 707220
  have htrace : WordTrace (prefixWord ++ tailWord_707220) baseStart_707220 baseEnd_707220 := by
    simpa [prefixWord, tailWord_707220, baseEnd_707220] using wordTrace_append hprefix tailTrace_707220
  have hstable : (prefixWord ++ tailWord_707220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707220).length < 2 ^ (prefixWord ++ tailWord_707220).sum := by decide
  have hdescent : baseEnd_707220 < baseStart_707220 := by decide
  rcases family_descends (prefixWord ++ tailWord_707220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707246 : List Nat := [4, 1, 4, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_707246 : Nat := 118140960795 + 707246 * 2 ^ 59
def prefixEnd_707246 : Nat := 4983230072969 + 3 ^ 40 * 707246 * 2
def baseEnd_707246 : Nat := 363157138969845130472441

theorem tailTrace_707246 : CollatzResearch.WordTrace tailWord_707246 prefixEnd_707246 363157138969845130472441 := by
  unfold tailWord_707246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3224422599472000605685699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17196920530517336563657061 3224422599472000605685699)
  ·
    refine ⟨4836633899208000908528549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3224422599472000605685699 4836633899208000908528549)
    ·
      refine ⟨906868856101500170349103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4836633899208000908528549 906868856101500170349103)
      ·
        refine ⟨1360303284152250255523655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 906868856101500170349103 1360303284152250255523655)
        ·
          refine ⟨2040454926228375383285483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1360303284152250255523655 2040454926228375383285483)
          ·
            refine ⟨3060682389342563074928225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2040454926228375383285483 3060682389342563074928225)
            ·
              refine ⟨2295511792006922306196169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3060682389342563074928225 2295511792006922306196169)
              ·
                refine ⟨1721633844005191729647127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2295511792006922306196169 1721633844005191729647127)
                ·
                  refine ⟨2582450766007787594470691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1721633844005191729647127 2582450766007787594470691)
                  ·
                    refine ⟨3873676149011681391706037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2582450766007787594470691 3873676149011681391706037)
                    ·
                      refine ⟨363157138969845130472441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3873676149011681391706037 363157138969845130472441)
                      ·
                        rfl

theorem cell23_707246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_707246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707246 prefixEnd_707246 := by exact prefixLift 707246
  have htrace : WordTrace (prefixWord ++ tailWord_707246) baseStart_707246 baseEnd_707246 := by
    simpa [prefixWord, tailWord_707246, baseEnd_707246] using wordTrace_append hprefix tailTrace_707246
  have hstable : (prefixWord ++ tailWord_707246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707246).length < 2 ^ (prefixWord ++ tailWord_707246).sum := by decide
  have hdescent : baseEnd_707246 < baseStart_707246 := by decide
  rcases family_descends (prefixWord ++ tailWord_707246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707253 : List Nat := [1, 3, 3, 3, 1, 1, 4, 1, 2, 4]
def baseStart_707253 : Nat := 118140960795 + 707253 * 2 ^ 59
def prefixEnd_707253 : Nat := 4983230072969 + 3 ^ 40 * 707253 * 2
def baseEnd_707253 : Nat := 121053577778142201028303

theorem tailTrace_707253 : CollatzResearch.WordTrace tailWord_707253 prefixEnd_707253 121053577778142201028303 := by
  unfold tailWord_707253
  simp only [CollatzResearch.WordTrace]
  refine ⟨25795636106750645040990413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17197090737833763360660275 25795636106750645040990413)
  ·
    refine ⟨9673363540031491890371405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25795636106750645040990413 9673363540031491890371405)
    ·
      refine ⟨3627511327511809458889277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9673363540031491890371405 3627511327511809458889277)
      ·
        refine ⟨1360316747816928547083479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3627511327511809458889277 1360316747816928547083479)
        ·
          refine ⟨2040475121725392820625219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1360316747816928547083479 2040475121725392820625219)
          ·
            refine ⟨3060712682588089230937829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2040475121725392820625219 3060712682588089230937829)
            ·
              refine ⟨573883627985266730800843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3060712682588089230937829 573883627985266730800843)
              ·
                refine ⟨860825441977900096201265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573883627985266730800843 860825441977900096201265)
                ·
                  refine ⟨645619081483425072150949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 860825441977900096201265 645619081483425072150949)
                  ·
                    refine ⟨121053577778142201028303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 645619081483425072150949 121053577778142201028303)
                    ·
                      rfl

theorem cell23_707253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_707253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707253 prefixEnd_707253 := by exact prefixLift 707253
  have htrace : WordTrace (prefixWord ++ tailWord_707253) baseStart_707253 baseEnd_707253 := by
    simpa [prefixWord, tailWord_707253, baseEnd_707253] using wordTrace_append hprefix tailTrace_707253
  have hstable : (prefixWord ++ tailWord_707253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707253).length < 2 ^ (prefixWord ++ tailWord_707253).sum := by decide
  have hdescent : baseEnd_707253 < baseStart_707253 := by decide
  rcases family_descends (prefixWord ++ tailWord_707253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707276 : List Nat := [2, 2, 1, 5, 1, 2, 1, 2, 1, 3, 3]
def baseStart_707276 : Nat := 118140960795 + 707276 * 2 ^ 59
def prefixEnd_707276 : Nat := 4983230072969 + 3 ^ 40 * 707276 * 2
def baseEnd_707276 : Nat := 363172543389480013097303

theorem tailTrace_707276 : CollatzResearch.WordTrace tailWord_707276 prefixEnd_707276 363172543389480013097303 := by
  unfold tailWord_707276
  simp only [CollatzResearch.WordTrace]
  refine ⟨12898237492833659984538841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17197649990444879979385121 12898237492833659984538841)
  ·
    refine ⟨9673678119625244988404131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12898237492833659984538841 9673678119625244988404131)
    ·
      refine ⟨14510517179437867482606197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9673678119625244988404131 14510517179437867482606197)
      ·
        refine ⟨1360360985572300076494331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14510517179437867482606197 1360360985572300076494331)
        ·
          refine ⟨2040541478358450114741497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1360360985572300076494331 2040541478358450114741497)
          ·
            refine ⟨1530406108768837586056123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2040541478358450114741497 1530406108768837586056123)
            ·
              refine ⟨2295609163153256379084185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1530406108768837586056123 2295609163153256379084185)
              ·
                refine ⟨1721706872364942284313139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2295609163153256379084185 1721706872364942284313139)
                ·
                  refine ⟨2582560308547413426469709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1721706872364942284313139 2582560308547413426469709)
                  ·
                    refine ⟨968460115705280034926141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2582560308547413426469709 968460115705280034926141)
                    ·
                      refine ⟨363172543389480013097303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 968460115705280034926141 363172543389480013097303)
                      ·
                        rfl

theorem cell23_707276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_707276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707276 prefixEnd_707276 := by exact prefixLift 707276
  have htrace : WordTrace (prefixWord ++ tailWord_707276) baseStart_707276 baseEnd_707276 := by
    simpa [prefixWord, tailWord_707276, baseEnd_707276] using wordTrace_append hprefix tailTrace_707276
  have hstable : (prefixWord ++ tailWord_707276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707276).length < 2 ^ (prefixWord ++ tailWord_707276).sum := by decide
  have hdescent : baseEnd_707276 < baseStart_707276 := by decide
  rcases family_descends (prefixWord ++ tailWord_707276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707299 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 4]
def baseStart_707299 : Nat := 118140960795 + 707299 * 2 ^ 59
def prefixEnd_707299 : Nat := 4983230072969 + 3 ^ 40 * 707299 * 2
def baseEnd_707299 : Nat := 363184353444533423109697

theorem tailTrace_707299 : CollatzResearch.WordTrace tailWord_707299 prefixEnd_707299 363184353444533423109697 := by
  unfold tailWord_707299
  simp only [CollatzResearch.WordTrace]
  refine ⟨25797313864583994897164951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17198209243055996598109967 25797313864583994897164951)
  ·
    refine ⟨38695970796875992345747427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25797313864583994897164951 38695970796875992345747427)
    ·
      refine ⟨58043956195313988518621141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38695970796875992345747427 58043956195313988518621141)
      ·
        refine ⟨1360405223327671605905183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 58043956195313988518621141 1360405223327671605905183)
        ·
          refine ⟨2040607834991507408857775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1360405223327671605905183 2040607834991507408857775)
          ·
            refine ⟨3060911752487261113286663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2040607834991507408857775 3060911752487261113286663)
            ·
              refine ⟨4591367628730891669929995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3060911752487261113286663 4591367628730891669929995)
              ·
                refine ⟨6887051443096337504894993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4591367628730891669929995 6887051443096337504894993)
                ·
                  refine ⟨5165288582322253128671245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6887051443096337504894993 5165288582322253128671245)
                  ·
                    refine ⟨1936983218370844923251717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5165288582322253128671245 1936983218370844923251717)
                    ·
                      refine ⟨363184353444533423109697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1936983218370844923251717 363184353444533423109697)
                      ·
                        rfl

theorem cell23_707299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_707299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707299 prefixEnd_707299 := by exact prefixLift 707299
  have htrace : WordTrace (prefixWord ++ tailWord_707299) baseStart_707299 baseEnd_707299 := by
    simpa [prefixWord, tailWord_707299, baseEnd_707299] using wordTrace_append hprefix tailTrace_707299
  have hstable : (prefixWord ++ tailWord_707299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707299).length < 2 ^ (prefixWord ++ tailWord_707299).sum := by decide
  have hdescent : baseEnd_707299 < baseStart_707299 := by decide
  rcases family_descends (prefixWord ++ tailWord_707299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707309 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 2, 6]
def baseStart_707309 : Nat := 118140960795 + 707309 * 2 ^ 59
def prefixEnd_707309 : Nat := 4983230072969 + 3 ^ 40 * 707309 * 2
def baseEnd_707309 : Nat := 121063162750359461328217

theorem tailTrace_707309 : CollatzResearch.WordTrace tailWord_707309 prefixEnd_707309 121063162750359461328217 := by
  unfold tailWord_707309
  simp only [CollatzResearch.WordTrace]
  refine ⟨25797678594547766605028981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17198452396365177736685987 25797678594547766605028981)
  ·
    refine ⟨2418532368238853119221467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25797678594547766605028981 2418532368238853119221467)
    ·
      refine ⟨3627798552358279678832201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2418532368238853119221467 3627798552358279678832201)
      ·
        refine ⟨2720848914268709759124151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3627798552358279678832201 2720848914268709759124151)
        ·
          refine ⟨4081273371403064638686227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2720848914268709759124151 4081273371403064638686227)
          ·
            refine ⟨6121910057104596958029341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4081273371403064638686227 6121910057104596958029341)
            ·
              refine ⟨2295716271414223859261003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6121910057104596958029341 2295716271414223859261003)
              ·
                refine ⟨3443574407121335788891505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2295716271414223859261003 3443574407121335788891505)
                ·
                  refine ⟨2582680805341001841668629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3443574407121335788891505 2582680805341001841668629)
                  ·
                    refine ⟨121063162750359461328217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2582680805341001841668629 121063162750359461328217)
                    ·
                      rfl

theorem cell23_707309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_707309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707309 prefixEnd_707309 := by exact prefixLift 707309
  have htrace : WordTrace (prefixWord ++ tailWord_707309) baseStart_707309 baseEnd_707309 := by
    simpa [prefixWord, tailWord_707309, baseEnd_707309] using wordTrace_append hprefix tailTrace_707309
  have hstable : (prefixWord ++ tailWord_707309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707309).length < 2 ^ (prefixWord ++ tailWord_707309).sum := by decide
  have hdescent : baseEnd_707309 < baseStart_707309 := by decide
  rcases family_descends (prefixWord ++ tailWord_707309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707322 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 9]
def baseStart_707322 : Nat := 118140960795 + 707322 * 2 ^ 59
def prefixEnd_707322 : Nat := 4983230072969 + 3 ^ 40 * 707322 * 2
def baseEnd_707322 : Nat := 40355129277731870346899

theorem tailTrace_707322 : CollatzResearch.WordTrace tailWord_707322 prefixEnd_707322 40355129277731870346899 := by
  unfold tailWord_707322
  simp only [CollatzResearch.WordTrace]
  refine ⟨6449538185875167456313055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17198768495667113216834813 6449538185875167456313055)
  ·
    refine ⟨9674307278812751184469583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6449538185875167456313055 9674307278812751184469583)
    ·
      refine ⟨14511460918219126776704375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9674307278812751184469583 14511460918219126776704375)
      ·
        refine ⟨21767191377328690165056563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14511460918219126776704375 21767191377328690165056563)
        ·
          refine ⟨32650787065993035247584845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21767191377328690165056563 32650787065993035247584845)
          ·
            refine ⟨12244045149747388217844317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32650787065993035247584845 12244045149747388217844317)
            ·
              refine ⟨4591516931155270581691619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12244045149747388217844317 4591516931155270581691619)
              ·
                refine ⟨6887275396732905872537429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4591516931155270581691619 6887275396732905872537429)
                ·
                  refine ⟨40355129277731870346899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6887275396732905872537429 40355129277731870346899)
                  ·
                    rfl

theorem cell23_707322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 9].length) (baseStart_707322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707322 prefixEnd_707322 := by exact prefixLift 707322
  have htrace : WordTrace (prefixWord ++ tailWord_707322) baseStart_707322 baseEnd_707322 := by
    simpa [prefixWord, tailWord_707322, baseEnd_707322] using wordTrace_append hprefix tailTrace_707322
  have hstable : (prefixWord ++ tailWord_707322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707322).length < 2 ^ (prefixWord ++ tailWord_707322).sum := by decide
  have hdescent : baseEnd_707322 < baseStart_707322 := by decide
  rcases family_descends (prefixWord ++ tailWord_707322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707349 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 4, 3, 3]
def baseStart_707349 : Nat := 118140960795 + 707349 * 2 ^ 59
def prefixEnd_707349 : Nat := 4983230072969 + 3 ^ 40 * 707349 * 2
def baseEnd_707349 : Nat := 363210027477258227484467

theorem tailTrace_707349 : CollatzResearch.WordTrace tailWord_707349 prefixEnd_707349 363210027477258227484467 := by
  unfold tailWord_707349
  simp only [CollatzResearch.WordTrace]
  refine ⟨25799137514402853436485101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17199425009601902290990067 25799137514402853436485101)
  ·
    refine ⟨9674676567901070038681913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25799137514402853436485101 9674676567901070038681913)
    ·
      refine ⟨7256007425925802529011435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9674676567901070038681913 7256007425925802529011435)
      ·
        refine ⟨10884011138888703793517153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7256007425925802529011435 10884011138888703793517153)
        ·
          refine ⟨8163008354166527845137865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10884011138888703793517153 8163008354166527845137865)
          ·
            refine ⟨6122256265624895883853399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8163008354166527845137865 6122256265624895883853399)
            ·
              refine ⟨9183384398437343825780099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6122256265624895883853399 9183384398437343825780099)
              ·
                refine ⟨13775076597656015738670149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9183384398437343825780099 13775076597656015738670149)
                ·
                  refine ⟨2582826862060502951000653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13775076597656015738670149 2582826862060502951000653)
                  ·
                    refine ⟨968560073272688606625245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2582826862060502951000653 968560073272688606625245)
                    ·
                      refine ⟨363210027477258227484467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 968560073272688606625245 363210027477258227484467)
                      ·
                        rfl

theorem cell23_707349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_707349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707349 prefixEnd_707349 := by exact prefixLift 707349
  have htrace : WordTrace (prefixWord ++ tailWord_707349) baseStart_707349 baseEnd_707349 := by
    simpa [prefixWord, tailWord_707349, baseEnd_707349] using wordTrace_append hprefix tailTrace_707349
  have hstable : (prefixWord ++ tailWord_707349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707349).length < 2 ^ (prefixWord ++ tailWord_707349).sum := by decide
  have hdescent : baseEnd_707349 < baseStart_707349 := by decide
  rcases family_descends (prefixWord ++ tailWord_707349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707356 : List Nat := [2, 2, 3, 1, 1, 3, 2, 4, 5]
def baseStart_707356 : Nat := 118140960795 + 707356 * 2 ^ 59
def prefixEnd_707356 : Nat := 4983230072969 + 3 ^ 40 * 707356 * 2
def baseEnd_707356 : Nat := 40357069093537744455215

theorem tailTrace_707356 : CollatzResearch.WordTrace tailWord_707356 prefixEnd_707356 40357069093537744455215 := by
  unfold tailWord_707356
  simp only [CollatzResearch.WordTrace]
  refine ⟨12899696412688746815994961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17199595216918329087993281 12899696412688746815994961)
  ·
    refine ⟨9674772309516560111996221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12899696412688746815994961 9674772309516560111996221)
    ·
      refine ⟨3628039616068710041998583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9674772309516560111996221 3628039616068710041998583)
      ·
        refine ⟨5442059424103065062997875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3628039616068710041998583 5442059424103065062997875)
        ·
          refine ⟨8163089136154597594496813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5442059424103065062997875 8163089136154597594496813)
          ·
            refine ⟨3061158426057974097936305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8163089136154597594496813 3061158426057974097936305)
            ·
              refine ⟨2295868819543480573452229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3061158426057974097936305 2295868819543480573452229)
              ·
                refine ⟨430475403664402607522293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2295868819543480573452229 430475403664402607522293)
                ·
                  refine ⟨40357069093537744455215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 430475403664402607522293 40357069093537744455215)
                  ·
                    rfl

theorem cell23_707356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 5].length) (baseStart_707356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707356 prefixEnd_707356 := by exact prefixLift 707356
  have htrace : WordTrace (prefixWord ++ tailWord_707356) baseStart_707356 baseEnd_707356 := by
    simpa [prefixWord, tailWord_707356, baseEnd_707356] using wordTrace_append hprefix tailTrace_707356
  have hstable : (prefixWord ++ tailWord_707356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707356).length < 2 ^ (prefixWord ++ tailWord_707356).sum := by decide
  have hdescent : baseEnd_707356 < baseStart_707356 := by decide
  rcases family_descends (prefixWord ++ tailWord_707356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707390 : List Nat := [4, 2, 1, 2, 3, 2, 1, 3, 5]
def baseStart_707390 : Nat := 118140960795 + 707390 * 2 ^ 59
def prefixEnd_707390 : Nat := 4983230072969 + 3 ^ 40 * 707390 * 2
def baseEnd_707390 : Nat := 40359008909343618563531

theorem tailTrace_707390 : CollatzResearch.WordTrace tailWord_707390 prefixEnd_707390 40359008909343618563531 := by
  unfold tailWord_707390
  simp only [CollatzResearch.WordTrace]
  refine ⟨3225079113406789679840953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17200421938169544959151749 3225079113406789679840953)
  ·
    refine ⟨2418809335055092259880715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3225079113406789679840953 2418809335055092259880715)
    ·
      refine ⟨3628214002582638389821073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2418809335055092259880715 3628214002582638389821073)
      ·
        refine ⟨2721160501936978792365805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3628214002582638389821073 2721160501936978792365805)
        ·
          refine ⟨1020435188226367047137177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2721160501936978792365805 1020435188226367047137177)
          ·
            refine ⟨765326391169775285352883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1020435188226367047137177 765326391169775285352883)
            ·
              refine ⟨1147989586754662928029325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 765326391169775285352883 1147989586754662928029325)
              ·
                refine ⟨430496095032998598010997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1147989586754662928029325 430496095032998598010997)
                ·
                  refine ⟨40359008909343618563531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 430496095032998598010997 40359008909343618563531)
                  ·
                    rfl

theorem cell23_707390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_707390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707390 prefixEnd_707390 := by exact prefixLift 707390
  have htrace : WordTrace (prefixWord ++ tailWord_707390) baseStart_707390 baseEnd_707390 := by
    simpa [prefixWord, tailWord_707390, baseEnd_707390] using wordTrace_append hprefix tailTrace_707390
  have hstable : (prefixWord ++ tailWord_707390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707390).length < 2 ^ (prefixWord ++ tailWord_707390).sum := by decide
  have hdescent : baseEnd_707390 < baseStart_707390 := by decide
  rcases family_descends (prefixWord ++ tailWord_707390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707406 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2]
def baseStart_707406 : Nat := 118140960795 + 707406 * 2 ^ 59
def prefixEnd_707406 : Nat := 4983230072969 + 3 ^ 40 * 707406 * 2
def baseEnd_707406 : Nat := 363239295874564504471705

theorem tailTrace_707406 : CollatzResearch.WordTrace tailWord_707406 prefixEnd_707406 363239295874564504471705 := by
  unfold tailWord_707406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3225152059399544021413759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17200810983464234780873381 3225152059399544021413759)
  ·
    refine ⟨4837728089099316032120639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3225152059399544021413759 4837728089099316032120639)
    ·
      refine ⟨7256592133648974048180959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4837728089099316032120639 7256592133648974048180959)
      ·
        refine ⟨10884888200473461072271439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7256592133648974048180959 10884888200473461072271439)
        ·
          refine ⟨16327332300710191608407159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10884888200473461072271439 16327332300710191608407159)
          ·
            refine ⟨24490998451065287412610739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16327332300710191608407159 24490998451065287412610739)
            ·
              refine ⟨36736497676597931118916109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24490998451065287412610739 36736497676597931118916109)
              ·
                refine ⟨13776186628724224169593541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36736497676597931118916109 13776186628724224169593541)
                ·
                  refine ⟨2583034992885792031798789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13776186628724224169593541 2583034992885792031798789)
                  ·
                    refine ⟨484319061166086005962273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2583034992885792031798789 484319061166086005962273)
                    ·
                      refine ⟨363239295874564504471705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 484319061166086005962273 363239295874564504471705)
                      ·
                        rfl

theorem cell23_707406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2].length) (baseStart_707406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707406 prefixEnd_707406 := by exact prefixLift 707406
  have htrace : WordTrace (prefixWord ++ tailWord_707406) baseStart_707406 baseEnd_707406 := by
    simpa [prefixWord, tailWord_707406, baseEnd_707406] using wordTrace_append hprefix tailTrace_707406
  have hstable : (prefixWord ++ tailWord_707406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707406).length < 2 ^ (prefixWord ++ tailWord_707406).sum := by decide
  have hdescent : baseEnd_707406 < baseStart_707406 := by decide
  rcases family_descends (prefixWord ++ tailWord_707406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707439 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 3]
def baseStart_707439 : Nat := 118140960795 + 707439 * 2 ^ 59
def prefixEnd_707439 : Nat := 4983230072969 + 3 ^ 40 * 707439 * 2
def baseEnd_707439 : Nat := 363256240736162875359053

theorem tailTrace_707439 : CollatzResearch.WordTrace tailWord_707439 prefixEnd_707439 363256240736162875359053 := by
  unfold tailWord_707439
  simp only [CollatzResearch.WordTrace]
  refine ⟨25802420084076798807261371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17201613389384532538174247 25802420084076798807261371)
  ·
    refine ⟨38703630126115198210892057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25802420084076798807261371 38703630126115198210892057)
    ·
      refine ⟨29027722594586398658169043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38703630126115198210892057 29027722594586398658169043)
      ·
        refine ⟨43541583891879597987253565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29027722594586398658169043 43541583891879597987253565)
        ·
          refine ⟨16328093959454849245220087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43541583891879597987253565 16328093959454849245220087)
          ·
            refine ⟨24492140939182273867830131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16328093959454849245220087 24492140939182273867830131)
            ·
              refine ⟨36738211408773410801745197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24492140939182273867830131 36738211408773410801745197)
              ·
                refine ⟨13776829278290029050654449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36738211408773410801745197 13776829278290029050654449)
                ·
                  refine ⟨10332621958717521787990837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13776829278290029050654449 10332621958717521787990837)
                  ·
                    refine ⟨968683308629767667624141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10332621958717521787990837 968683308629767667624141)
                    ·
                      refine ⟨363256240736162875359053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 968683308629767667624141 363256240736162875359053)
                      ·
                        rfl

theorem cell23_707439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 3].length) (baseStart_707439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707439 prefixEnd_707439 := by exact prefixLift 707439
  have htrace : WordTrace (prefixWord ++ tailWord_707439) baseStart_707439 baseEnd_707439 := by
    simpa [prefixWord, tailWord_707439, baseEnd_707439] using wordTrace_append hprefix tailTrace_707439
  have hstable : (prefixWord ++ tailWord_707439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707439).length < 2 ^ (prefixWord ++ tailWord_707439).sum := by decide
  have hdescent : baseEnd_707439 < baseStart_707439 := by decide
  rcases family_descends (prefixWord ++ tailWord_707439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707456 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 7, 1, 3]
def baseStart_707456 : Nat := 118140960795 + 707456 * 2 ^ 59
def prefixEnd_707456 : Nat := 4983230072969 + 3 ^ 40 * 707456 * 2
def baseEnd_707456 : Nat := 363264969907289308846475

theorem tailTrace_707456 : CollatzResearch.WordTrace tailWord_707456 prefixEnd_707456 363264969907289308846475 := by
  unfold tailWord_707456
  simp only [CollatzResearch.WordTrace]
  refine ⟨12901520062507605355315111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17202026750010140473753481 12901520062507605355315111)
  ·
    refine ⟨19352280093761408032972667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12901520062507605355315111 19352280093761408032972667)
    ·
      refine ⟨29028420140642112049459001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19352280093761408032972667 29028420140642112049459001)
      ·
        refine ⟨21771315105481584037094251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29028420140642112049459001 21771315105481584037094251)
        ·
          refine ⟨32656972658222376055641377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21771315105481584037094251 32656972658222376055641377)
          ·
            refine ⟨24492729493666782041731033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32656972658222376055641377 24492729493666782041731033)
            ·
              refine ⟨18369547120250086531298275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24492729493666782041731033 18369547120250086531298275)
              ·
                refine ⟨27554320680375129796947413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18369547120250086531298275 27554320680375129796947413)
                ·
                  refine ⟨645804390946292104615955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 27554320680375129796947413 645804390946292104615955)
                  ·
                    refine ⟨968706586419438156923933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 645804390946292104615955 968706586419438156923933)
                    ·
                      refine ⟨363264969907289308846475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 968706586419438156923933 363264969907289308846475)
                      ·
                        rfl

theorem cell23_707456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 7, 1, 3].length) (baseStart_707456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707456 prefixEnd_707456 := by exact prefixLift 707456
  have htrace : WordTrace (prefixWord ++ tailWord_707456) baseStart_707456 baseEnd_707456 := by
    simpa [prefixWord, tailWord_707456, baseEnd_707456] using wordTrace_append hprefix tailTrace_707456
  have hstable : (prefixWord ++ tailWord_707456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707456).length < 2 ^ (prefixWord ++ tailWord_707456).sum := by decide
  have hdescent : baseEnd_707456 < baseStart_707456 := by decide
  rcases family_descends (prefixWord ++ tailWord_707456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707476 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 5, 5]
def baseStart_707476 : Nat := 118140960795 + 707476 * 2 ^ 59
def prefixEnd_707476 : Nat := 4983230072969 + 3 ^ 40 * 707476 * 2
def baseEnd_707476 : Nat := 121091746506793076865461

theorem tailTrace_707476 : CollatzResearch.WordTrace tailWord_707476 prefixEnd_707476 121091746506793076865461 := by
  unfold tailWord_707476
  simp only [CollatzResearch.WordTrace]
  refine ⟨12901884792471377063179141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17202513056628502750905521 12901884792471377063179141)
  ·
    refine ⟨2419103398588383199346089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12901884792471377063179141 2419103398588383199346089)
    ·
      refine ⟨1814327548941287399509567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2419103398588383199346089 1814327548941287399509567)
      ·
        refine ⟨2721491323411931099264351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1814327548941287399509567 2721491323411931099264351)
        ·
          refine ⟨4082236985117896648896527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2721491323411931099264351 4082236985117896648896527)
          ·
            refine ⟨6123355477676844973344791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4082236985117896648896527 6123355477676844973344791)
            ·
              refine ⟨9185033216515267460017187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6123355477676844973344791 9185033216515267460017187)
              ·
                refine ⟨13777549824772901190025781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9185033216515267460017187 13777549824772901190025781)
                ·
                  refine ⟨1291645296072459486564917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13777549824772901190025781 1291645296072459486564917)
                  ·
                    refine ⟨121091746506793076865461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1291645296072459486564917 121091746506793076865461)
                    ·
                      rfl

theorem cell23_707476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_707476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707476 prefixEnd_707476 := by exact prefixLift 707476
  have htrace : WordTrace (prefixWord ++ tailWord_707476) baseStart_707476 baseEnd_707476 := by
    simpa [prefixWord, tailWord_707476, baseEnd_707476] using wordTrace_append hprefix tailTrace_707476
  have hstable : (prefixWord ++ tailWord_707476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707476).length < 2 ^ (prefixWord ++ tailWord_707476).sum := by decide
  have hdescent : baseEnd_707476 < baseStart_707476 := by decide
  rcases family_descends (prefixWord ++ tailWord_707476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707490 : List Nat := [3, 3, 1, 2, 2, 2, 1, 2, 3, 1, 3]
def baseStart_707490 : Nat := 118140960795 + 707490 * 2 ^ 59
def prefixEnd_707490 : Nat := 4983230072969 + 3 ^ 40 * 707490 * 2
def baseEnd_707490 : Nat := 363282428249542175821319

theorem tailTrace_707490 : CollatzResearch.WordTrace tailWord_707490 prefixEnd_707490 363282428249542175821319 := by
  unfold tailWord_707490
  simp only [CollatzResearch.WordTrace]
  refine ⟨6451070051723008629341981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17202853471261356344911949 6451070051723008629341981)
  ·
    refine ⟨2419151269396128236003243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6451070051723008629341981 2419151269396128236003243)
    ·
      refine ⟨3628726904094192354004865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2419151269396128236003243 3628726904094192354004865)
      ·
        refine ⟨2721545178070644265503649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3628726904094192354004865 2721545178070644265503649)
        ·
          refine ⟨2041158883552983199127737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2721545178070644265503649 2041158883552983199127737)
          ·
            refine ⟨1530869162664737399345803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2041158883552983199127737 1530869162664737399345803)
            ·
              refine ⟨2296303743997106099018705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1530869162664737399345803 2296303743997106099018705)
              ·
                refine ⟨1722227807997829574264029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2296303743997106099018705 1722227807997829574264029)
                ·
                  refine ⟨645835427999186090349011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1722227807997829574264029 645835427999186090349011)
                  ·
                    refine ⟨968753141998779135523517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 645835427999186090349011 968753141998779135523517)
                    ·
                      refine ⟨363282428249542175821319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 968753141998779135523517 363282428249542175821319)
                      ·
                        rfl

theorem cell23_707490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_707490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707490 prefixEnd_707490 := by exact prefixLift 707490
  have htrace : WordTrace (prefixWord ++ tailWord_707490) baseStart_707490 baseEnd_707490 := by
    simpa [prefixWord, tailWord_707490, baseEnd_707490] using wordTrace_append hprefix tailTrace_707490
  have hstable : (prefixWord ++ tailWord_707490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707490).length < 2 ^ (prefixWord ++ tailWord_707490).sum := by decide
  have hdescent : baseEnd_707490 < baseStart_707490 := by decide
  rcases family_descends (prefixWord ++ tailWord_707490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707499 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 5]
def baseStart_707499 : Nat := 118140960795 + 707499 * 2 ^ 59
def prefixEnd_707499 : Nat := 4983230072969 + 3 ^ 40 * 707499 * 2
def baseEnd_707499 : Nat := 363287049575432640608777

theorem tailTrace_707499 : CollatzResearch.WordTrace tailWord_707499 prefixEnd_707499 363287049575432640608777 := by
  unfold tailWord_707499
  simp only [CollatzResearch.WordTrace]
  refine ⟨25804608463859429054445551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17203072309239619369630367 25804608463859429054445551)
  ·
    refine ⟨38706912695789143581668327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25804608463859429054445551 38706912695789143581668327)
    ·
      refine ⟨58060369043683715372502491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38706912695789143581668327 58060369043683715372502491)
      ·
        refine ⟨87090553565525573058753737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58060369043683715372502491 87090553565525573058753737)
        ·
          refine ⟨65317915174144179794065303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87090553565525573058753737 65317915174144179794065303)
          ·
            refine ⟨97976872761216269691097955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65317915174144179794065303 97976872761216269691097955)
            ·
              refine ⟨146965309141824404536646933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97976872761216269691097955 146965309141824404536646933)
              ·
                refine ⟨6888998866023018962655325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 146965309141824404536646933 6888998866023018962655325)
                ·
                  refine ⟨2583374574758632110995747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6888998866023018962655325 2583374574758632110995747)
                  ·
                    refine ⟨3875061862137948166493621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2583374574758632110995747 3875061862137948166493621)
                    ·
                      refine ⟨363287049575432640608777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3875061862137948166493621 363287049575432640608777)
                      ·
                        rfl

theorem cell23_707499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 5].length) (baseStart_707499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707499 prefixEnd_707499 := by exact prefixLift 707499
  have htrace : WordTrace (prefixWord ++ tailWord_707499) baseStart_707499 baseEnd_707499 := by
    simpa [prefixWord, tailWord_707499, baseEnd_707499] using wordTrace_append hprefix tailTrace_707499
  have hstable : (prefixWord ++ tailWord_707499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707499).length < 2 ^ (prefixWord ++ tailWord_707499).sum := by decide
  have hdescent : baseEnd_707499 < baseStart_707499 := by decide
  rcases family_descends (prefixWord ++ tailWord_707499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707513 : List Nat := [1, 2, 1, 4, 2, 3, 1, 3, 1, 1, 4]
def baseStart_707513 : Nat := 118140960795 + 707513 * 2 ^ 59
def prefixEnd_707513 : Nat := 4983230072969 + 3 ^ 40 * 707513 * 2
def baseEnd_707513 : Nat := 363294238304595585833713

theorem tailTrace_707513 : CollatzResearch.WordTrace tailWord_707513 prefixEnd_707513 363294238304595585833713 := by
  unfold tailWord_707513
  simp only [CollatzResearch.WordTrace]
  refine ⟨25805119085808709445455193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17203412723872472963636795 25805119085808709445455193)
  ·
    refine ⟨19353839314356532084091395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25805119085808709445455193 19353839314356532084091395)
    ·
      refine ⟨29030758971534798126137093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19353839314356532084091395 29030758971534798126137093)
      ·
        refine ⟨5443267307162774648650705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29030758971534798126137093 5443267307162774648650705)
        ·
          refine ⟨4082450480372080986488029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5443267307162774648650705 4082450480372080986488029)
          ·
            refine ⟨1530918930139530369933011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4082450480372080986488029 1530918930139530369933011)
            ·
              refine ⟨2296378395209295554899517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1530918930139530369933011 2296378395209295554899517)
              ·
                refine ⟨861141898203485833087319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2296378395209295554899517 861141898203485833087319)
                ·
                  refine ⟨1291712847305228749630979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 861141898203485833087319 1291712847305228749630979)
                  ·
                    refine ⟨1937569270957843124446469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1291712847305228749630979 1937569270957843124446469)
                    ·
                      refine ⟨363294238304595585833713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1937569270957843124446469 363294238304595585833713)
                      ·
                        rfl

theorem cell23_707513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_707513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707513 prefixEnd_707513 := by exact prefixLift 707513
  have htrace : WordTrace (prefixWord ++ tailWord_707513) baseStart_707513 baseEnd_707513 := by
    simpa [prefixWord, tailWord_707513, baseEnd_707513] using wordTrace_append hprefix tailTrace_707513
  have hstable : (prefixWord ++ tailWord_707513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707513).length < 2 ^ (prefixWord ++ tailWord_707513).sum := by decide
  have hdescent : baseEnd_707513 < baseStart_707513 := by decide
  rcases family_descends (prefixWord ++ tailWord_707513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707570 : List Nat := [3, 2, 1, 5, 2, 1, 9]
def baseStart_707570 : Nat := 118140960795 + 707570 * 2 ^ 59
def prefixEnd_707570 : Nat := 4983230072969 + 3 ^ 40 * 707570 * 2
def baseEnd_707570 : Nat := 4485475391381504479271

theorem tailTrace_707570 : CollatzResearch.WordTrace tailWord_707570 prefixEnd_707570 4485475391381504479271 := by
  unfold tailWord_707570
  simp only [CollatzResearch.WordTrace]
  refine ⟨6451799511650552045070041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17204798697734805453520109 6451799511650552045070041)
  ·
    refine ⟨4838849633737914033802531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6451799511650552045070041 4838849633737914033802531)
    ·
      refine ⟨7258274450606871050703797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4838849633737914033802531 7258274450606871050703797)
      ·
        refine ⟨680463229744394161003481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7258274450606871050703797 680463229744394161003481)
        ·
          refine ⟨510347422308295620752611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 680463229744394161003481 510347422308295620752611)
          ·
            refine ⟨765521133462443431128917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510347422308295620752611 765521133462443431128917)
            ·
              refine ⟨4485475391381504479271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 765521133462443431128917 4485475391381504479271)
              ·
                rfl

theorem cell23_707570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 9].length) (baseStart_707570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707570 prefixEnd_707570 := by exact prefixLift 707570
  have htrace : WordTrace (prefixWord ++ tailWord_707570) baseStart_707570 baseEnd_707570 := by
    simpa [prefixWord, tailWord_707570, baseEnd_707570] using wordTrace_append hprefix tailTrace_707570
  have hstable : (prefixWord ++ tailWord_707570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707570).length < 2 ^ (prefixWord ++ tailWord_707570).sum := by decide
  have hdescent : baseEnd_707570 < baseStart_707570 := by decide
  rcases family_descends (prefixWord ++ tailWord_707570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707603 : List Nat := [1, 1, 1, 2, 1, 4, 1, 5, 1, 4, 2]
def baseStart_707603 : Nat := 118140960795 + 707603 * 2 ^ 59
def prefixEnd_707603 : Nat := 4983230072969 + 3 ^ 40 * 707603 * 2
def baseEnd_707603 : Nat := 363340451563500233708299

theorem tailTrace_707603 : CollatzResearch.WordTrace tailWord_707603 prefixEnd_707603 363340451563500233708299 := by
  unfold tailWord_707603
  simp only [CollatzResearch.WordTrace]
  refine ⟨25808401655482654816231463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17205601103655103210820975 25808401655482654816231463)
  ·
    refine ⟨38712602483223982224347195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25808401655482654816231463 38712602483223982224347195)
    ·
      refine ⟨58068903724835973336520793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38712602483223982224347195 58068903724835973336520793)
      ·
        refine ⟨43551677793626980002390595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58068903724835973336520793 43551677793626980002390595)
        ·
          refine ⟨65327516690440470003585893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43551677793626980002390595 65327516690440470003585893)
          ·
            refine ⟨12248909379457588125672355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65327516690440470003585893 12248909379457588125672355)
            ·
              refine ⟨18373364069186382188508533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12248909379457588125672355 18373364069186382188508533)
              ·
                refine ⟨1722502881486223330172675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18373364069186382188508533 1722502881486223330172675)
                ·
                  refine ⟨2583754322229334995259013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1722502881486223330172675 2583754322229334995259013)
                  ·
                    refine ⟨484453935418000311611065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2583754322229334995259013 484453935418000311611065)
                    ·
                      refine ⟨363340451563500233708299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 484453935418000311611065 363340451563500233708299)
                      ·
                        rfl

theorem cell23_707603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 4, 2].length) (baseStart_707603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707603 prefixEnd_707603 := by exact prefixLift 707603
  have htrace : WordTrace (prefixWord ++ tailWord_707603) baseStart_707603 baseEnd_707603 := by
    simpa [prefixWord, tailWord_707603, baseEnd_707603] using wordTrace_append hprefix tailTrace_707603
  have hstable : (prefixWord ++ tailWord_707603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707603).length < 2 ^ (prefixWord ++ tailWord_707603).sum := by decide
  have hdescent : baseEnd_707603 < baseStart_707603 := by decide
  rcases family_descends (prefixWord ++ tailWord_707603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707607 : List Nat := [1, 1, 3, 5, 1, 1, 3, 2, 1, 3, 2]
def baseStart_707607 : Nat := 118140960795 + 707607 * 2 ^ 59
def prefixEnd_707607 : Nat := 4983230072969 + 3 ^ 40 * 707607 * 2
def baseEnd_707607 : Nat := 363342505486118218058281

theorem tailTrace_707607 : CollatzResearch.WordTrace tailWord_707607 prefixEnd_707607 363342505486118218058281 := by
  unfold tailWord_707607
  simp only [CollatzResearch.WordTrace]
  refine ⟨25808547547468163499377075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17205698364978775666251383 25808547547468163499377075)
  ·
    refine ⟨38712821321202245249065613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25808547547468163499377075 38712821321202245249065613)
    ·
      refine ⟨14517307995450841968399605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38712821321202245249065613 14517307995450841968399605)
      ·
        refine ⟨1360997624573516434537463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14517307995450841968399605 1360997624573516434537463)
        ·
          refine ⟨2041496436860274651806195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1360997624573516434537463 2041496436860274651806195)
          ·
            refine ⟨3062244655290411977709293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2041496436860274651806195 3062244655290411977709293)
            ·
              refine ⟨1148341745733904491640985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3062244655290411977709293 1148341745733904491640985)
              ·
                refine ⟨861256309300428368730739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1148341745733904491640985 861256309300428368730739)
                ·
                  refine ⟨1291884463950642553096109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 861256309300428368730739 1291884463950642553096109)
                  ·
                    refine ⟨484456673981490957411041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1291884463950642553096109 484456673981490957411041)
                    ·
                      refine ⟨363342505486118218058281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 484456673981490957411041 363342505486118218058281)
                      ·
                        rfl

theorem cell23_707607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_707607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707607 prefixEnd_707607 := by exact prefixLift 707607
  have htrace : WordTrace (prefixWord ++ tailWord_707607) baseStart_707607 baseEnd_707607 := by
    simpa [prefixWord, tailWord_707607, baseEnd_707607] using wordTrace_append hprefix tailTrace_707607
  have hstable : (prefixWord ++ tailWord_707607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707607).length < 2 ^ (prefixWord ++ tailWord_707607).sum := by decide
  have hdescent : baseEnd_707607 < baseStart_707607 := by decide
  rcases family_descends (prefixWord ++ tailWord_707607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707620 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 3, 4, 2]
def baseStart_707620 : Nat := 118140960795 + 707620 * 2 ^ 59
def prefixEnd_707620 : Nat := 4983230072969 + 3 ^ 40 * 707620 * 2
def baseEnd_707620 : Nat := 363349180734626667195721

theorem tailTrace_707620 : CollatzResearch.WordTrace tailWord_707620 prefixEnd_707620 363349180734626667195721 := by
  unfold tailWord_707620
  simp only [CollatzResearch.WordTrace]
  refine ⟨12904510848210533359800157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17206014464280711146400209 12904510848210533359800157)
  ·
    refine ⟨4839191568078950009925059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12904510848210533359800157 4839191568078950009925059)
    ·
      refine ⟨7258787352118425014887589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4839191568078950009925059 7258787352118425014887589)
      ·
        refine ⟨1361022628522204690291423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7258787352118425014887589 1361022628522204690291423)
        ·
          refine ⟨2041533942783307035437135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1361022628522204690291423 2041533942783307035437135)
          ·
            refine ⟨3062300914174960553155703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2041533942783307035437135 3062300914174960553155703)
            ·
              refine ⟨4593451371262440829733555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3062300914174960553155703 4593451371262440829733555)
              ·
                refine ⟨6890177056893661244600333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4593451371262440829733555 6890177056893661244600333)
                ·
                  refine ⟨2583816396335122966725125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6890177056893661244600333 2583816396335122966725125)
                  ·
                    refine ⟨484465574312835556260961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2583816396335122966725125 484465574312835556260961)
                    ·
                      refine ⟨363349180734626667195721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 484465574312835556260961 363349180734626667195721)
                      ·
                        rfl

theorem cell23_707620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_707620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707620 prefixEnd_707620 := by exact prefixLift 707620
  have htrace : WordTrace (prefixWord ++ tailWord_707620) baseStart_707620 baseEnd_707620 := by
    simpa [prefixWord, tailWord_707620, baseEnd_707620] using wordTrace_append hprefix tailTrace_707620
  have hstable : (prefixWord ++ tailWord_707620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707620).length < 2 ^ (prefixWord ++ tailWord_707620).sum := by decide
  have hdescent : baseEnd_707620 < baseStart_707620 := by decide
  rcases family_descends (prefixWord ++ tailWord_707620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707654 : List Nat := [6, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2]
def baseStart_707654 : Nat := 118140960795 + 707654 * 2 ^ 59
def prefixEnd_707654 : Nat := 4983230072969 + 3 ^ 40 * 707654 * 2
def baseEnd_707654 : Nat := 363366639076879534170565

theorem tailTrace_707654 : CollatzResearch.WordTrace tailWord_707654 prefixEnd_707654 363366639076879534170565 := by
  unfold tailWord_707654
  simp only [CollatzResearch.WordTrace]
  refine ⟨806570680571809078948063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17206841185531927017558677 806570680571809078948063)
  ·
    refine ⟨1209856020857713618422095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 806570680571809078948063 1209856020857713618422095)
    ·
      refine ⟨1814784031286570427633143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1209856020857713618422095 1814784031286570427633143)
      ·
        refine ⟨2722176046929855641449715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1814784031286570427633143 2722176046929855641449715)
        ·
          refine ⟨4083264070394783462174573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2722176046929855641449715 4083264070394783462174573)
          ·
            refine ⟨1531224026398043798315465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4083264070394783462174573 1531224026398043798315465)
            ·
              refine ⟨1148418019798532848736599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1531224026398043798315465 1148418019798532848736599)
              ·
                refine ⟨1722627029697799273104899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1148418019798532848736599 1722627029697799273104899)
                ·
                  refine ⟨2583940544546698909657349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1722627029697799273104899 2583940544546698909657349)
                  ·
                    refine ⟨484488852102506045560753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2583940544546698909657349 484488852102506045560753)
                    ·
                      refine ⟨363366639076879534170565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 484488852102506045560753 363366639076879534170565)
                      ·
                        rfl

theorem cell23_707654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_707654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707654 prefixEnd_707654 := by exact prefixLift 707654
  have htrace : WordTrace (prefixWord ++ tailWord_707654) baseStart_707654 baseEnd_707654 := by
    simpa [prefixWord, tailWord_707654, baseEnd_707654] using wordTrace_append hprefix tailTrace_707654
  have hstable : (prefixWord ++ tailWord_707654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707654).length < 2 ^ (prefixWord ++ tailWord_707654).sum := by decide
  have hdescent : baseEnd_707654 < baseStart_707654 := by decide
  rcases family_descends (prefixWord ++ tailWord_707654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707656 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 1, 7]
def baseStart_707656 : Nat := 118140960795 + 707656 * 2 ^ 59
def prefixEnd_707656 : Nat := 4983230072969 + 3 ^ 40 * 707656 * 2
def baseEnd_707656 : Nat := 121122555346062842115185

theorem tailTrace_707656 : CollatzResearch.WordTrace tailWord_707656 prefixEnd_707656 121122555346062842115185 := by
  unfold tailWord_707656
  simp only [CollatzResearch.WordTrace]
  refine ⟨12905167362145322433955411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17206889816193763245273881 12905167362145322433955411)
  ·
    refine ⟨19357751043217983650933117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12905167362145322433955411 19357751043217983650933117)
    ·
      refine ⟨7259156641206743869099919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19357751043217983650933117 7259156641206743869099919)
      ·
        refine ⟨10888734961810115803649879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7259156641206743869099919 10888734961810115803649879)
        ·
          refine ⟨16333102442715173705474819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10888734961810115803649879 16333102442715173705474819)
          ·
            refine ⟨24499653664072760558212229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16333102442715173705474819 24499653664072760558212229)
            ·
              refine ⟨4593685062013642604664793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24499653664072760558212229 4593685062013642604664793)
              ·
                refine ⟨3445263796510231953498595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4593685062013642604664793 3445263796510231953498595)
                ·
                  refine ⟨5167895694765347930247893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3445263796510231953498595 5167895694765347930247893)
                  ·
                    refine ⟨121122555346062842115185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5167895694765347930247893 121122555346062842115185)
                    ·
                      rfl

theorem cell23_707656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_707656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707656 prefixEnd_707656 := by exact prefixLift 707656
  have htrace : WordTrace (prefixWord ++ tailWord_707656) baseStart_707656 baseEnd_707656 := by
    simpa [prefixWord, tailWord_707656, baseEnd_707656] using wordTrace_append hprefix tailTrace_707656
  have hstable : (prefixWord ++ tailWord_707656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707656).length < 2 ^ (prefixWord ++ tailWord_707656).sum := by decide
  have hdescent : baseEnd_707656 < baseStart_707656 := by decide
  rcases family_descends (prefixWord ++ tailWord_707656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707688 : List Nat := [2, 1, 4, 4, 2, 1, 1, 2, 2, 2, 2]
def baseStart_707688 : Nat := 118140960795 + 707688 * 2 ^ 59
def prefixEnd_707688 : Nat := 4983230072969 + 3 ^ 40 * 707688 * 2
def baseEnd_707688 : Nat := 363384097419132401145409

theorem tailTrace_707688 : CollatzResearch.WordTrace tailWord_707688 prefixEnd_707688 363384097419132401145409 := by
  unfold tailWord_707688
  simp only [CollatzResearch.WordTrace]
  refine ⟨12905750930087357166537859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17207667906783142888717145 12905750930087357166537859)
  ·
    refine ⟨19358626395131035749806789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12905750930087357166537859 19358626395131035749806789)
    ·
      refine ⟨3629742449087069203088773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19358626395131035749806789 3629742449087069203088773)
      ·
        refine ⟨680576709203825475579145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3629742449087069203088773 680576709203825475579145)
        ·
          refine ⟨510432531902869106684359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 680576709203825475579145 510432531902869106684359)
          ·
            refine ⟨765648797854303660026539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510432531902869106684359 765648797854303660026539)
            ·
              refine ⟨1148473196781455490039809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 765648797854303660026539 1148473196781455490039809)
              ·
                refine ⟨861354897586091617529857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1148473196781455490039809 861354897586091617529857)
                ·
                  refine ⟨646016173189568713147393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 861354897586091617529857 646016173189568713147393)
                  ·
                    refine ⟨484512129892176534860545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 646016173189568713147393 484512129892176534860545)
                    ·
                      refine ⟨363384097419132401145409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 484512129892176534860545 363384097419132401145409)
                      ·
                        rfl

theorem cell23_707688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_707688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707688 prefixEnd_707688 := by exact prefixLift 707688
  have htrace : WordTrace (prefixWord ++ tailWord_707688) baseStart_707688 baseEnd_707688 := by
    simpa [prefixWord, tailWord_707688, baseEnd_707688] using wordTrace_append hprefix tailTrace_707688
  have hstable : (prefixWord ++ tailWord_707688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707688).length < 2 ^ (prefixWord ++ tailWord_707688).sum := by decide
  have hdescent : baseEnd_707688 < baseStart_707688 := by decide
  rcases family_descends (prefixWord ++ tailWord_707688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707730 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_707730 : Nat := 118140960795 + 707730 * 2 ^ 59
def prefixEnd_707730 : Nat := 4983230072969 + 3 ^ 40 * 707730 * 2
def baseEnd_707730 : Nat := 363405663606621236820215

theorem tailTrace_707730 : CollatzResearch.WordTrace tailWord_707730 prefixEnd_707730 363405663606621236820215 := by
  unfold tailWord_707730
  simp only [CollatzResearch.WordTrace]
  refine ⟨6453258431505638876526161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17208689150681703670736429 6453258431505638876526161)
  ·
    refine ⟨4839943823629229157394621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6453258431505638876526161 4839943823629229157394621)
    ·
      refine ⟨1814978933860960934022983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4839943823629229157394621 1814978933860960934022983)
      ·
        refine ⟨2722468400791441401034475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1814978933860960934022983 2722468400791441401034475)
        ·
          refine ⟨4083702601187162101551713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2722468400791441401034475 4083702601187162101551713)
          ·
            refine ⟨3062776950890371576163785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4083702601187162101551713 3062776950890371576163785)
            ·
              refine ⟨2297082713167778682122839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3062776950890371576163785 2297082713167778682122839)
              ·
                refine ⟨3445624069751668023184259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2297082713167778682122839 3445624069751668023184259)
                ·
                  refine ⟨5168436104627502034776389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3445624069751668023184259 5168436104627502034776389)
                  ·
                    refine ⟨969081769617656631520573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5168436104627502034776389 969081769617656631520573)
                    ·
                      refine ⟨363405663606621236820215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 969081769617656631520573 363405663606621236820215)
                      ·
                        rfl

theorem cell23_707730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_707730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707730 prefixEnd_707730 := by exact prefixLift 707730
  have htrace : WordTrace (prefixWord ++ tailWord_707730) baseStart_707730 baseEnd_707730 := by
    simpa [prefixWord, tailWord_707730, baseEnd_707730] using wordTrace_append hprefix tailTrace_707730
  have hstable : (prefixWord ++ tailWord_707730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707730).length < 2 ^ (prefixWord ++ tailWord_707730).sum := by decide
  have hdescent : baseEnd_707730 < baseStart_707730 := by decide
  rcases family_descends (prefixWord ++ tailWord_707730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707754 : List Nat := [3, 1, 5, 1, 1, 3, 1, 1, 3, 4]
def baseStart_707754 : Nat := 118140960795 + 707754 * 2 ^ 59
def prefixEnd_707754 : Nat := 4983230072969 + 3 ^ 40 * 707754 * 2
def baseEnd_707754 : Nat := 121139329047443047640035

theorem tailTrace_707754 : CollatzResearch.WordTrace tailWord_707754 prefixEnd_707754 121139329047443047640035 := by
  unfold tailWord_707754
  simp only [CollatzResearch.WordTrace]
  refine ⟨6453477269483901901244579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17209272718623738403318877 6453477269483901901244579)
  ·
    refine ⟨9680215904225852851866869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6453477269483901901244579 9680215904225852851866869)
    ·
      refine ⟨907520241021173704862519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9680215904225852851866869 907520241021173704862519)
      ·
        refine ⟨1361280361531760557293779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 907520241021173704862519 1361280361531760557293779)
        ·
          refine ⟨2041920542297640835940669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1361280361531760557293779 2041920542297640835940669)
          ·
            refine ⟨765720203361615313477751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2041920542297640835940669 765720203361615313477751)
            ·
              refine ⟨1148580305042422970216627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 765720203361615313477751 1148580305042422970216627)
              ·
                refine ⟨1722870457563634455324941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1148580305042422970216627 1722870457563634455324941)
                ·
                  refine ⟨646076421586362920746853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1722870457563634455324941 646076421586362920746853)
                  ·
                    refine ⟨121139329047443047640035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 646076421586362920746853 121139329047443047640035)
                    ·
                      rfl

theorem cell23_707754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_707754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707754 prefixEnd_707754 := by exact prefixLift 707754
  have htrace : WordTrace (prefixWord ++ tailWord_707754) baseStart_707754 baseEnd_707754 := by
    simpa [prefixWord, tailWord_707754, baseEnd_707754] using wordTrace_append hprefix tailTrace_707754
  have hstable : (prefixWord ++ tailWord_707754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707754).length < 2 ^ (prefixWord ++ tailWord_707754).sum := by decide
  have hdescent : baseEnd_707754 < baseStart_707754 := by decide
  rcases family_descends (prefixWord ++ tailWord_707754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707770 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2]
def baseStart_707770 : Nat := 118140960795 + 707770 * 2 ^ 59
def prefixEnd_707770 : Nat := 4983230072969 + 3 ^ 40 * 707770 * 2
def baseEnd_707770 : Nat := 363426202832801080320031

theorem tailTrace_707770 : CollatzResearch.WordTrace tailWord_707770 prefixEnd_707770 363426202832801080320031 := by
  unfold tailWord_707770
  simp only [CollatzResearch.WordTrace]
  refine ⟨6453623161469410584390191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17209661763918428225040509 6453623161469410584390191)
  ·
    refine ⟨9680434742204115876585287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6453623161469410584390191 9680434742204115876585287)
    ·
      refine ⟨14520652113306173814877931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9680434742204115876585287 14520652113306173814877931)
      ·
        refine ⟨21780978169959260722316897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14520652113306173814877931 21780978169959260722316897)
        ·
          refine ⟨16335733627469445541737673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21780978169959260722316897 16335733627469445541737673)
          ·
            refine ⟨12251800220602084156303255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16335733627469445541737673 12251800220602084156303255)
            ·
              refine ⟨18377700330903126234454883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12251800220602084156303255 18377700330903126234454883)
              ·
                refine ⟨27566550496354689351682325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18377700330903126234454883 27566550496354689351682325)
                ·
                  refine ⟨1292182054516626063360109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27566550496354689351682325 1292182054516626063360109)
                  ·
                    refine ⟨484568270443734773760041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1292182054516626063360109 484568270443734773760041)
                    ·
                      refine ⟨363426202832801080320031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 484568270443734773760041 363426202832801080320031)
                      ·
                        rfl

theorem cell23_707770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2].length) (baseStart_707770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707770 prefixEnd_707770 := by exact prefixLift 707770
  have htrace : WordTrace (prefixWord ++ tailWord_707770) baseStart_707770 baseEnd_707770 := by
    simpa [prefixWord, tailWord_707770, baseEnd_707770] using wordTrace_append hprefix tailTrace_707770
  have hstable : (prefixWord ++ tailWord_707770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707770).length < 2 ^ (prefixWord ++ tailWord_707770).sum := by decide
  have hdescent : baseEnd_707770 < baseStart_707770 := by decide
  rcases family_descends (prefixWord ++ tailWord_707770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707794 : List Nat := [3, 2, 2, 2, 1, 1, 2, 5, 1, 1, 3]
def baseStart_707794 : Nat := 118140960795 + 707794 * 2 ^ 59
def prefixEnd_707794 : Nat := 4983230072969 + 3 ^ 40 * 707794 * 2
def baseEnd_707794 : Nat := 363438526368508986419921

theorem tailTrace_707794 : CollatzResearch.WordTrace tailWord_707794 prefixEnd_707794 363438526368508986419921 := by
  unfold tailWord_707794
  simp only [CollatzResearch.WordTrace]
  refine ⟨6453841999447673609108609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17210245331860462957622957 6453841999447673609108609)
  ·
    refine ⟨4840381499585755206831457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6453841999447673609108609 4840381499585755206831457)
    ·
      refine ⟨3630286124689316405123593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4840381499585755206831457 3630286124689316405123593)
      ·
        refine ⟨2722714593516987303842695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3630286124689316405123593 2722714593516987303842695)
        ·
          refine ⟨4084071890275480955764043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2722714593516987303842695 4084071890275480955764043)
          ·
            refine ⟨6126107835413221433646065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4084071890275480955764043 6126107835413221433646065)
            ·
              refine ⟨4594580876559916075234549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6126107835413221433646065 4594580876559916075234549)
              ·
                refine ⟨430741957177492132053239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4594580876559916075234549 430741957177492132053239)
                ·
                  refine ⟨646112935766238198079859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 430741957177492132053239 646112935766238198079859)
                  ·
                    refine ⟨969169403649357297119789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 646112935766238198079859 969169403649357297119789)
                    ·
                      refine ⟨363438526368508986419921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 969169403649357297119789 363438526368508986419921)
                      ·
                        rfl

theorem cell23_707794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_707794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707794 prefixEnd_707794 := by exact prefixLift 707794
  have htrace : WordTrace (prefixWord ++ tailWord_707794) baseStart_707794 baseEnd_707794 := by
    simpa [prefixWord, tailWord_707794, baseEnd_707794] using wordTrace_append hprefix tailTrace_707794
  have hstable : (prefixWord ++ tailWord_707794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707794).length < 2 ^ (prefixWord ++ tailWord_707794).sum := by decide
  have hdescent : baseEnd_707794 < baseStart_707794 := by decide
  rcases family_descends (prefixWord ++ tailWord_707794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707820 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 3]
def baseStart_707820 : Nat := 118140960795 + 707820 * 2 ^ 59
def prefixEnd_707820 : Nat := 4983230072969 + 3 ^ 40 * 707820 * 2
def baseEnd_707820 : Nat := 363451876865525884694801

theorem tailTrace_707820 : CollatzResearch.WordTrace tailWord_707820 prefixEnd_707820 363451876865525884694801 := by
  unfold tailWord_707820
  simp only [CollatzResearch.WordTrace]
  refine ⟨12908158147848250438440457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17210877530464333917920609 12908158147848250438440457)
  ·
    refine ⟨9681118610886187828830343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12908158147848250438440457 9681118610886187828830343)
    ·
      refine ⟨14521677916329281743245515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9681118610886187828830343 14521677916329281743245515)
      ·
        refine ⟨21782516874493922614868273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14521677916329281743245515 21782516874493922614868273)
        ·
          refine ⟨16336887655870441961151205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21782516874493922614868273 16336887655870441961151205)
          ·
            refine ⟨3063166435475707867715851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16336887655870441961151205 3063166435475707867715851)
            ·
              refine ⟨4594749653213561801573777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3063166435475707867715851 4594749653213561801573777)
              ·
                refine ⟨3446062239910171351180333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4594749653213561801573777 3446062239910171351180333)
                ·
                  refine ⟨1292273339966314256692625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3446062239910171351180333 1292273339966314256692625)
                  ·
                    refine ⟨969205004974735692519469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1292273339966314256692625 969205004974735692519469)
                    ·
                      refine ⟨363451876865525884694801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 969205004974735692519469 363451876865525884694801)
                      ·
                        rfl

theorem cell23_707820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 3].length) (baseStart_707820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707820 prefixEnd_707820 := by exact prefixLift 707820
  have htrace : WordTrace (prefixWord ++ tailWord_707820) baseStart_707820 baseEnd_707820 := by
    simpa [prefixWord, tailWord_707820, baseEnd_707820] using wordTrace_append hprefix tailTrace_707820
  have hstable : (prefixWord ++ tailWord_707820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707820).length < 2 ^ (prefixWord ++ tailWord_707820).sum := by decide
  have hdescent : baseEnd_707820 < baseStart_707820 := by decide
  rcases family_descends (prefixWord ++ tailWord_707820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707828 : List Nat := [2, 6, 1, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_707828 : Nat := 118140960795 + 707828 * 2 ^ 59
def prefixEnd_707828 : Nat := 4983230072969 + 3 ^ 40 * 707828 * 2
def baseEnd_707828 : Nat := 363455984710761853394765

theorem tailTrace_707828 : CollatzResearch.WordTrace tailWord_707828 prefixEnd_707828 363455984710761853394765 := by
  unfold tailWord_707828
  simp only [CollatzResearch.WordTrace]
  refine ⟨12908304039833759121586069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17211072053111678828781425 12908304039833759121586069)
  ·
    refine ⟨605076751867207458824347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12908304039833759121586069 605076751867207458824347)
    ·
      refine ⟨907615127800811188236521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 605076751867207458824347 907615127800811188236521)
      ·
        refine ⟨680711345850608391177391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 907615127800811188236521 680711345850608391177391)
        ·
          refine ⟨1021067018775912586766087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 680711345850608391177391 1021067018775912586766087)
          ·
            refine ⟨1531600528163868880149131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021067018775912586766087 1531600528163868880149131)
            ·
              refine ⟨2297400792245803320223697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1531600528163868880149131 2297400792245803320223697)
              ·
                refine ⟨1723050594184352490167773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2297400792245803320223697 1723050594184352490167773)
                ·
                  refine ⟨646143972819132183812915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1723050594184352490167773 646143972819132183812915)
                  ·
                    refine ⟨969215959228698275719373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 646143972819132183812915 969215959228698275719373)
                    ·
                      refine ⟨363455984710761853394765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 969215959228698275719373 363455984710761853394765)
                      ·
                        rfl

theorem cell23_707828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_707828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707828 prefixEnd_707828 := by exact prefixLift 707828
  have htrace : WordTrace (prefixWord ++ tailWord_707828) baseStart_707828 baseEnd_707828 := by
    simpa [prefixWord, tailWord_707828, baseEnd_707828] using wordTrace_append hprefix tailTrace_707828
  have hstable : (prefixWord ++ tailWord_707828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707828).length < 2 ^ (prefixWord ++ tailWord_707828).sum := by decide
  have hdescent : baseEnd_707828 < baseStart_707828 := by decide
  rcases family_descends (prefixWord ++ tailWord_707828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707851 : List Nat := [1, 1, 1, 1, 5, 4, 2, 3, 1, 2, 2]
def baseStart_707851 : Nat := 118140960795 + 707851 * 2 ^ 59
def prefixEnd_707851 : Nat := 4983230072969 + 3 ^ 40 * 707851 * 2
def baseEnd_707851 : Nat := 363467794765815263407159

theorem tailTrace_707851 : CollatzResearch.WordTrace tailWord_707851 prefixEnd_707851 363467794765815263407159 := by
  unfold tailWord_707851
  simp only [CollatzResearch.WordTrace]
  refine ⟨25817446958584193171259407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17211631305722795447506271 25817446958584193171259407)
  ·
    refine ⟨38726170437876289756889111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25817446958584193171259407 38726170437876289756889111)
    ·
      refine ⟨58089255656814434635333667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38726170437876289756889111 58089255656814434635333667)
      ·
        refine ⟨87133883485221651953000501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58089255656814434635333667 87133883485221651953000501)
        ·
          refine ⟨8168801576739529870593797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87133883485221651953000501 8168801576739529870593797)
          ·
            refine ⟨1531650295638661850736337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8168801576739529870593797 1531650295638661850736337)
            ·
              refine ⟨1148737721728996388052253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1531650295638661850736337 1148737721728996388052253)
              ·
                refine ⟨430776645648373645519595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1148737721728996388052253 430776645648373645519595)
                ·
                  refine ⟨646164968472560468279393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 430776645648373645519595 646164968472560468279393)
                  ·
                    refine ⟨484623726354420351209545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 646164968472560468279393 484623726354420351209545)
                    ·
                      refine ⟨363467794765815263407159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 484623726354420351209545 363467794765815263407159)
                      ·
                        rfl

theorem cell23_707851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 1, 2, 2].length) (baseStart_707851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707851 prefixEnd_707851 := by exact prefixLift 707851
  have htrace : WordTrace (prefixWord ++ tailWord_707851) baseStart_707851 baseEnd_707851 := by
    simpa [prefixWord, tailWord_707851, baseEnd_707851] using wordTrace_append hprefix tailTrace_707851
  have hstable : (prefixWord ++ tailWord_707851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707851).length < 2 ^ (prefixWord ++ tailWord_707851).sum := by decide
  have hdescent : baseEnd_707851 < baseStart_707851 := by decide
  rcases family_descends (prefixWord ++ tailWord_707851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707854 : List Nat := [4, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3]
def baseStart_707854 : Nat := 118140960795 + 707854 * 2 ^ 59
def prefixEnd_707854 : Nat := 4983230072969 + 3 ^ 40 * 707854 * 2
def baseEnd_707854 : Nat := 363469335207778751669645

theorem tailTrace_707854 : CollatzResearch.WordTrace tailWord_707854 prefixEnd_707854 363469335207778751669645 := by
  unfold tailWord_707854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3227194547196665585452327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17211704251715549789079077 3227194547196665585452327)
  ·
    refine ⟨4840791820794998378178491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3227194547196665585452327 4840791820794998378178491)
    ·
      refine ⟨7261187731192497567267737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4840791820794998378178491 7261187731192497567267737)
      ·
        refine ⟨5445890798394373175450803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7261187731192497567267737 5445890798394373175450803)
        ·
          refine ⟨8168836197591559763176205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5445890798394373175450803 8168836197591559763176205)
          ·
            refine ⟨3063313574096834911191077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8168836197591559763176205 3063313574096834911191077)
            ·
              refine ⟨574371295143156545848327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3063313574096834911191077 574371295143156545848327)
              ·
                refine ⟨861556942714734818772491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 574371295143156545848327 861556942714734818772491)
                ·
                  refine ⟨1292335414072102228158737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 861556942714734818772491 1292335414072102228158737)
                  ·
                    refine ⟨969251560554076671119053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1292335414072102228158737 969251560554076671119053)
                    ·
                      refine ⟨363469335207778751669645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 969251560554076671119053 363469335207778751669645)
                      ·
                        rfl

theorem cell23_707854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_707854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707854 prefixEnd_707854 := by exact prefixLift 707854
  have htrace : WordTrace (prefixWord ++ tailWord_707854) baseStart_707854 baseEnd_707854 := by
    simpa [prefixWord, tailWord_707854, baseEnd_707854] using wordTrace_append hprefix tailTrace_707854
  have hstable : (prefixWord ++ tailWord_707854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707854).length < 2 ^ (prefixWord ++ tailWord_707854).sum := by decide
  have hdescent : baseEnd_707854 < baseStart_707854 := by decide
  rcases family_descends (prefixWord ++ tailWord_707854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707913 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 9]
def baseStart_707913 : Nat := 118140960795 + 707913 * 2 ^ 59
def prefixEnd_707913 : Nat := 4983230072969 + 3 ^ 40 * 707913 * 2
def baseEnd_707913 : Nat := 40388847840710446759097

theorem tailTrace_707913 : CollatzResearch.WordTrace tailWord_707913 prefixEnd_707913 40388847840710446759097 := by
  unfold tailWord_707913
  simp only [CollatzResearch.WordTrace]
  refine ⟨25819708284359577760016393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17213138856239718506677595 25819708284359577760016393)
  ·
    refine ⟨19364781213269683320012295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25819708284359577760016393 19364781213269683320012295)
    ·
      refine ⟨29047171819904524980018443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19364781213269683320012295 29047171819904524980018443)
      ·
        refine ⟨43570757729856787470027665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29047171819904524980018443 43570757729856787470027665)
        ·
          refine ⟨32678068297392590602520749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43570757729856787470027665 32678068297392590602520749)
          ·
            refine ⟨12254275611522221475945281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32678068297392590602520749 12254275611522221475945281)
            ·
              refine ⟨9190706708641666106958961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12254275611522221475945281 9190706708641666106958961)
              ·
                refine ⟨6893030031481249580219221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9190706708641666106958961 6893030031481249580219221)
                ·
                  refine ⟨40388847840710446759097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6893030031481249580219221 40388847840710446759097)
                  ·
                    rfl

theorem cell23_707913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 9].length) (baseStart_707913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707913 prefixEnd_707913 := by exact prefixLift 707913
  have htrace : WordTrace (prefixWord ++ tailWord_707913) baseStart_707913 baseEnd_707913 := by
    simpa [prefixWord, tailWord_707913, baseEnd_707913] using wordTrace_append hprefix tailTrace_707913
  have hstable : (prefixWord ++ tailWord_707913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707913).length < 2 ^ (prefixWord ++ tailWord_707913).sum := by decide
  have hdescent : baseEnd_707913 < baseStart_707913 := by decide
  rcases family_descends (prefixWord ++ tailWord_707913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707923 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 7]
def baseStart_707923 : Nat := 118140960795 + 707923 * 2 ^ 59
def prefixEnd_707923 : Nat := 4983230072969 + 3 ^ 40 * 707923 * 2
def baseEnd_707923 : Nat := 363504765372938981706827

theorem tailTrace_707923 : CollatzResearch.WordTrace tailWord_707923 prefixEnd_707923 363504765372938981706827 := by
  unfold tailWord_707923
  simp only [CollatzResearch.WordTrace]
  refine ⟨25820073014323349467880423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17213382009548899645253615 25820073014323349467880423)
  ·
    refine ⟨38730109521485024201820635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25820073014323349467880423 38730109521485024201820635)
    ·
      refine ⟨58095164282227536302730953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38730109521485024201820635 58095164282227536302730953)
      ·
        refine ⟨43571373211670652227048215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58095164282227536302730953 43571373211670652227048215)
        ·
          refine ⟨65357059817505978340572323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43571373211670652227048215 65357059817505978340572323)
          ·
            refine ⟨98035589726258967510858485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65357059817505978340572323 98035589726258967510858485)
            ·
              refine ⟨9190836536836778204142983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98035589726258967510858485 9190836536836778204142983)
              ·
                refine ⟨13786254805255167306214475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9190836536836778204142983 13786254805255167306214475)
                ·
                  refine ⟨20679382207882750959321713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13786254805255167306214475 20679382207882750959321713)
                  ·
                    refine ⟨15509536655912063219491285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20679382207882750959321713 15509536655912063219491285)
                    ·
                      refine ⟨363504765372938981706827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15509536655912063219491285 363504765372938981706827)
                      ·
                        rfl

theorem cell23_707923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_707923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707923 prefixEnd_707923 := by exact prefixLift 707923
  have htrace : WordTrace (prefixWord ++ tailWord_707923) baseStart_707923 baseEnd_707923 := by
    simpa [prefixWord, tailWord_707923, baseEnd_707923] using wordTrace_append hprefix tailTrace_707923
  have hstable : (prefixWord ++ tailWord_707923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707923).length < 2 ^ (prefixWord ++ tailWord_707923).sum := by decide
  have hdescent : baseEnd_707923 < baseStart_707923 := by decide
  rcases family_descends (prefixWord ++ tailWord_707923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707924 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 4, 2, 2]
def baseStart_707924 : Nat := 118140960795 + 707924 * 2 ^ 59
def prefixEnd_707924 : Nat := 4983230072969 + 3 ^ 40 * 707924 * 2
def baseEnd_707924 : Nat := 363505278853593477794323

theorem tailTrace_707924 : CollatzResearch.WordTrace tailWord_707924 prefixEnd_707924 363505278853593477794323 := by
  unfold tailWord_707924
  simp only [CollatzResearch.WordTrace]
  refine ⟨12910054743659863319333413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17213406324879817759111217 12910054743659863319333413)
  ·
    refine ⟨2420635264436224372375015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12910054743659863319333413 2420635264436224372375015)
    ·
      refine ⟨3630952896654336558562523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2420635264436224372375015 3630952896654336558562523)
      ·
        refine ⟨5446429344981504837843785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3630952896654336558562523 5446429344981504837843785)
        ·
          refine ⟨4084822008736128628382839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5446429344981504837843785 4084822008736128628382839)
          ·
            refine ⟨6127233013104192942574259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4084822008736128628382839 6127233013104192942574259)
            ·
              refine ⟨9190849519656289413861389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6127233013104192942574259 9190849519656289413861389)
              ·
                refine ⟨3446568569871108530198021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9190849519656289413861389 3446568569871108530198021)
                ·
                  refine ⟨646231606850832849412129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3446568569871108530198021 646231606850832849412129)
                  ·
                    refine ⟨484673705138124637059097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 646231606850832849412129 484673705138124637059097)
                    ·
                      refine ⟨363505278853593477794323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 484673705138124637059097 363505278853593477794323)
                      ·
                        rfl

theorem cell23_707924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_707924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707924 prefixEnd_707924 := by exact prefixLift 707924
  have htrace : WordTrace (prefixWord ++ tailWord_707924) baseStart_707924 baseEnd_707924 := by
    simpa [prefixWord, tailWord_707924, baseEnd_707924] using wordTrace_append hprefix tailTrace_707924
  have hstable : (prefixWord ++ tailWord_707924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707924).length < 2 ^ (prefixWord ++ tailWord_707924).sum := by decide
  have hdescent : baseEnd_707924 < baseStart_707924 := by decide
  rcases family_descends (prefixWord ++ tailWord_707924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707930 : List Nat := [3, 1, 1, 2, 1, 2, 5, 1, 7]
def baseStart_707930 : Nat := 118140960795 + 707930 * 2 ^ 59
def prefixEnd_707930 : Nat := 4983230072969 + 3 ^ 40 * 707930 * 2
def baseEnd_707930 : Nat := 40389817748613383813255

theorem tailTrace_707930 : CollatzResearch.WordTrace tailWord_707930 prefixEnd_707930 40389817748613383813255 := by
  unfold tailWord_707930
  simp only [CollatzResearch.WordTrace]
  refine ⟨6455082081324497415846311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17213552216865326442256829 6455082081324497415846311)
  ·
    refine ⟨9682623121986746123769467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6455082081324497415846311 9682623121986746123769467)
    ·
      refine ⟨14523934682980119185654201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9682623121986746123769467 14523934682980119185654201)
      ·
        refine ⟨10892951012235089389240651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14523934682980119185654201 10892951012235089389240651)
        ·
          refine ⟨16339426518352634083860977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10892951012235089389240651 16339426518352634083860977)
          ·
            refine ⟨12254569888764475562895733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16339426518352634083860977 12254569888764475562895733)
            ·
              refine ⟨1148865927071669584021475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12254569888764475562895733 1148865927071669584021475)
              ·
                refine ⟨1723298890607504376032213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1148865927071669584021475 1723298890607504376032213)
                ·
                  refine ⟨40389817748613383813255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1723298890607504376032213 40389817748613383813255)
                  ·
                    rfl

theorem cell23_707930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 7].length) (baseStart_707930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_707930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_707930 prefixEnd_707930 := by exact prefixLift 707930
  have htrace : WordTrace (prefixWord ++ tailWord_707930) baseStart_707930 baseEnd_707930 := by
    simpa [prefixWord, tailWord_707930, baseEnd_707930] using wordTrace_append hprefix tailTrace_707930
  have hstable : (prefixWord ++ tailWord_707930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707930).length < 2 ^ (prefixWord ++ tailWord_707930).sum := by decide
  have hdescent : baseEnd_707930 < baseStart_707930 := by decide
  rcases family_descends (prefixWord ++ tailWord_707930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708017 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 1, 4, 3]
def baseStart_708017 : Nat := 118140960795 + 708017 * 2 ^ 59
def prefixEnd_708017 : Nat := 4983230072969 + 3 ^ 40 * 708017 * 2
def baseEnd_708017 : Nat := 363553032554461613931395

theorem tailTrace_708017 : CollatzResearch.WordTrace tailWord_708017 prefixEnd_708017 363553032554461613931395 := by
  unfold tailWord_708017
  simp only [CollatzResearch.WordTrace]
  refine ⟨25823501475982803521802305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17215667650655202347868203 25823501475982803521802305)
  ·
    refine ⟨19367626106987102641351729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25823501475982803521802305 19367626106987102641351729)
    ·
      refine ⟨14525719580240326981013797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19367626106987102641351729 14525719580240326981013797)
      ·
        refine ⟨2723572421295061308940087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14525719580240326981013797 2723572421295061308940087)
        ·
          refine ⟨4085358631942591963410131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2723572421295061308940087 4085358631942591963410131)
          ·
            refine ⟨6128037947913887945115197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4085358631942591963410131 6128037947913887945115197)
            ·
              refine ⟨2298014230467707979418199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6128037947913887945115197 2298014230467707979418199)
              ·
                refine ⟨3447021345701561969127299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2298014230467707979418199 3447021345701561969127299)
                ·
                  refine ⟨5170532018552342953690949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3447021345701561969127299 5170532018552342953690949)
                  ·
                    refine ⟨969474753478564303817053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5170532018552342953690949 969474753478564303817053)
                    ·
                      refine ⟨363553032554461613931395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 969474753478564303817053 363553032554461613931395)
                      ·
                        rfl

theorem cell23_708017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_708017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708017 prefixEnd_708017 := by exact prefixLift 708017
  have htrace : WordTrace (prefixWord ++ tailWord_708017) baseStart_708017 baseEnd_708017 := by
    simpa [prefixWord, tailWord_708017, baseEnd_708017] using wordTrace_append hprefix tailTrace_708017
  have hstable : (prefixWord ++ tailWord_708017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708017).length < 2 ^ (prefixWord ++ tailWord_708017).sum := by decide
  have hdescent : baseEnd_708017 < baseStart_708017 := by decide
  rcases family_descends (prefixWord ++ tailWord_708017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708024 : List Nat := [2, 1, 2, 1, 2, 2, 3, 5, 1, 4]
def baseStart_708024 : Nat := 118140960795 + 708024 * 2 ^ 59
def prefixEnd_708024 : Nat := 4983230072969 + 3 ^ 40 * 708024 * 2
def baseEnd_708024 : Nat := 121185542306347695514621

theorem tailTrace_708024 : CollatzResearch.WordTrace tailWord_708024 prefixEnd_708024 121185542306347695514621 := by
  unfold tailWord_708024
  simp only [CollatzResearch.WordTrace]
  refine ⟨12911878393478721858653563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17215837857971629144871417 12911878393478721858653563)
  ·
    refine ⟨19367817590218082787980345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12911878393478721858653563 19367817590218082787980345)
    ·
      refine ⟨14525863192663562090985259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19367817590218082787980345 14525863192663562090985259)
      ·
        refine ⟨21788794788995343136477889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14525863192663562090985259 21788794788995343136477889)
        ·
          refine ⟨16341596091746507352358417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21788794788995343136477889 16341596091746507352358417)
          ·
            refine ⟨12256197068809880514268813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16341596091746507352358417 12256197068809880514268813)
            ·
              refine ⟨4596073900803705192850805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12256197068809880514268813 4596073900803705192850805)
              ·
                refine ⟨430881928200347361829763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4596073900803705192850805 430881928200347361829763)
                ·
                  refine ⟨646322892300521042744645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 430881928200347361829763 646322892300521042744645)
                  ·
                    refine ⟨121185542306347695514621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 646322892300521042744645 121185542306347695514621)
                    ·
                      rfl

theorem cell23_708024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 1, 4].length) (baseStart_708024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708024 prefixEnd_708024 := by exact prefixLift 708024
  have htrace : WordTrace (prefixWord ++ tailWord_708024) baseStart_708024 baseEnd_708024 := by
    simpa [prefixWord, tailWord_708024, baseEnd_708024] using wordTrace_append hprefix tailTrace_708024
  have hstable : (prefixWord ++ tailWord_708024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708024).length < 2 ^ (prefixWord ++ tailWord_708024).sum := by decide
  have hdescent : baseEnd_708024 < baseStart_708024 := by decide
  rcases family_descends (prefixWord ++ tailWord_708024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708040 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 1, 1, 8]
def baseStart_708040 : Nat := 118140960795 + 708040 * 2 ^ 59
def prefixEnd_708040 : Nat := 4983230072969 + 3 ^ 40 * 708040 * 2
def baseEnd_708040 : Nat := 363564842609515023943789

theorem tailTrace_708040 : CollatzResearch.WordTrace tailWord_708040 prefixEnd_708040 363564842609515023943789 := by
  unfold tailWord_708040
  simp only [CollatzResearch.WordTrace]
  refine ⟨12912170177449739224944787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17216226903266318966593049 12912170177449739224944787)
  ·
    refine ⟨19368255266174608837417181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12912170177449739224944787 19368255266174608837417181)
    ·
      refine ⟨7263095724815478314031443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19368255266174608837417181 7263095724815478314031443)
      ·
        refine ⟨10894643587223217471047165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7263095724815478314031443 10894643587223217471047165)
        ·
          refine ⟨4085491345208706551642687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10894643587223217471047165 4085491345208706551642687)
          ·
            refine ⟨6128237017813059827464031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4085491345208706551642687 6128237017813059827464031)
            ·
              refine ⟨9192355526719589741196047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6128237017813059827464031 9192355526719589741196047)
              ·
                refine ⟨13788533290079384611794071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9192355526719589741196047 13788533290079384611794071)
                ·
                  refine ⟨20682799935119076917691107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13788533290079384611794071 20682799935119076917691107)
                  ·
                    refine ⟨31024199902678615376536661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20682799935119076917691107 31024199902678615376536661)
                    ·
                      refine ⟨363564842609515023943789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 31024199902678615376536661 363564842609515023943789)
                      ·
                        rfl

theorem cell23_708040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_708040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708040 prefixEnd_708040 := by exact prefixLift 708040
  have htrace : WordTrace (prefixWord ++ tailWord_708040) baseStart_708040 baseEnd_708040 := by
    simpa [prefixWord, tailWord_708040, baseEnd_708040] using wordTrace_append hprefix tailTrace_708040
  have hstable : (prefixWord ++ tailWord_708040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708040).length < 2 ^ (prefixWord ++ tailWord_708040).sum := by decide
  have hdescent : baseEnd_708040 < baseStart_708040 := by decide
  rcases family_descends (prefixWord ++ tailWord_708040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708098 : List Nat := [3, 4, 1, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_708098 : Nat := 118140960795 + 708098 * 2 ^ 59
def prefixEnd_708098 : Nat := 4983230072969 + 3 ^ 40 * 708098 * 2
def baseEnd_708098 : Nat := 363594624487475797018523

theorem tailTrace_708098 : CollatzResearch.WordTrace tailWord_708098 prefixEnd_708098 363594624487475797018523 := by
  unfold tailWord_708098
  simp only [CollatzResearch.WordTrace]
  refine ⟨6456613947172338588875237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17217637192459569570333965 6456613947172338588875237)
  ·
    refine ⟨1210615115094813485414107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6456613947172338588875237 1210615115094813485414107)
    ·
      refine ⟨1815922672642220228121161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1210615115094813485414107 1815922672642220228121161)
      ·
        refine ⟨1361942004481665171090871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1815922672642220228121161 1361942004481665171090871)
        ·
          refine ⟨2042913006722497756636307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1361942004481665171090871 2042913006722497756636307)
          ·
            refine ⟨3064369510083746634954461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2042913006722497756636307 3064369510083746634954461)
            ·
              refine ⟨1149138566281404988107923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3064369510083746634954461 1149138566281404988107923)
              ·
                refine ⟨1723707849422107482161885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1149138566281404988107923 1723707849422107482161885)
                ·
                  refine ⟨646390443533290305810707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1723707849422107482161885 646390443533290305810707)
                  ·
                    refine ⟨969585665299935458716061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 646390443533290305810707 969585665299935458716061)
                    ·
                      refine ⟨363594624487475797018523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 969585665299935458716061 363594624487475797018523)
                      ·
                        rfl

theorem cell23_708098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_708098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708098 prefixEnd_708098 := by exact prefixLift 708098
  have htrace : WordTrace (prefixWord ++ tailWord_708098) baseStart_708098 baseEnd_708098 := by
    simpa [prefixWord, tailWord_708098, baseEnd_708098] using wordTrace_append hprefix tailTrace_708098
  have hstable : (prefixWord ++ tailWord_708098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708098).length < 2 ^ (prefixWord ++ tailWord_708098).sum := by decide
  have hdescent : baseEnd_708098 < baseStart_708098 := by decide
  rcases family_descends (prefixWord ++ tailWord_708098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708117 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 1, 1, 6]
def baseStart_708117 : Nat := 118140960795 + 708117 * 2 ^ 59
def prefixEnd_708117 : Nat := 4983230072969 + 3 ^ 40 * 708117 * 2
def baseEnd_708117 : Nat := 363604380619911222680935

theorem tailTrace_708117 : CollatzResearch.WordTrace tailWord_708117 prefixEnd_708117 363604380619911222680935 := by
  unfold tailWord_708117
  simp only [CollatzResearch.WordTrace]
  refine ⟨25827148775620520600442605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17218099183747013733628403 25827148775620520600442605)
  ·
    refine ⟨9685180790857695225165977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25827148775620520600442605 9685180790857695225165977)
    ·
      refine ⟨7263885593143271418874483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9685180790857695225165977 7263885593143271418874483)
      ·
        refine ⟨10895828389714907128311725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7263885593143271418874483 10895828389714907128311725)
        ·
          refine ⟨4085935646143090173116897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10895828389714907128311725 4085935646143090173116897)
          ·
            refine ⟨3064451734607317629837673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4085935646143090173116897 3064451734607317629837673)
            ·
              refine ⟨2298338800955488222378255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3064451734607317629837673 2298338800955488222378255)
              ·
                refine ⟨3447508201433232333567383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2298338800955488222378255 3447508201433232333567383)
                ·
                  refine ⟨5171262302149848500351075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3447508201433232333567383 5171262302149848500351075)
                  ·
                    refine ⟨7756893453224772750526613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5171262302149848500351075 7756893453224772750526613)
                    ·
                      refine ⟨363604380619911222680935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7756893453224772750526613 363604380619911222680935)
                      ·
                        rfl

theorem cell23_708117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_708117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708117 prefixEnd_708117 := by exact prefixLift 708117
  have htrace : WordTrace (prefixWord ++ tailWord_708117) baseStart_708117 baseEnd_708117 := by
    simpa [prefixWord, tailWord_708117, baseEnd_708117] using wordTrace_append hprefix tailTrace_708117
  have hstable : (prefixWord ++ tailWord_708117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708117).length < 2 ^ (prefixWord ++ tailWord_708117).sum := by decide
  have hdescent : baseEnd_708117 < baseStart_708117 := by decide
  rcases family_descends (prefixWord ++ tailWord_708117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708124 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 3, 2, 3]
def baseStart_708124 : Nat := 118140960795 + 708124 * 2 ^ 59
def prefixEnd_708124 : Nat := 4983230072969 + 3 ^ 40 * 708124 * 2
def baseEnd_708124 : Nat := 363607974984492695293403

theorem tailTrace_708124 : CollatzResearch.WordTrace tailWord_708124 prefixEnd_708124 363607974984492695293403 := by
  unfold tailWord_708124
  simp only [CollatzResearch.WordTrace]
  refine ⟨12913702043297580397973713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17218269391063440530631617 12913702043297580397973713)
  ·
    refine ⟨9685276532473185298480285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12913702043297580397973713 9685276532473185298480285)
    ·
      refine ⟨3631978699677444486930107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9685276532473185298480285 3631978699677444486930107)
      ·
        refine ⟨5447968049516166730395161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3631978699677444486930107 5447968049516166730395161)
        ·
          refine ⟨4085976037137125047796371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5447968049516166730395161 4085976037137125047796371)
          ·
            refine ⟨6128964055705687571694557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4085976037137125047796371 6128964055705687571694557)
            ·
              refine ⟨2298361520889632839385459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6128964055705687571694557 2298361520889632839385459)
              ·
                refine ⟨3447542281334449259078189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2298361520889632839385459 3447542281334449259078189)
                ·
                  refine ⟨1292828355500418472154321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3447542281334449259078189 1292828355500418472154321)
                  ·
                    refine ⟨969621266625313854115741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1292828355500418472154321 969621266625313854115741)
                    ·
                      refine ⟨363607974984492695293403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 969621266625313854115741 363607974984492695293403)
                      ·
                        rfl

theorem cell23_708124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_708124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708124 prefixEnd_708124 := by exact prefixLift 708124
  have htrace : WordTrace (prefixWord ++ tailWord_708124) baseStart_708124 baseEnd_708124 := by
    simpa [prefixWord, tailWord_708124, baseEnd_708124] using wordTrace_append hprefix tailTrace_708124
  have hstable : (prefixWord ++ tailWord_708124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708124).length < 2 ^ (prefixWord ++ tailWord_708124).sum := by decide
  have hdescent : baseEnd_708124 < baseStart_708124 := by decide
  rcases family_descends (prefixWord ++ tailWord_708124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708177 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 2, 3, 4]
def baseStart_708177 : Nat := 118140960795 + 708177 * 2 ^ 59
def prefixEnd_708177 : Nat := 4983230072969 + 3 ^ 40 * 708177 * 2
def baseEnd_708177 : Nat := 363635189459180987930659

theorem tailTrace_708177 : CollatzResearch.WordTrace tailWord_708177 prefixEnd_708177 363635189459180987930659 := by
  unfold tailWord_708177
  simp only [CollatzResearch.WordTrace]
  refine ⟨25829337155403150847626785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17219558103602100565084523 25829337155403150847626785)
  ·
    refine ⟨19372002866552363135720089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25829337155403150847626785 19372002866552363135720089)
    ·
      refine ⟨14529002149914272351790067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19372002866552363135720089 14529002149914272351790067)
      ·
        refine ⟨21793503224871408527685101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14529002149914272351790067 21793503224871408527685101)
        ·
          refine ⟨8172563709326778197881913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21793503224871408527685101 8172563709326778197881913)
          ·
            refine ⟨6129422781995083648411435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8172563709326778197881913 6129422781995083648411435)
            ·
              refine ⟨9194134172992625472617153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6129422781995083648411435 9194134172992625472617153)
              ·
                refine ⟨6895600629744469104462865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9194134172992625472617153 6895600629744469104462865)
                ·
                  refine ⟨5171700472308351828347149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6895600629744469104462865 5171700472308351828347149)
                  ·
                    refine ⟨1939387677115631935630181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5171700472308351828347149 1939387677115631935630181)
                    ·
                      refine ⟨363635189459180987930659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1939387677115631935630181 363635189459180987930659)
                      ·
                        rfl

theorem cell23_708177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_708177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708177 prefixEnd_708177 := by exact prefixLift 708177
  have htrace : WordTrace (prefixWord ++ tailWord_708177) baseStart_708177 baseEnd_708177 := by
    simpa [prefixWord, tailWord_708177, baseEnd_708177] using wordTrace_append hprefix tailTrace_708177
  have hstable : (prefixWord ++ tailWord_708177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708177).length < 2 ^ (prefixWord ++ tailWord_708177).sum := by decide
  have hdescent : baseEnd_708177 < baseStart_708177 := by decide
  rcases family_descends (prefixWord ++ tailWord_708177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708181 : List Nat := [1, 3, 2, 2, 1, 1, 1, 6, 1, 3, 2]
def baseStart_708181 : Nat := 118140960795 + 708181 * 2 ^ 59
def prefixEnd_708181 : Nat := 4983230072969 + 3 ^ 40 * 708181 * 2
def baseEnd_708181 : Nat := 363637243381798972280641

theorem tailTrace_708181 : CollatzResearch.WordTrace tailWord_708181 prefixEnd_708181 363637243381798972280641 := by
  unfold tailWord_708181
  simp only [CollatzResearch.WordTrace]
  refine ⟨25829483047388659530772397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17219655364925773020514931 25829483047388659530772397)
  ·
    refine ⟨9686056142770747324039649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25829483047388659530772397 9686056142770747324039649)
    ·
      refine ⟨7264542107078060493029737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9686056142770747324039649 7264542107078060493029737)
      ·
        refine ⟨5448406580308545369772303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7264542107078060493029737 5448406580308545369772303)
        ·
          refine ⟨8172609870462818054658455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5448406580308545369772303 8172609870462818054658455)
          ·
            refine ⟨12258914805694227081987683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8172609870462818054658455 12258914805694227081987683)
            ·
              refine ⟨18388372208541340622981525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12258914805694227081987683 18388372208541340622981525)
              ·
                refine ⟨861954947275375341702259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18388372208541340622981525 861954947275375341702259)
                ·
                  refine ⟨1292932420913063012553389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 861954947275375341702259 1292932420913063012553389)
                  ·
                    refine ⟨484849657842398629707521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1292932420913063012553389 484849657842398629707521)
                    ·
                      refine ⟨363637243381798972280641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 484849657842398629707521 363637243381798972280641)
                      ·
                        rfl

theorem cell23_708181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_708181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708181 prefixEnd_708181 := by exact prefixLift 708181
  have htrace : WordTrace (prefixWord ++ tailWord_708181) baseStart_708181 baseEnd_708181 := by
    simpa [prefixWord, tailWord_708181, baseEnd_708181] using wordTrace_append hprefix tailTrace_708181
  have hstable : (prefixWord ++ tailWord_708181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708181).length < 2 ^ (prefixWord ++ tailWord_708181).sum := by decide
  have hdescent : baseEnd_708181 < baseStart_708181 := by decide
  rcases family_descends (prefixWord ++ tailWord_708181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708189 : List Nat := [1, 4, 4, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_708189 : Nat := 118140960795 + 708189 * 2 ^ 59
def prefixEnd_708189 : Nat := 4983230072969 + 3 ^ 40 * 708189 * 2
def baseEnd_708189 : Nat := 363641351227034940980605

theorem tailTrace_708189 : CollatzResearch.WordTrace tailWord_708189 prefixEnd_708189 363641351227034940980605 := by
  unfold tailWord_708189
  simp only [CollatzResearch.WordTrace]
  refine ⟨25829774831359676897063621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17219849887573117931375747 25829774831359676897063621)
  ·
    refine ⟨4843082780879939418199429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25829774831359676897063621 4843082780879939418199429)
    ·
      refine ⟨908078021414988640912393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4843082780879939418199429 908078021414988640912393)
      ·
        refine ⟨681058516061241480684295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 908078021414988640912393 681058516061241480684295)
        ·
          refine ⟨1021587774091862221026443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 681058516061241480684295 1021587774091862221026443)
          ·
            refine ⟨1532381661137793331539665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021587774091862221026443 1532381661137793331539665)
            ·
              refine ⟨1149286245853344998654749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1532381661137793331539665 1149286245853344998654749)
              ·
                refine ⟨430982342195004374495531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1149286245853344998654749 430982342195004374495531)
                ·
                  refine ⟨646473513292506561743297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 430982342195004374495531 646473513292506561743297)
                  ·
                    refine ⟨484855134969379921307473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 646473513292506561743297 484855134969379921307473)
                    ·
                      refine ⟨363641351227034940980605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 484855134969379921307473 363641351227034940980605)
                      ·
                        rfl

theorem cell23_708189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_708189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708189 prefixEnd_708189 := by exact prefixLift 708189
  have htrace : WordTrace (prefixWord ++ tailWord_708189) baseStart_708189 baseEnd_708189 := by
    simpa [prefixWord, tailWord_708189, baseEnd_708189] using wordTrace_append hprefix tailTrace_708189
  have hstable : (prefixWord ++ tailWord_708189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708189).length < 2 ^ (prefixWord ++ tailWord_708189).sum := by decide
  have hdescent : baseEnd_708189 < baseStart_708189 := by decide
  rcases family_descends (prefixWord ++ tailWord_708189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708205 : List Nat := [1, 5, 1, 1, 4, 2, 1, 2, 2, 1, 3]
def baseStart_708205 : Nat := 118140960795 + 708205 * 2 ^ 59
def prefixEnd_708205 : Nat := 4983230072969 + 3 ^ 40 * 708205 * 2
def baseEnd_708205 : Nat := 363649566917506878380531

theorem tailTrace_708205 : CollatzResearch.WordTrace tailWord_708205 prefixEnd_708205 363649566917506878380531 := by
  unfold tailWord_708205
  simp only [CollatzResearch.WordTrace]
  refine ⟨25830358399301711629646069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17220238932867807753097379 25830358399301711629646069)
  ·
    refine ⟨2421596099934535465279319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25830358399301711629646069 2421596099934535465279319)
    ·
      refine ⟨3632394149901803197918979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2421596099934535465279319 3632394149901803197918979)
      ·
        refine ⟨5448591224852704796878469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3632394149901803197918979 5448591224852704796878469)
        ·
          refine ⟨1021610854659882149414713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5448591224852704796878469 1021610854659882149414713)
          ·
            refine ⟨766208140994911612061035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1021610854659882149414713 766208140994911612061035)
            ·
              refine ⟨1149312211492367418091553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766208140994911612061035 1149312211492367418091553)
              ·
                refine ⟨861984158619275563568665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1149312211492367418091553 861984158619275563568665)
                ·
                  refine ⟨646488118964456672676499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 861984158619275563568665 646488118964456672676499)
                  ·
                    refine ⟨969732178446685009014749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 646488118964456672676499 969732178446685009014749)
                    ·
                      refine ⟨363649566917506878380531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 969732178446685009014749 363649566917506878380531)
                      ·
                        rfl

theorem cell23_708205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_708205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708205 prefixEnd_708205 := by exact prefixLift 708205
  have htrace : WordTrace (prefixWord ++ tailWord_708205) baseStart_708205 baseEnd_708205 := by
    simpa [prefixWord, tailWord_708205, baseEnd_708205] using wordTrace_append hprefix tailTrace_708205
  have hstable : (prefixWord ++ tailWord_708205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708205).length < 2 ^ (prefixWord ++ tailWord_708205).sum := by decide
  have hdescent : baseEnd_708205 < baseStart_708205 := by decide
  rcases family_descends (prefixWord ++ tailWord_708205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708234 : List Nat := [3, 1, 2, 3, 2, 1, 2, 2, 7]
def baseStart_708234 : Nat := 118140960795 + 708234 * 2 ^ 59
def prefixEnd_708234 : Nat := 4983230072969 + 3 ^ 40 * 708234 * 2
def baseEnd_708234 : Nat := 40407161984054140546433

theorem tailTrace_708234 : CollatzResearch.WordTrace tailWord_708234 prefixEnd_708234 40407161984054140546433 := by
  unfold tailWord_708234
  simp only [CollatzResearch.WordTrace]
  refine ⟨6457854029049162395612939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17220944077464433054967837 6457854029049162395612939)
  ·
    refine ⟨9686781043573743593419409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6457854029049162395612939 9686781043573743593419409)
    ·
      refine ⟨7265085782680307695064557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9686781043573743593419409 7265085782680307695064557)
      ·
        refine ⟨2724407168505115385649209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7265085782680307695064557 2724407168505115385649209)
        ·
          refine ⟨2043305376378836539236907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2724407168505115385649209 2043305376378836539236907)
          ·
            refine ⟨3064958064568254808855361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2043305376378836539236907 3064958064568254808855361)
            ·
              refine ⟨2298718548426191106641521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3064958064568254808855361 2298718548426191106641521)
              ·
                refine ⟨1724038911319643329981141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2298718548426191106641521 1724038911319643329981141)
                ·
                  refine ⟨40407161984054140546433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1724038911319643329981141 40407161984054140546433)
                  ·
                    rfl

theorem cell23_708234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 7].length) (baseStart_708234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708234 prefixEnd_708234 := by exact prefixLift 708234
  have htrace : WordTrace (prefixWord ++ tailWord_708234) baseStart_708234 baseEnd_708234 := by
    simpa [prefixWord, tailWord_708234, baseEnd_708234] using wordTrace_append hprefix tailTrace_708234
  have hstable : (prefixWord ++ tailWord_708234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708234).length < 2 ^ (prefixWord ++ tailWord_708234).sum := by decide
  have hdescent : baseEnd_708234 < baseStart_708234 := by decide
  rcases family_descends (prefixWord ++ tailWord_708234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708267 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 4]
def baseStart_708267 : Nat := 118140960795 + 708267 * 2 ^ 59
def prefixEnd_708267 : Nat := 4983230072969 + 3 ^ 40 * 708267 * 2
def baseEnd_708267 : Nat := 363681402718085635805245

theorem tailTrace_708267 : CollatzResearch.WordTrace tailWord_708267 prefixEnd_708267 363681402718085635805245 := by
  unfold tailWord_708267
  simp only [CollatzResearch.WordTrace]
  refine ⟨25832619725077096218403055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17221746483384730812268703 25832619725077096218403055)
  ·
    refine ⟨38748929587615644327604583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25832619725077096218403055 38748929587615644327604583)
    ·
      refine ⟨58123394381423466491406875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38748929587615644327604583 58123394381423466491406875)
      ·
        refine ⟨87185091572135199737110313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58123394381423466491406875 87185091572135199737110313)
        ·
          refine ⟨65388818679101399802832735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87185091572135199737110313 65388818679101399802832735)
          ·
            refine ⟨98083228018652099704249103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65388818679101399802832735 98083228018652099704249103)
            ·
              refine ⟨147124842027978149556373655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98083228018652099704249103 147124842027978149556373655)
              ·
                refine ⟨220687263041967224334560483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147124842027978149556373655 220687263041967224334560483)
                ·
                  refine ⟨331030894562950836501840725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220687263041967224334560483 331030894562950836501840725)
                  ·
                    refine ⟨1939634147829790057627973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 331030894562950836501840725 1939634147829790057627973)
                    ·
                      refine ⟨363681402718085635805245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1939634147829790057627973 363681402718085635805245)
                      ·
                        rfl

theorem cell23_708267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 4].length) (baseStart_708267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708267 prefixEnd_708267 := by exact prefixLift 708267
  have htrace : WordTrace (prefixWord ++ tailWord_708267) baseStart_708267 baseEnd_708267 := by
    simpa [prefixWord, tailWord_708267, baseEnd_708267] using wordTrace_append hprefix tailTrace_708267
  have hstable : (prefixWord ++ tailWord_708267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708267).length < 2 ^ (prefixWord ++ tailWord_708267).sum := by decide
  have hdescent : baseEnd_708267 < baseStart_708267 := by decide
  rcases family_descends (prefixWord ++ tailWord_708267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708351 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 5, 1, 3]
def baseStart_708351 : Nat := 118140960795 + 708351 * 2 ^ 59
def prefixEnd_708351 : Nat := 4983230072969 + 3 ^ 40 * 708351 * 2
def baseEnd_708351 : Nat := 363724535093063307154859

theorem tailTrace_708351 : CollatzResearch.WordTrace tailWord_708351 prefixEnd_708351 363724535093063307154859 := by
  unfold tailWord_708351
  simp only [CollatzResearch.WordTrace]
  refine ⟨25835683456772778564460907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17223788971181852376307271 25835683456772778564460907)
  ·
    refine ⟨38753525185159167846691361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25835683456772778564460907 38753525185159167846691361)
    ·
      refine ⟨29065143888869375885018521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38753525185159167846691361 29065143888869375885018521)
      ·
        refine ⟨21798857916652031913763891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29065143888869375885018521 21798857916652031913763891)
        ·
          refine ⟨32698286874978047870645837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21798857916652031913763891 32698286874978047870645837)
          ·
            refine ⟨12261857578116767951492189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32698286874978047870645837 12261857578116767951492189)
            ·
              refine ⟨4598196591793787981809571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12261857578116767951492189 4598196591793787981809571)
              ·
                refine ⟨6897294887690681972714357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4598196591793787981809571 6897294887690681972714357)
                ·
                  refine ⟨646621395721001434941971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6897294887690681972714357 646621395721001434941971)
                  ·
                    refine ⟨969932093581502152412957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 646621395721001434941971 969932093581502152412957)
                    ·
                      refine ⟨363724535093063307154859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 969932093581502152412957 363724535093063307154859)
                      ·
                        rfl

theorem cell23_708351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 1, 3].length) (baseStart_708351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708351 prefixEnd_708351 := by exact prefixLift 708351
  have htrace : WordTrace (prefixWord ++ tailWord_708351) baseStart_708351 baseEnd_708351 := by
    simpa [prefixWord, tailWord_708351, baseEnd_708351] using wordTrace_append hprefix tailTrace_708351
  have hstable : (prefixWord ++ tailWord_708351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708351).length < 2 ^ (prefixWord ++ tailWord_708351).sum := by decide
  have hdescent : baseEnd_708351 < baseStart_708351 := by decide
  rcases family_descends (prefixWord ++ tailWord_708351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708385 : List Nat := [1, 2, 3, 2, 1, 3, 2, 4, 1, 1, 3]
def baseStart_708385 : Nat := 118140960795 + 708385 * 2 ^ 59
def prefixEnd_708385 : Nat := 4983230072969 + 3 ^ 40 * 708385 * 2
def baseEnd_708385 : Nat := 363741993435316174129703

theorem tailTrace_708385 : CollatzResearch.WordTrace tailWord_708385 prefixEnd_708385 363741993435316174129703 := by
  unfold tailWord_708385
  simp only [CollatzResearch.WordTrace]
  refine ⟨25836923538649602371198609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17224615692433068247465739 25836923538649602371198609)
  ·
    refine ⟨19377692653987201778398957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25836923538649602371198609 19377692653987201778398957)
    ·
      refine ⟨7266634745245200666899609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19377692653987201778398957 7266634745245200666899609)
      ·
        refine ⟨5449976058933900500174707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7266634745245200666899609 5449976058933900500174707)
        ·
          refine ⟨8174964088400850750262061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5449976058933900500174707 8174964088400850750262061)
          ·
            refine ⟨3065611533150319031348273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8174964088400850750262061 3065611533150319031348273)
            ·
              refine ⟨2299208649862739273511205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3065611533150319031348273 2299208649862739273511205)
              ·
                refine ⟨431101621849263613783351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2299208649862739273511205 431101621849263613783351)
                ·
                  refine ⟨646652432773895420675027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 431101621849263613783351 646652432773895420675027)
                  ·
                    refine ⟨969978649160843131012541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 646652432773895420675027 969978649160843131012541)
                    ·
                      refine ⟨363741993435316174129703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 969978649160843131012541 363741993435316174129703)
                      ·
                        rfl

theorem cell23_708385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_708385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708385 prefixEnd_708385 := by exact prefixLift 708385
  have htrace : WordTrace (prefixWord ++ tailWord_708385) baseStart_708385 baseEnd_708385 := by
    simpa [prefixWord, tailWord_708385, baseEnd_708385] using wordTrace_append hprefix tailTrace_708385
  have hstable : (prefixWord ++ tailWord_708385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708385).length < 2 ^ (prefixWord ++ tailWord_708385).sum := by decide
  have hdescent : baseEnd_708385 < baseStart_708385 := by decide
  rcases family_descends (prefixWord ++ tailWord_708385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708401 : List Nat := [1, 2, 2, 3, 2, 2, 3, 1, 1, 6]
def baseStart_708401 : Nat := 118140960795 + 708401 * 2 ^ 59
def prefixEnd_708401 : Nat := 4983230072969 + 3 ^ 40 * 708401 * 2
def baseEnd_708401 : Nat := 121250069708596037176543

theorem tailTrace_708401 : CollatzResearch.WordTrace tailWord_708401 prefixEnd_708401 121250069708596037176543 := by
  unfold tailWord_708401
  simp only [CollatzResearch.WordTrace]
  refine ⟨25837507106591637103781057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17225004737727758069187371 25837507106591637103781057)
  ·
    refine ⟨19378130329943727827835793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25837507106591637103781057 19378130329943727827835793)
    ·
      refine ⟨14533597747457795870876845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19378130329943727827835793 14533597747457795870876845)
      ·
        refine ⟨5450099155296673451578817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14533597747457795870876845 5450099155296673451578817)
        ·
          refine ⟨4087574366472505088684113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5450099155296673451578817 4087574366472505088684113)
          ·
            refine ⟨3065680774854378816513085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4087574366472505088684113 3065680774854378816513085)
            ·
              refine ⟨1149630290570392056192407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3065680774854378816513085 1149630290570392056192407)
              ·
                refine ⟨1724445435855588084288611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1149630290570392056192407 1724445435855588084288611)
                ·
                  refine ⟨2586668153783382126432917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1724445435855588084288611 2586668153783382126432917)
                  ·
                    refine ⟨121250069708596037176543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2586668153783382126432917 121250069708596037176543)
                    ·
                      rfl

theorem cell23_708401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 6].length) (baseStart_708401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708401 prefixEnd_708401 := by exact prefixLift 708401
  have htrace : WordTrace (prefixWord ++ tailWord_708401) baseStart_708401 baseEnd_708401 := by
    simpa [prefixWord, tailWord_708401, baseEnd_708401] using wordTrace_append hprefix tailTrace_708401
  have hstable : (prefixWord ++ tailWord_708401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708401).length < 2 ^ (prefixWord ++ tailWord_708401).sum := by decide
  have hdescent : baseEnd_708401 < baseStart_708401 := by decide
  rcases family_descends (prefixWord ++ tailWord_708401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708408 : List Nat := [2, 1, 2, 1, 3, 4, 2, 2, 1, 1, 4]
def baseStart_708408 : Nat := 118140960795 + 708408 * 2 ^ 59
def prefixEnd_708408 : Nat := 4983230072969 + 3 ^ 40 * 708408 * 2
def baseEnd_708408 : Nat := 363753803490369584142097

theorem tailTrace_708408 : CollatzResearch.WordTrace tailWord_708408 prefixEnd_708408 363753803490369584142097 := by
  unfold tailWord_708408
  simp only [CollatzResearch.WordTrace]
  refine ⟨12918881208783138649642939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17225174945044184866190585 12918881208783138649642939)
  ·
    refine ⟨19378321813174707974464409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12918881208783138649642939 19378321813174707974464409)
    ·
      refine ⟨14533741359881030980848307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19378321813174707974464409 14533741359881030980848307)
      ·
        refine ⟨21800612039821546471272461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14533741359881030980848307 21800612039821546471272461)
        ·
          refine ⟨8175229514933079926727173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21800612039821546471272461 8175229514933079926727173)
          ·
            refine ⟨1532855534049952486261345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8175229514933079926727173 1532855534049952486261345)
            ·
              refine ⟨1149641650537464364696009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1532855534049952486261345 1149641650537464364696009)
              ·
                refine ⟨862231237903098273522007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1149641650537464364696009 862231237903098273522007)
                ·
                  refine ⟨1293346856854647410283011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 862231237903098273522007 1293346856854647410283011)
                  ·
                    refine ⟨1940020285281971115424517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1293346856854647410283011 1940020285281971115424517)
                    ·
                      refine ⟨363753803490369584142097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1940020285281971115424517 363753803490369584142097)
                      ·
                        rfl

theorem cell23_708408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 1, 1, 4].length) (baseStart_708408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708408 prefixEnd_708408 := by exact prefixLift 708408
  have htrace : WordTrace (prefixWord ++ tailWord_708408) baseStart_708408 baseEnd_708408 := by
    simpa [prefixWord, tailWord_708408, baseEnd_708408] using wordTrace_append hprefix tailTrace_708408
  have hstable : (prefixWord ++ tailWord_708408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708408).length < 2 ^ (prefixWord ++ tailWord_708408).sum := by decide
  have hdescent : baseEnd_708408 < baseStart_708408 := by decide
  rcases family_descends (prefixWord ++ tailWord_708408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708428 : List Nat := [2, 2, 1, 3, 4, 1, 2, 1, 1, 1, 5]
def baseStart_708428 : Nat := 118140960795 + 708428 * 2 ^ 59
def prefixEnd_708428 : Nat := 4983230072969 + 3 ^ 40 * 708428 * 2
def baseEnd_708428 : Nat := 363764073103459505892005

theorem tailTrace_708428 : CollatzResearch.WordTrace tailWord_708428 prefixEnd_708428 363764073103459505892005 := by
  unfold tailWord_708428
  simp only [CollatzResearch.WordTrace]
  refine ⟨12919245938746910357506969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17225661251662547143342625 12919245938746910357506969)
  ·
    refine ⟨9689434454060182768130227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12919245938746910357506969 9689434454060182768130227)
    ·
      refine ⟨14534151681090274152195341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9689434454060182768130227 14534151681090274152195341)
      ·
        refine ⟨5450306880408852807073253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14534151681090274152195341 5450306880408852807073253)
        ·
          refine ⟨1021932540076659901326235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5450306880408852807073253 1021932540076659901326235)
          ·
            refine ⟨1532898810114989851989353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021932540076659901326235 1532898810114989851989353)
            ·
              refine ⟨1149674107586242388992015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1532898810114989851989353 1149674107586242388992015)
              ·
                refine ⟨1724511161379363583488023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1149674107586242388992015 1724511161379363583488023)
                ·
                  refine ⟨2586766742069045375232035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1724511161379363583488023 2586766742069045375232035)
                  ·
                    refine ⟨3880150113103568062848053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2586766742069045375232035 3880150113103568062848053)
                    ·
                      refine ⟨363764073103459505892005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3880150113103568062848053 363764073103459505892005)
                      ·
                        rfl

theorem cell23_708428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_708428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708428 prefixEnd_708428 := by exact prefixLift 708428
  have htrace : WordTrace (prefixWord ++ tailWord_708428) baseStart_708428 baseEnd_708428 := by
    simpa [prefixWord, tailWord_708428, baseEnd_708428] using wordTrace_append hprefix tailTrace_708428
  have hstable : (prefixWord ++ tailWord_708428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708428).length < 2 ^ (prefixWord ++ tailWord_708428).sum := by decide
  have hdescent : baseEnd_708428 < baseStart_708428 := by decide
  rcases family_descends (prefixWord ++ tailWord_708428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708452 : List Nat := [2, 3, 1, 1, 5, 2, 2, 1, 2, 4]
def baseStart_708452 : Nat := 118140960795 + 708452 * 2 ^ 59
def prefixEnd_708452 : Nat := 4983230072969 + 3 ^ 40 * 708452 * 2
def baseEnd_708452 : Nat := 121258798879722470663965

theorem tailTrace_708452 : CollatzResearch.WordTrace tailWord_708452 prefixEnd_708452 121258798879722470663965 := by
  unfold tailWord_708452
  simp only [CollatzResearch.WordTrace]
  refine ⟨12919683614703436406943805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17226244819604581875925073 12919683614703436406943805)
  ·
    refine ⟨4844881355513788652603927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12919683614703436406943805 4844881355513788652603927)
    ·
      refine ⟨7267322033270682978905891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4844881355513788652603927 7267322033270682978905891)
      ·
        refine ⟨10900983049906024468358837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7267322033270682978905891 10900983049906024468358837)
        ·
          refine ⟨1021967160928689793908641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10900983049906024468358837 1021967160928689793908641)
          ·
            refine ⟨766475370696517345431481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1021967160928689793908641 766475370696517345431481)
            ·
              refine ⟨574856528022388009073611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 766475370696517345431481 574856528022388009073611)
              ·
                refine ⟨862284792033582013610417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 574856528022388009073611 862284792033582013610417)
                ·
                  refine ⟨646713594025186510207813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 862284792033582013610417 646713594025186510207813)
                  ·
                    refine ⟨121258798879722470663965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 646713594025186510207813 121258798879722470663965)
                    ·
                      rfl

theorem cell23_708452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_708452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708452 prefixEnd_708452 := by exact prefixLift 708452
  have htrace : WordTrace (prefixWord ++ tailWord_708452) baseStart_708452 baseEnd_708452 := by
    simpa [prefixWord, tailWord_708452, baseEnd_708452] using wordTrace_append hprefix tailTrace_708452
  have hstable : (prefixWord ++ tailWord_708452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708452).length < 2 ^ (prefixWord ++ tailWord_708452).sum := by decide
  have hdescent : baseEnd_708452 < baseStart_708452 := by decide
  rcases family_descends (prefixWord ++ tailWord_708452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708462 : List Nat := [4, 1, 2, 3, 1, 3, 1, 2, 1, 2, 3]
def baseStart_708462 : Nat := 118140960795 + 708462 * 2 ^ 59
def prefixEnd_708462 : Nat := 4983230072969 + 3 ^ 40 * 708462 * 2
def baseEnd_708462 : Nat := 363781531445712372866849

theorem tailTrace_708462 : CollatzResearch.WordTrace tailWord_708462 prefixEnd_708462 363781531445712372866849 := by
  unfold tailWord_708462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3229966494921330565218955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17226487972913763014501093 3229966494921330565218955)
  ·
    refine ⟨4844949742381995847828433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3229966494921330565218955 4844949742381995847828433)
    ·
      refine ⟨3633712306786496885871325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4844949742381995847828433 3633712306786496885871325)
      ·
        refine ⟨1362642115044936332201747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3633712306786496885871325 1362642115044936332201747)
        ·
          refine ⟨2043963172567404498302621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1362642115044936332201747 2043963172567404498302621)
          ·
            refine ⟨766486189712776686863483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2043963172567404498302621 766486189712776686863483)
            ·
              refine ⟨1149729284569165030295225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766486189712776686863483 1149729284569165030295225)
              ·
                refine ⟨862296963426873772721419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1149729284569165030295225 862296963426873772721419)
                ·
                  refine ⟨1293445445140310659082129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 862296963426873772721419 1293445445140310659082129)
                  ·
                    refine ⟨970084083855232994311597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1293445445140310659082129 970084083855232994311597)
                    ·
                      refine ⟨363781531445712372866849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 970084083855232994311597 363781531445712372866849)
                      ·
                        rfl

theorem cell23_708462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_708462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708462 prefixEnd_708462 := by exact prefixLift 708462
  have htrace : WordTrace (prefixWord ++ tailWord_708462) baseStart_708462 baseEnd_708462 := by
    simpa [prefixWord, tailWord_708462, baseEnd_708462] using wordTrace_append hprefix tailTrace_708462
  have hstable : (prefixWord ++ tailWord_708462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708462).length < 2 ^ (prefixWord ++ tailWord_708462).sum := by decide
  have hdescent : baseEnd_708462 < baseStart_708462 := by decide
  rcases family_descends (prefixWord ++ tailWord_708462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708464 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 8]
def baseStart_708464 : Nat := 118140960795 + 708464 * 2 ^ 59
def prefixEnd_708464 : Nat := 4983230072969 + 3 ^ 40 * 708464 * 2
def baseEnd_708464 : Nat := 363782558407021365041839

theorem tailTrace_708464 : CollatzResearch.WordTrace tailWord_708464 prefixEnd_708464 363782558407021365041839 := by
  unfold tailWord_708464
  simp only [CollatzResearch.WordTrace]
  refine ⟨12919902452681699431662223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17226536603575599242216297 12919902452681699431662223)
  ·
    refine ⟨19379853679022549147493335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12919902452681699431662223 19379853679022549147493335)
    ·
      refine ⟨29069780518533823721240003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19379853679022549147493335 29069780518533823721240003)
      ·
        refine ⟨43604670777800735581860005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29069780518533823721240003 43604670777800735581860005)
        ·
          refine ⟨8175875770837637921598751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43604670777800735581860005 8175875770837637921598751)
          ·
            refine ⟨12263813656256456882398127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8175875770837637921598751 12263813656256456882398127)
            ·
              refine ⟨18395720484384685323597191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12263813656256456882398127 18395720484384685323597191)
              ·
                refine ⟨27593580726577027985395787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18395720484384685323597191 27593580726577027985395787)
                ·
                  refine ⟨41390371089865541978093681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27593580726577027985395787 41390371089865541978093681)
                  ·
                    refine ⟨31042778317399156483570261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41390371089865541978093681 31042778317399156483570261)
                    ·
                      refine ⟨363782558407021365041839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 31042778317399156483570261 363782558407021365041839)
                      ·
                        rfl

theorem cell23_708464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_708464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708464 prefixEnd_708464 := by exact prefixLift 708464
  have htrace : WordTrace (prefixWord ++ tailWord_708464) baseStart_708464 baseEnd_708464 := by
    simpa [prefixWord, tailWord_708464, baseEnd_708464] using wordTrace_append hprefix tailTrace_708464
  have hstable : (prefixWord ++ tailWord_708464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708464).length < 2 ^ (prefixWord ++ tailWord_708464).sum := by decide
  have hdescent : baseEnd_708464 < baseStart_708464 := by decide
  rcases family_descends (prefixWord ++ tailWord_708464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708498 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_708498 : Nat := 118140960795 + 708498 * 2 ^ 59
def prefixEnd_708498 : Nat := 4983230072969 + 3 ^ 40 * 708498 * 2
def baseEnd_708498 : Nat := 363800016749274232016683

theorem tailTrace_708498 : CollatzResearch.WordTrace tailWord_708498 prefixEnd_708498 363800016749274232016683 := by
  unfold tailWord_708498
  simp only [CollatzResearch.WordTrace]
  refine ⟨6460261246810055667515537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17227363324826815113374765 6460261246810055667515537)
  ·
    refine ⟨4845195935107541750636653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6460261246810055667515537 4845195935107541750636653)
    ·
      refine ⟨1816948475665328156488745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4845195935107541750636653 1816948475665328156488745)
      ·
        refine ⟨1362711356748996117366559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1816948475665328156488745 1362711356748996117366559)
        ·
          refine ⟨2044067035123494176049839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1362711356748996117366559 2044067035123494176049839)
          ·
            refine ⟨3066100552685241264074759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2044067035123494176049839 3066100552685241264074759)
            ·
              refine ⟨4599150829027861896112139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3066100552685241264074759 4599150829027861896112139)
              ·
                refine ⟨6898726243541792844168209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4599150829027861896112139 6898726243541792844168209)
                ·
                  refine ⟨5174044682656344633126157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6898726243541792844168209 5174044682656344633126157)
                  ·
                    refine ⟨1940266755996129237422309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5174044682656344633126157 1940266755996129237422309)
                    ·
                      refine ⟨363800016749274232016683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1940266755996129237422309 363800016749274232016683)
                      ·
                        rfl

theorem cell23_708498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_708498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708498 prefixEnd_708498 := by exact prefixLift 708498
  have htrace : WordTrace (prefixWord ++ tailWord_708498) baseStart_708498 baseEnd_708498 := by
    simpa [prefixWord, tailWord_708498, baseEnd_708498] using wordTrace_append hprefix tailTrace_708498
  have hstable : (prefixWord ++ tailWord_708498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708498).length < 2 ^ (prefixWord ++ tailWord_708498).sum := by decide
  have hdescent : baseEnd_708498 < baseStart_708498 := by decide
  rcases family_descends (prefixWord ++ tailWord_708498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708501 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 1, 6, 3]
def baseStart_708501 : Nat := 118140960795 + 708501 * 2 ^ 59
def prefixEnd_708501 : Nat := 4983230072969 + 3 ^ 40 * 708501 * 2
def baseEnd_708501 : Nat := 363801557191237720279169

theorem tailTrace_708501 : CollatzResearch.WordTrace tailWord_708501 prefixEnd_708501 363801557191237720279169 := by
  unfold tailWord_708501
  simp only [CollatzResearch.WordTrace]
  refine ⟨25841154406229354182421357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17227436270819569454947571 25841154406229354182421357)
  ·
    refine ⟨9690432902336007818408009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25841154406229354182421357 9690432902336007818408009)
    ·
      refine ⟨7267824676752005863806007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9690432902336007818408009 7267824676752005863806007)
      ·
        refine ⟨10901737015128008795709011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7267824676752005863806007 10901737015128008795709011)
        ·
          refine ⟨16352605522692013193563517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10901737015128008795709011 16352605522692013193563517)
          ·
            refine ⟨6132227071009504947586319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16352605522692013193563517 6132227071009504947586319)
            ·
              refine ⟨9198340606514257421379479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6132227071009504947586319 9198340606514257421379479)
              ·
                refine ⟨13797510909771386132069219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9198340606514257421379479 13797510909771386132069219)
                ·
                  refine ⟨20696266364657079198103829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13797510909771386132069219 20696266364657079198103829)
                  ·
                    refine ⟨970137485843300587411117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20696266364657079198103829 970137485843300587411117)
                    ·
                      refine ⟨363801557191237720279169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 970137485843300587411117 363801557191237720279169)
                      ·
                        rfl

theorem cell23_708501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_708501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708501 prefixEnd_708501 := by exact prefixLift 708501
  have htrace : WordTrace (prefixWord ++ tailWord_708501) baseStart_708501 baseEnd_708501 := by
    simpa [prefixWord, tailWord_708501, baseEnd_708501] using wordTrace_append hprefix tailTrace_708501
  have hstable : (prefixWord ++ tailWord_708501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708501).length < 2 ^ (prefixWord ++ tailWord_708501).sum := by decide
  have hdescent : baseEnd_708501 < baseStart_708501 := by decide
  rcases family_descends (prefixWord ++ tailWord_708501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708508 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 2, 6]
def baseStart_708508 : Nat := 118140960795 + 708508 * 2 ^ 59
def prefixEnd_708508 : Nat := 4983230072969 + 3 ^ 40 * 708508 * 2
def baseEnd_708508 : Nat := 121268383851939730963879

theorem tailTrace_708508 : CollatzResearch.WordTrace tailWord_708508 prefixEnd_708508 121268383851939730963879 := by
  unfold tailWord_708508
  simp only [CollatzResearch.WordTrace]
  refine ⟨12920704858601997188963089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17227606478135996251950785 12920704858601997188963089)
  ·
    refine ⟨9690528643951497891722317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12920704858601997188963089 9690528643951497891722317)
    ·
      refine ⟨3633948241481811709395869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9690528643951497891722317 3633948241481811709395869)
      ·
        refine ⟨1362730590555679391023451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3633948241481811709395869 1362730590555679391023451)
        ·
          refine ⟨2044095885833519086535177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1362730590555679391023451 2044095885833519086535177)
          ·
            refine ⟨1533071914375139314901383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2044095885833519086535177 1533071914375139314901383)
            ·
              refine ⟨2299607871562708972352075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1533071914375139314901383 2299607871562708972352075)
              ·
                refine ⟨3449411807344063458528113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2299607871562708972352075 3449411807344063458528113)
                ·
                  refine ⟨2587058855508047593896085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3449411807344063458528113 2587058855508047593896085)
                  ·
                    refine ⟨121268383851939730963879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2587058855508047593896085 121268383851939730963879)
                    ·
                      rfl

theorem cell23_708508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_708508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708508 prefixEnd_708508 := by exact prefixLift 708508
  have htrace : WordTrace (prefixWord ++ tailWord_708508) baseStart_708508 baseEnd_708508 := by
    simpa [prefixWord, tailWord_708508, baseEnd_708508] using wordTrace_append hprefix tailTrace_708508
  have hstable : (prefixWord ++ tailWord_708508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708508).length < 2 ^ (prefixWord ++ tailWord_708508).sum := by decide
  have hdescent : baseEnd_708508 < baseStart_708508 := by decide
  rcases family_descends (prefixWord ++ tailWord_708508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708531 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 3]
def baseStart_708531 : Nat := 118140960795 + 708531 * 2 ^ 59
def prefixEnd_708531 : Nat := 4983230072969 + 3 ^ 40 * 708531 * 2
def baseEnd_708531 : Nat := 363816961610872602904031

theorem tailTrace_708531 : CollatzResearch.WordTrace tailWord_708531 prefixEnd_708531 363816961610872602904031 := by
  unfold tailWord_708531
  simp only [CollatzResearch.WordTrace]
  refine ⟨25842248596120669306013447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17228165730747112870675631 25842248596120669306013447)
  ·
    refine ⟨38763372894181003959020171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25842248596120669306013447 38763372894181003959020171)
    ·
      refine ⟨58145059341271505938530257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38763372894181003959020171 58145059341271505938530257)
      ·
        refine ⟨43608794505953629453897693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58145059341271505938530257 43608794505953629453897693)
        ·
          refine ⟨16353297939732611045211635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43608794505953629453897693 16353297939732611045211635)
          ·
            refine ⟨24529946909598916567817453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16353297939732611045211635 24529946909598916567817453)
            ·
              refine ⟨9198730091099593712931545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24529946909598916567817453 9198730091099593712931545)
              ·
                refine ⟨6899047568324695284698659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9198730091099593712931545 6899047568324695284698659)
                ·
                  refine ⟨10348571352487042927047989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6899047568324695284698659 10348571352487042927047989)
                  ·
                    refine ⟨970178564295660274410749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10348571352487042927047989 970178564295660274410749)
                    ·
                      refine ⟨363816961610872602904031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 970178564295660274410749 363816961610872602904031)
                      ·
                        rfl

theorem cell23_708531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 3].length) (baseStart_708531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708531 prefixEnd_708531 := by exact prefixLift 708531
  have htrace : WordTrace (prefixWord ++ tailWord_708531) baseStart_708531 baseEnd_708531 := by
    simpa [prefixWord, tailWord_708531, baseEnd_708531] using wordTrace_append hprefix tailTrace_708531
  have hstable : (prefixWord ++ tailWord_708531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708531).length < 2 ^ (prefixWord ++ tailWord_708531).sum := by decide
  have hdescent : baseEnd_708531 < baseStart_708531 := by decide
  rcases family_descends (prefixWord ++ tailWord_708531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708551 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 4, 5]
def baseStart_708551 : Nat := 118140960795 + 708551 * 2 ^ 59
def prefixEnd_708551 : Nat := 4983230072969 + 3 ^ 40 * 708551 * 2
def baseEnd_708551 : Nat := 121275743741320841551313

theorem tailTrace_708551 : CollatzResearch.WordTrace tailWord_708551 prefixEnd_708551 121275743741320841551313 := by
  unfold tailWord_708551
  simp only [CollatzResearch.WordTrace]
  refine ⟨25842978056048212721741507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17228652037365475147827671 25842978056048212721741507)
  ·
    refine ⟨38764467084072319082612261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25842978056048212721741507 38764467084072319082612261)
    ·
      refine ⟨7268337578263559827989799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38764467084072319082612261 7268337578263559827989799)
      ·
        refine ⟨10902506367395339741984699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7268337578263559827989799 10902506367395339741984699)
        ·
          refine ⟨16353759551093009612977049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10902506367395339741984699 16353759551093009612977049)
          ·
            refine ⟨12265319663319757209732787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16353759551093009612977049 12265319663319757209732787)
            ·
              refine ⟨18397979494979635814599181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12265319663319757209732787 18397979494979635814599181)
              ·
                refine ⟨6899242310617363430474693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18397979494979635814599181 6899242310617363430474693)
                ·
                  refine ⟨1293607933240755643214005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6899242310617363430474693 1293607933240755643214005)
                  ·
                    refine ⟨121275743741320841551313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1293607933240755643214005 121275743741320841551313)
                    ·
                      rfl

theorem cell23_708551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_708551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708551 prefixEnd_708551 := by exact prefixLift 708551
  have htrace : WordTrace (prefixWord ++ tailWord_708551) baseStart_708551 baseEnd_708551 := by
    simpa [prefixWord, tailWord_708551, baseEnd_708551] using wordTrace_append hprefix tailTrace_708551
  have hstable : (prefixWord ++ tailWord_708551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708551).length < 2 ^ (prefixWord ++ tailWord_708551).sum := by decide
  have hdescent : baseEnd_708551 < baseStart_708551 := by decide
  rcases family_descends (prefixWord ++ tailWord_708551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708566 : List Nat := [5, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2]
def baseStart_708566 : Nat := 118140960795 + 708566 * 2 ^ 59
def prefixEnd_708566 : Nat := 4983230072969 + 3 ^ 40 * 708566 * 2
def baseEnd_708566 : Nat := 363834933433779965966371

theorem tailTrace_708566 : CollatzResearch.WordTrace tailWord_708566 prefixEnd_708566 363834933433779965966371 := by
  unfold tailWord_708566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1615220321937116892721097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17229016767329246855691701 1615220321937116892721097)
  ·
    refine ⟨1211415241452837669540823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1615220321937116892721097 1211415241452837669540823)
    ·
      refine ⟨1817122862179256504311235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1211415241452837669540823 1817122862179256504311235)
      ·
        refine ⟨2725684293268884756466853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1817122862179256504311235 2725684293268884756466853)
        ·
          refine ⟨511065804987915891837535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2725684293268884756466853 511065804987915891837535)
          ·
            refine ⟨766598707481873837756303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511065804987915891837535 766598707481873837756303)
            ·
              refine ⟨1149898061222810756634455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766598707481873837756303 1149898061222810756634455)
              ·
                refine ⟨1724847091834216134951683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1149898061222810756634455 1724847091834216134951683)
                ·
                  refine ⟨2587270637751324202427525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1724847091834216134951683 2587270637751324202427525)
                  ·
                    refine ⟨485113244578373287955161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2587270637751324202427525 485113244578373287955161)
                    ·
                      refine ⟨363834933433779965966371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 485113244578373287955161 363834933433779965966371)
                      ·
                        rfl

theorem cell23_708566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_708566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708566 prefixEnd_708566 := by exact prefixLift 708566
  have htrace : WordTrace (prefixWord ++ tailWord_708566) baseStart_708566 baseEnd_708566 := by
    simpa [prefixWord, tailWord_708566, baseEnd_708566] using wordTrace_append hprefix tailTrace_708566
  have hstable : (prefixWord ++ tailWord_708566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708566).length < 2 ^ (prefixWord ++ tailWord_708566).sum := by decide
  have hdescent : baseEnd_708566 < baseStart_708566 := by decide
  rcases family_descends (prefixWord ++ tailWord_708566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708588 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 1, 6, 2]
def baseStart_708588 : Nat := 118140960795 + 708588 * 2 ^ 59
def prefixEnd_708588 : Nat := 4983230072969 + 3 ^ 40 * 708588 * 2
def baseEnd_708588 : Nat := 363846230008178879891269

theorem tailTrace_708588 : CollatzResearch.WordTrace tailWord_708588 prefixEnd_708588 363846230008178879891269 := by
  unfold tailWord_708588
  simp only [CollatzResearch.WordTrace]
  refine ⟨12922163778457084020419209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17229551704609445360558945 12922163778457084020419209)
  ·
    refine ⟨9691622833842813015314407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12922163778457084020419209 9691622833842813015314407)
    ·
      refine ⟨14537434250764219522971611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9691622833842813015314407 14537434250764219522971611)
      ·
        refine ⟨21806151376146329284457417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14537434250764219522971611 21806151376146329284457417)
        ·
          refine ⟨16354613532109746963343063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21806151376146329284457417 16354613532109746963343063)
          ·
            refine ⟨24531920298164620445014595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16354613532109746963343063 24531920298164620445014595)
            ·
              refine ⟨36797880447246930667521893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24531920298164620445014595 36797880447246930667521893)
              ·
                refine ⟨6899602583858799500160355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36797880447246930667521893 6899602583858799500160355)
                ·
                  refine ⟨10349403875788199250240533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6899602583858799500160355 10349403875788199250240533)
                  ·
                    refine ⟨485128306677571839855025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10349403875788199250240533 485128306677571839855025)
                    ·
                      refine ⟨363846230008178879891269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 485128306677571839855025 363846230008178879891269)
                      ·
                        rfl

theorem cell23_708588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 6, 2].length) (baseStart_708588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708588 prefixEnd_708588 := by exact prefixLift 708588
  have htrace : WordTrace (prefixWord ++ tailWord_708588) baseStart_708588 baseEnd_708588 := by
    simpa [prefixWord, tailWord_708588, baseEnd_708588] using wordTrace_append hprefix tailTrace_708588
  have hstable : (prefixWord ++ tailWord_708588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708588).length < 2 ^ (prefixWord ++ tailWord_708588).sum := by decide
  have hdescent : baseEnd_708588 < baseStart_708588 := by decide
  rcases family_descends (prefixWord ++ tailWord_708588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708589 : List Nat := [1, 5, 1, 4, 1, 2, 1, 3, 5]
def baseStart_708589 : Nat := 118140960795 + 708589 * 2 ^ 59
def prefixEnd_708589 : Nat := 4983230072969 + 3 ^ 40 * 708589 * 2
def baseEnd_708589 : Nat := 40427415943203708442085

theorem tailTrace_708589 : CollatzResearch.WordTrace tailWord_708589 prefixEnd_708589 40427415943203708442085 := by
  unfold tailWord_708589
  simp only [CollatzResearch.WordTrace]
  refine ⟨25844364029910545211624821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17229576019940363474416547 25844364029910545211624821)
  ·
    refine ⟨2422909127804113613589827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25844364029910545211624821 2422909127804113613589827)
    ·
      refine ⟨3634363691706170420384741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2422909127804113613589827 3634363691706170420384741)
      ·
        refine ⟨681443192194906953822139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3634363691706170420384741 681443192194906953822139)
        ·
          refine ⟨1022164788292360430733209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 681443192194906953822139 1022164788292360430733209)
          ·
            refine ⟨766623591219270323049907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1022164788292360430733209 766623591219270323049907)
            ·
              refine ⟨1149935386828905484574861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766623591219270323049907 1149935386828905484574861)
              ·
                refine ⟨431225770060839556715573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1149935386828905484574861 431225770060839556715573)
                ·
                  refine ⟨40427415943203708442085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 431225770060839556715573 40427415943203708442085)
                  ·
                    rfl

theorem cell23_708589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_708589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708589 prefixEnd_708589 := by exact prefixLift 708589
  have htrace : WordTrace (prefixWord ++ tailWord_708589) baseStart_708589 baseEnd_708589 := by
    simpa [prefixWord, tailWord_708589, baseEnd_708589] using wordTrace_append hprefix tailTrace_708589
  have hstable : (prefixWord ++ tailWord_708589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708589).length < 2 ^ (prefixWord ++ tailWord_708589).sum := by decide
  have hdescent : baseEnd_708589 < baseStart_708589 := by decide
  rcases family_descends (prefixWord ++ tailWord_708589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708615 : List Nat := [1, 1, 4, 3, 1, 2, 3, 1, 3, 4]
def baseStart_708615 : Nat := 118140960795 + 708615 * 2 ^ 59
def prefixEnd_708615 : Nat := 4983230072969 + 3 ^ 40 * 708615 * 2
def baseEnd_708615 : Nat := 121286697995283424751215

theorem tailTrace_708615 : CollatzResearch.WordTrace tailWord_708615 prefixEnd_708615 121286697995283424751215 := by
  unfold tailWord_708615
  simp only [CollatzResearch.WordTrace]
  refine ⟨25845312327816351652071299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17230208218544234434714199 25845312327816351652071299)
  ·
    refine ⟨38767968491724527478106949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25845312327816351652071299 38767968491724527478106949)
    ·
      refine ⟨7268994092198348902145053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38767968491724527478106949 7268994092198348902145053)
      ·
        refine ⟨2725872784574380838304395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7268994092198348902145053 2725872784574380838304395)
        ·
          refine ⟨4088809176861571257456593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2725872784574380838304395 4088809176861571257456593)
          ·
            refine ⟨3066606882646178443092445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4088809176861571257456593 3066606882646178443092445)
            ·
              refine ⟨1149977580992316916159667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3066606882646178443092445 1149977580992316916159667)
              ·
                refine ⟨1724966371488475374239501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1149977580992316916159667 1724966371488475374239501)
                ·
                  refine ⟨646862389308178265339813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1724966371488475374239501 646862389308178265339813)
                  ·
                    refine ⟨121286697995283424751215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 646862389308178265339813 121286697995283424751215)
                    ·
                      rfl

theorem cell23_708615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_708615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708615 prefixEnd_708615 := by exact prefixLift 708615
  have htrace : WordTrace (prefixWord ++ tailWord_708615) baseStart_708615 baseEnd_708615 := by
    simpa [prefixWord, tailWord_708615, baseEnd_708615] using wordTrace_append hprefix tailTrace_708615
  have hstable : (prefixWord ++ tailWord_708615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708615).length < 2 ^ (prefixWord ++ tailWord_708615).sum := by decide
  have hdescent : baseEnd_708615 < baseStart_708615 := by decide
  rcases family_descends (prefixWord ++ tailWord_708615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708651 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 5]
def baseStart_708651 : Nat := 118140960795 + 708651 * 2 ^ 59
def prefixEnd_708651 : Nat := 4983230072969 + 3 ^ 40 * 708651 * 2
def baseEnd_708651 : Nat := 363878579289412133403479

theorem tailTrace_708651 : CollatzResearch.WordTrace tailWord_708651 prefixEnd_708651 363878579289412133403479 := by
  unfold tailWord_708651
  simp only [CollatzResearch.WordTrace]
  refine ⟨25846625355685929800381807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17231083570457286533587871 25846625355685929800381807)
  ·
    refine ⟨38769938033528894700572711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25846625355685929800381807 38769938033528894700572711)
    ·
      refine ⟨58154907050293342050859067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38769938033528894700572711 58154907050293342050859067)
      ·
        refine ⟨87232360575440013076288601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58154907050293342050859067 87232360575440013076288601)
        ·
          refine ⟨65424270431580009807216451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87232360575440013076288601 65424270431580009807216451)
          ·
            refine ⟨98136405647370014710824677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65424270431580009807216451 98136405647370014710824677)
            ·
              refine ⟨18400576058881877758279627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98136405647370014710824677 18400576058881877758279627)
              ·
                refine ⟨27600864088322816637419441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18400576058881877758279627 27600864088322816637419441)
                ·
                  refine ⟨20700648066242112478064581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27600864088322816637419441 20700648066242112478064581)
                  ·
                    refine ⟨3881371512420396089637109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20700648066242112478064581 3881371512420396089637109)
                    ·
                      refine ⟨363878579289412133403479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3881371512420396089637109 363878579289412133403479)
                      ·
                        rfl

theorem cell23_708651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 5].length) (baseStart_708651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708651 prefixEnd_708651 := by exact prefixLift 708651
  have htrace : WordTrace (prefixWord ++ tailWord_708651) baseStart_708651 baseEnd_708651 := by
    simpa [prefixWord, tailWord_708651, baseEnd_708651] using wordTrace_append hprefix tailTrace_708651
  have hstable : (prefixWord ++ tailWord_708651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708651).length < 2 ^ (prefixWord ++ tailWord_708651).sum := by decide
  have hdescent : baseEnd_708651 < baseStart_708651 := by decide
  rcases family_descends (prefixWord ++ tailWord_708651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708688 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 8, 4]
def baseStart_708688 : Nat := 118140960795 + 708688 * 2 ^ 59
def prefixEnd_708688 : Nat := 4983230072969 + 3 ^ 40 * 708688 * 2
def baseEnd_708688 : Nat := 121299192691209496213603

theorem tailTrace_708688 : CollatzResearch.WordTrace tailWord_708688 prefixEnd_708688 121299192691209496213603 := by
  unfold tailWord_708688
  simp only [CollatzResearch.WordTrace]
  refine ⟨12923987428275942559739359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17231983237701256746319145 12923987428275942559739359)
  ·
    refine ⟨19385981142413913839609039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12923987428275942559739359 19385981142413913839609039)
    ·
      refine ⟨29078971713620870759413559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19385981142413913839609039 29078971713620870759413559)
      ·
        refine ⟨43618457570431306139120339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29078971713620870759413559 43618457570431306139120339)
        ·
          refine ⟨65427686355646959208680509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43618457570431306139120339 65427686355646959208680509)
          ·
            refine ⟨24535382383367609703255191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65427686355646959208680509 24535382383367609703255191)
            ·
              refine ⟨36803073575051414554882787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24535382383367609703255191 36803073575051414554882787)
              ·
                refine ⟨55204610362577121832324181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36803073575051414554882787 55204610362577121832324181)
                ·
                  refine ⟨646929027686450646472549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 55204610362577121832324181 646929027686450646472549)
                  ·
                    refine ⟨121299192691209496213603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 646929027686450646472549 121299192691209496213603)
                    ·
                      rfl

theorem cell23_708688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 8, 4].length) (baseStart_708688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708688 prefixEnd_708688 := by exact prefixLift 708688
  have htrace : WordTrace (prefixWord ++ tailWord_708688) baseStart_708688 baseEnd_708688 := by
    simpa [prefixWord, tailWord_708688, baseEnd_708688] using wordTrace_append hprefix tailTrace_708688
  have hstable : (prefixWord ++ tailWord_708688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708688).length < 2 ^ (prefixWord ++ tailWord_708688).sum := by decide
  have hdescent : baseEnd_708688 < baseStart_708688 := by decide
  rcases family_descends (prefixWord ++ tailWord_708688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708718 : List Nat := [4, 1, 2, 2, 1, 1, 12]
def baseStart_708718 : Nat := 118140960795 + 708718 * 2 ^ 59
def prefixEnd_708718 : Nat := 4983230072969 + 3 ^ 40 * 708718 * 2
def baseEnd_708718 : Nat := 4492752870287202114391

theorem tailTrace_708718 : CollatzResearch.WordTrace tailWord_708718 prefixEnd_708718 4492752870287202114391 := by
  unfold tailWord_708718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3231133630805400030383851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17232712697628800162047205 3231133630805400030383851)
  ·
    refine ⟨4846700446208100045575777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3231133630805400030383851 4846700446208100045575777)
    ·
      refine ⟨3635025334656075034181833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4846700446208100045575777 3635025334656075034181833)
      ·
        refine ⟨2726269000992056275636375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3635025334656075034181833 2726269000992056275636375)
        ·
          refine ⟨4089403501488084413454563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2726269000992056275636375 4089403501488084413454563)
          ·
            refine ⟨6134105252232126620181845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4089403501488084413454563 6134105252232126620181845)
            ·
              refine ⟨4492752870287202114391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 6134105252232126620181845 4492752870287202114391)
              ·
                rfl

theorem cell23_708718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 12].length) (baseStart_708718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708718 prefixEnd_708718 := by exact prefixLift 708718
  have htrace : WordTrace (prefixWord ++ tailWord_708718) baseStart_708718 baseEnd_708718 := by
    simpa [prefixWord, tailWord_708718, baseEnd_708718] using wordTrace_append hprefix tailTrace_708718
  have hstable : (prefixWord ++ tailWord_708718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708718).length < 2 ^ (prefixWord ++ tailWord_708718).sum := by decide
  have hdescent : baseEnd_708718 < baseStart_708718 := by decide
  rcases family_descends (prefixWord ++ tailWord_708718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708722 : List Nat := [3, 2, 1, 2, 2, 2, 3, 2, 2, 4]
def baseStart_708722 : Nat := 118140960795 + 708722 * 2 ^ 59
def prefixEnd_708722 : Nat := 4983230072969 + 3 ^ 40 * 708722 * 2
def baseEnd_708722 : Nat := 121305012138627118538551

theorem tailTrace_708722 : CollatzResearch.WordTrace tailWord_708722 prefixEnd_708722 121305012138627118538551 := by
  unfold tailWord_708722
  simp only [CollatzResearch.WordTrace]
  refine ⟨6462303734607177231554105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17232809958952472617477613 6462303734607177231554105)
  ·
    refine ⟨4846727800955382923665579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6462303734607177231554105 4846727800955382923665579)
    ·
      refine ⟨7270091701433074385498369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4846727800955382923665579 7270091701433074385498369)
      ·
        refine ⟨5452568776074805789123777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7270091701433074385498369 5452568776074805789123777)
        ·
          refine ⟨4089426582056104341842833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5452568776074805789123777 4089426582056104341842833)
          ·
            refine ⟨3067069936542078256382125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4089426582056104341842833 3067069936542078256382125)
            ·
              refine ⟨1150151226203279346143297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3067069936542078256382125 1150151226203279346143297)
              ·
                refine ⟨862613419652459509607473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1150151226203279346143297 862613419652459509607473)
                ·
                  refine ⟨646960064739344632205605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 862613419652459509607473 646960064739344632205605)
                  ·
                    refine ⟨121305012138627118538551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 646960064739344632205605 121305012138627118538551)
                    ·
                      rfl

theorem cell23_708722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_708722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708722 prefixEnd_708722 := by exact prefixLift 708722
  have htrace : WordTrace (prefixWord ++ tailWord_708722) baseStart_708722 baseEnd_708722 := by
    simpa [prefixWord, tailWord_708722, baseEnd_708722] using wordTrace_append hprefix tailTrace_708722
  have hstable : (prefixWord ++ tailWord_708722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708722).length < 2 ^ (prefixWord ++ tailWord_708722).sum := by decide
  have hdescent : baseEnd_708722 < baseStart_708722 := by decide
  rcases family_descends (prefixWord ++ tailWord_708722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708729 : List Nat := [1, 2, 1, 3, 4, 2, 2, 1, 3, 2, 2]
def baseStart_708729 : Nat := 118140960795 + 708729 * 2 ^ 59
def prefixEnd_708729 : Nat := 4983230072969 + 3 ^ 40 * 708729 * 2
def baseEnd_708729 : Nat := 363918630780462828228121

theorem tailTrace_708729 : CollatzResearch.WordTrace tailWord_708729 prefixEnd_708729 363918630780462828228121 := by
  unfold tailWord_708729
  simp only [CollatzResearch.WordTrace]
  refine ⟨25849470249403349121721241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17232980166268899414480827 25849470249403349121721241)
  ·
    refine ⟨19387102687052511841290931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25849470249403349121721241 19387102687052511841290931)
    ·
      refine ⟨29080654030578767761936397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19387102687052511841290931 29080654030578767761936397)
      ·
        refine ⟨10905245261467037910726149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29080654030578767761936397 10905245261467037910726149)
        ·
          refine ⟨2044733486525069608261153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10905245261467037910726149 2044733486525069608261153)
          ·
            refine ⟨1533550114893802206195865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2044733486525069608261153 1533550114893802206195865)
            ·
              refine ⟨1150162586170351654646899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1533550114893802206195865 1150162586170351654646899)
              ·
                refine ⟨1725243879255527481970349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1150162586170351654646899 1725243879255527481970349)
                ·
                  refine ⟨646966454720822805738881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1725243879255527481970349 646966454720822805738881)
                  ·
                    refine ⟨485224841040617104304161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 646966454720822805738881 485224841040617104304161)
                    ·
                      refine ⟨363918630780462828228121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 485224841040617104304161 363918630780462828228121)
                      ·
                        rfl

theorem cell23_708729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 2, 2].length) (baseStart_708729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708729 prefixEnd_708729 := by exact prefixLift 708729
  have htrace : WordTrace (prefixWord ++ tailWord_708729) baseStart_708729 baseEnd_708729 := by
    simpa [prefixWord, tailWord_708729, baseEnd_708729] using wordTrace_append hprefix tailTrace_708729
  have hstable : (prefixWord ++ tailWord_708729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708729).length < 2 ^ (prefixWord ++ tailWord_708729).sum := by decide
  have hdescent : baseEnd_708729 < baseStart_708729 := by decide
  rcases family_descends (prefixWord ++ tailWord_708729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708808 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 9]
def baseStart_708808 : Nat := 118140960795 + 708808 * 2 ^ 59
def prefixEnd_708808 : Nat := 4983230072969 + 3 ^ 40 * 708808 * 2
def baseEnd_708808 : Nat := 40439910639129779904473

theorem tailTrace_708808 : CollatzResearch.WordTrace tailWord_708808 prefixEnd_708808 40439910639129779904473 := by
  unfold tailWord_708808
  simp only [CollatzResearch.WordTrace]
  refine ⟨12926175808058572806923539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17234901077411430409231385 12926175808058572806923539)
  ·
    refine ⟨19389263712087859210385309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12926175808058572806923539 19389263712087859210385309)
    ·
      refine ⟨7270973892032947203894491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19389263712087859210385309 7270973892032947203894491)
      ·
        refine ⟨10906460838049420805841737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7270973892032947203894491 10906460838049420805841737)
        ·
          refine ⟨8179845628537065604381303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10906460838049420805841737 8179845628537065604381303)
          ·
            refine ⟨12269768442805598406571955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8179845628537065604381303 12269768442805598406571955)
            ·
              refine ⟨18404652664208397609857933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12269768442805598406571955 18404652664208397609857933)
              ·
                refine ⟨6901744749078149103696725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18404652664208397609857933 6901744749078149103696725)
                ·
                  refine ⟨40439910639129779904473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6901744749078149103696725 40439910639129779904473)
                  ·
                    rfl

theorem cell23_708808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 9].length) (baseStart_708808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708808 prefixEnd_708808 := by exact prefixLift 708808
  have htrace : WordTrace (prefixWord ++ tailWord_708808) baseStart_708808 baseEnd_708808 := by
    simpa [prefixWord, tailWord_708808, baseEnd_708808] using wordTrace_append hprefix tailTrace_708808
  have hstable : (prefixWord ++ tailWord_708808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708808).length < 2 ^ (prefixWord ++ tailWord_708808).sum := by decide
  have hdescent : baseEnd_708808 < baseStart_708808 := by decide
  rcases family_descends (prefixWord ++ tailWord_708808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708842 : List Nat := [3, 1, 3, 1, 1, 2, 3, 4, 5]
def baseStart_708842 : Nat := 118140960795 + 708842 * 2 ^ 59
def prefixEnd_708842 : Nat := 4983230072969 + 3 ^ 40 * 708842 * 2
def baseEnd_708842 : Nat := 40441850454935654012789

theorem tailTrace_708842 : CollatzResearch.WordTrace tailWord_708842 prefixEnd_708842 40441850454935654012789 := by
  unfold tailWord_708842
  simp only [CollatzResearch.WordTrace]
  refine ⟨6463397924498492355146195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17235727798662646280389853 6463397924498492355146195)
  ·
    refine ⟨9695096886747738532719293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6463397924498492355146195 9695096886747738532719293)
    ·
      refine ⟨3635661332530401949769735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9695096886747738532719293 3635661332530401949769735)
      ·
        refine ⟨5453491998795602924654603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3635661332530401949769735 5453491998795602924654603)
        ·
          refine ⟨8180237998193404386981905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5453491998795602924654603 8180237998193404386981905)
          ·
            refine ⟨6135178498645053290236429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8180237998193404386981905 6135178498645053290236429)
            ·
              refine ⟨2300691936991894983838661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6135178498645053290236429 2300691936991894983838661)
              ·
                refine ⟨431379738185980309469749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2300691936991894983838661 431379738185980309469749)
                ·
                  refine ⟨40441850454935654012789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 431379738185980309469749 40441850454935654012789)
                  ·
                    rfl

theorem cell23_708842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 5].length) (baseStart_708842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708842 prefixEnd_708842 := by exact prefixLift 708842
  have htrace : WordTrace (prefixWord ++ tailWord_708842) baseStart_708842 baseEnd_708842 := by
    simpa [prefixWord, tailWord_708842, baseEnd_708842] using wordTrace_append hprefix tailTrace_708842
  have hstable : (prefixWord ++ tailWord_708842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708842).length < 2 ^ (prefixWord ++ tailWord_708842).sum := by decide
  have hdescent : baseEnd_708842 < baseStart_708842 := by decide
  rcases family_descends (prefixWord ++ tailWord_708842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708872 : List Nat := [2, 1, 3, 2, 3, 1, 3, 1, 2, 5]
def baseStart_708872 : Nat := 118140960795 + 708872 * 2 ^ 59
def prefixEnd_708872 : Nat := 4983230072969 + 3 ^ 40 * 708872 * 2
def baseEnd_708872 : Nat := 121330686171351922913321

theorem tailTrace_708872 : CollatzResearch.WordTrace tailWord_708872 prefixEnd_708872 121330686171351922913321 := by
  unfold tailWord_708872
  simp only [CollatzResearch.WordTrace]
  refine ⟨12927342943942642272088435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17236457258590189696117913 12927342943942642272088435)
  ·
    refine ⟨19391014415913963408132653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12927342943942642272088435 19391014415913963408132653)
    ·
      refine ⟨7271630405967736278049745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19391014415913963408132653 7271630405967736278049745)
      ·
        refine ⟨5453722804475802208537309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7271630405967736278049745 5453722804475802208537309)
        ·
          refine ⟨2045146051678425828201491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5453722804475802208537309 2045146051678425828201491)
          ·
            refine ⟨3067719077517638742302237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2045146051678425828201491 3067719077517638742302237)
            ·
              refine ⟨1150394654069114528363339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3067719077517638742302237 1150394654069114528363339)
              ·
                refine ⟨1725591981103671792545009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1150394654069114528363339 1725591981103671792545009)
                ·
                  refine ⟨1294193985827753844408757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1725591981103671792545009 1294193985827753844408757)
                  ·
                    refine ⟨121330686171351922913321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1294193985827753844408757 121330686171351922913321)
                    ·
                      rfl

theorem cell23_708872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_708872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708872 prefixEnd_708872 := by exact prefixLift 708872
  have htrace : WordTrace (prefixWord ++ tailWord_708872) baseStart_708872 baseEnd_708872 := by
    simpa [prefixWord, tailWord_708872, baseEnd_708872] using wordTrace_append hprefix tailTrace_708872
  have hstable : (prefixWord ++ tailWord_708872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708872).length < 2 ^ (prefixWord ++ tailWord_708872).sum := by decide
  have hdescent : baseEnd_708872 < baseStart_708872 := by decide
  rcases family_descends (prefixWord ++ tailWord_708872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708875 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 4]
def baseStart_708875 : Nat := 118140960795 + 708875 * 2 ^ 59
def prefixEnd_708875 : Nat := 4983230072969 + 3 ^ 40 * 708875 * 2
def baseEnd_708875 : Nat := 363993598956019257002449

theorem tailTrace_708875 : CollatzResearch.WordTrace tailWord_708875 prefixEnd_708875 363993598956019257002449 := by
  unfold tailWord_708875
  simp only [CollatzResearch.WordTrace]
  refine ⟨25854795306874416056536079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17236530204582944037690719 25854795306874416056536079)
  ·
    refine ⟨38782192960311624084804119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25854795306874416056536079 38782192960311624084804119)
    ·
      refine ⟨58173289440467436127206179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38782192960311624084804119 58173289440467436127206179)
      ·
        refine ⟨87259934160701154190809269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58173289440467436127206179 87259934160701154190809269)
        ·
          refine ⟨8180618827565733205388369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87259934160701154190809269 8180618827565733205388369)
          ·
            refine ⟨6135464120674299904041277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8180618827565733205388369 6135464120674299904041277)
            ·
              refine ⟨2300799045252862464015479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6135464120674299904041277 2300799045252862464015479)
              ·
                refine ⟨3451198567879293696023219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2300799045252862464015479 3451198567879293696023219)
                ·
                  refine ⟨5176797851818940544034829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3451198567879293696023219 5176797851818940544034829)
                  ·
                    refine ⟨1941299194432102704013061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5176797851818940544034829 1941299194432102704013061)
                    ·
                      refine ⟨363993598956019257002449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1941299194432102704013061 363993598956019257002449)
                      ·
                        rfl

theorem cell23_708875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 4].length) (baseStart_708875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708875 prefixEnd_708875 := by exact prefixLift 708875
  have htrace : WordTrace (prefixWord ++ tailWord_708875) baseStart_708875 baseEnd_708875 := by
    simpa [prefixWord, tailWord_708875, baseEnd_708875] using wordTrace_append hprefix tailTrace_708875
  have hstable : (prefixWord ++ tailWord_708875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708875).length < 2 ^ (prefixWord ++ tailWord_708875).sum := by decide
  have hdescent : baseEnd_708875 < baseStart_708875 := by decide
  rcases family_descends (prefixWord ++ tailWord_708875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708952 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 3, 5, 2]
def baseStart_708952 : Nat := 118140960795 + 708952 * 2 ^ 59
def prefixEnd_708952 : Nat := 4983230072969 + 3 ^ 40 * 708952 * 2
def baseEnd_708952 : Nat := 364033136966415455739595

theorem tailTrace_708952 : CollatzResearch.WordTrace tailWord_708952 prefixEnd_708952 364033136966415455739595 := by
  unfold tailWord_708952
  simp only [CollatzResearch.WordTrace]
  refine ⟨12928801863797729103544555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17238402485063638804726073 12928801863797729103544555)
  ·
    refine ⟨19393202795696593655316833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12928801863797729103544555 19393202795696593655316833)
    ·
      refine ⟨14544902096772445241487625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19393202795696593655316833 14544902096772445241487625)
      ·
        refine ⟨10908676572579333931115719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14544902096772445241487625 10908676572579333931115719)
        ·
          refine ⟨16363014858869000896673579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10908676572579333931115719 16363014858869000896673579)
          ·
            refine ⟨24544522288303501345010369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16363014858869000896673579 24544522288303501345010369)
            ·
              refine ⟨18408391716227626008757777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24544522288303501345010369 18408391716227626008757777)
              ·
                refine ⟨13806293787170719506568333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18408391716227626008757777 13806293787170719506568333)
                ·
                  refine ⟨5177360170189019814963125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13806293787170719506568333 5177360170189019814963125)
                  ·
                    refine ⟨485377515955220607652793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5177360170189019814963125 485377515955220607652793)
                    ·
                      refine ⟨364033136966415455739595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 485377515955220607652793 364033136966415455739595)
                      ·
                        rfl

theorem cell23_708952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 3, 5, 2].length) (baseStart_708952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708952 prefixEnd_708952 := by exact prefixLift 708952
  have htrace : WordTrace (prefixWord ++ tailWord_708952) baseStart_708952 baseEnd_708952 := by
    simpa [prefixWord, tailWord_708952, baseEnd_708952] using wordTrace_append hprefix tailTrace_708952
  have hstable : (prefixWord ++ tailWord_708952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708952).length < 2 ^ (prefixWord ++ tailWord_708952).sum := by decide
  have hdescent : baseEnd_708952 < baseStart_708952 := by decide
  rcases family_descends (prefixWord ++ tailWord_708952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708959 : List Nat := [1, 1, 2, 3, 1, 2, 5, 1, 3, 1, 3]
def baseStart_708959 : Nat := 118140960795 + 708959 * 2 ^ 59
def prefixEnd_708959 : Nat := 4983230072969 + 3 ^ 40 * 708959 * 2
def baseEnd_708959 : Nat := 364036731330996928352063

theorem tailTrace_708959 : CollatzResearch.WordTrace tailWord_708959 prefixEnd_708959 364036731330996928352063 := by
  unfold tailWord_708959
  simp only [CollatzResearch.WordTrace]
  refine ⟨25857859038570098402593931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17238572692380065601729287 25857859038570098402593931)
  ·
    refine ⟨38786788557855147603890897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25857859038570098402593931 38786788557855147603890897)
    ·
      refine ⟨29090091418391360702918173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38786788557855147603890897 29090091418391360702918173)
      ·
        refine ⟨10908784281896760263594315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29090091418391360702918173 10908784281896760263594315)
        ·
          refine ⟨16363176422845140395391473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10908784281896760263594315 16363176422845140395391473)
          ·
            refine ⟨12272382317133855296543605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16363176422845140395391473 12272382317133855296543605)
            ·
              refine ⟨1150535842231298934050963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12272382317133855296543605 1150535842231298934050963)
              ·
                refine ⟨1725803763346948401076445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1150535842231298934050963 1725803763346948401076445)
                ·
                  refine ⟨647176411255105650403667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1725803763346948401076445 647176411255105650403667)
                  ·
                    refine ⟨970764616882658475605501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 647176411255105650403667 970764616882658475605501)
                    ·
                      refine ⟨364036731330996928352063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 970764616882658475605501 364036731330996928352063)
                      ·
                        rfl

theorem cell23_708959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_708959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_708959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_708959 prefixEnd_708959 := by exact prefixLift 708959
  have htrace : WordTrace (prefixWord ++ tailWord_708959) baseStart_708959 baseEnd_708959 := by
    simpa [prefixWord, tailWord_708959, baseEnd_708959] using wordTrace_append hprefix tailTrace_708959
  have hstable : (prefixWord ++ tailWord_708959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708959).length < 2 ^ (prefixWord ++ tailWord_708959).sum := by decide
  have hdescent : baseEnd_708959 < baseStart_708959 := by decide
  rcases family_descends (prefixWord ++ tailWord_708959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709049 : List Nat := [1, 2, 1, 4, 3, 1, 2, 2, 1, 3, 3]
def baseStart_709049 : Nat := 118140960795 + 709049 * 2 ^ 59
def prefixEnd_709049 : Nat := 4983230072969 + 3 ^ 40 * 709049 * 2
def baseEnd_709049 : Nat := 364082944589901576226649

theorem tailTrace_709049 : CollatzResearch.WordTrace tailWord_709049 prefixEnd_709049 364082944589901576226649 := by
  unfold tailWord_709049
  simp only [CollatzResearch.WordTrace]
  refine ⟨25861141608244043773370201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17240761072162695848913467 25861141608244043773370201)
  ·
    refine ⟨19395856206183032830027651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25861141608244043773370201 19395856206183032830027651)
    ·
      refine ⟨29093784309274549245041477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19395856206183032830027651 29093784309274549245041477)
      ·
        refine ⟨5455084557988977983445277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29093784309274549245041477 5455084557988977983445277)
        ·
          refine ⟨2045656709245866743791979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5455084557988977983445277 2045656709245866743791979)
          ·
            refine ⟨3068485063868800115687969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2045656709245866743791979 3068485063868800115687969)
            ·
              refine ⟨2301363797901600086765977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3068485063868800115687969 2301363797901600086765977)
              ·
                refine ⟨1726022848426200065074483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2301363797901600086765977 1726022848426200065074483)
                ·
                  refine ⟨2589034272639300097611725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1726022848426200065074483 2589034272639300097611725)
                  ·
                    refine ⟨970887852239737536604397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2589034272639300097611725 970887852239737536604397)
                    ·
                      refine ⟨364082944589901576226649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 970887852239737536604397 364082944589901576226649)
                      ·
                        rfl

theorem cell23_709049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_709049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709049 prefixEnd_709049 := by exact prefixLift 709049
  have htrace : WordTrace (prefixWord ++ tailWord_709049) baseStart_709049 baseEnd_709049 := by
    simpa [prefixWord, tailWord_709049, baseEnd_709049] using wordTrace_append hprefix tailTrace_709049
  have hstable : (prefixWord ++ tailWord_709049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709049).length < 2 ^ (prefixWord ++ tailWord_709049).sum := by decide
  have hdescent : baseEnd_709049 < baseStart_709049 := by decide
  rcases family_descends (prefixWord ++ tailWord_709049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709053 : List Nat := [1, 4, 1, 2, 2, 4, 2, 1, 1, 2, 3]
def baseStart_709053 : Nat := 118140960795 + 709053 * 2 ^ 59
def prefixEnd_709053 : Nat := 4983230072969 + 3 ^ 40 * 709053 * 2
def baseEnd_709053 : Nat := 364084998512519560576631

theorem tailTrace_709053 : CollatzResearch.WordTrace tailWord_709053 prefixEnd_709053 364084998512519560576631 := by
  unfold tailWord_709053
  simp only [CollatzResearch.WordTrace]
  refine ⟨25861287500229552456515813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17240858333486368304343875 25861287500229552456515813)
  ·
    refine ⟨4848991406293041085596715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25861287500229552456515813 4848991406293041085596715)
    ·
      refine ⟨7273487109439561628395073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4848991406293041085596715 7273487109439561628395073)
      ·
        refine ⟨5455115332079671221296305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7273487109439561628395073 5455115332079671221296305)
        ·
          refine ⟨4091336499059753415972229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5455115332079671221296305 4091336499059753415972229)
          ·
            refine ⟨767125593573703765494793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4091336499059753415972229 767125593573703765494793)
            ·
              refine ⟨575344195180277824121095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 767125593573703765494793 575344195180277824121095)
              ·
                refine ⟨863016292770416736181643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 575344195180277824121095 863016292770416736181643)
                ·
                  refine ⟨1294524439155625104272465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 863016292770416736181643 1294524439155625104272465)
                  ·
                    refine ⟨970893329366718828204349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1294524439155625104272465 970893329366718828204349)
                    ·
                      refine ⟨364084998512519560576631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 970893329366718828204349 364084998512519560576631)
                      ·
                        rfl

theorem cell23_709053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_709053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709053 prefixEnd_709053 := by exact prefixLift 709053
  have htrace : WordTrace (prefixWord ++ tailWord_709053) baseStart_709053 baseEnd_709053 := by
    simpa [prefixWord, tailWord_709053, baseEnd_709053] using wordTrace_append hprefix tailTrace_709053
  have hstable : (prefixWord ++ tailWord_709053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709053).length < 2 ^ (prefixWord ++ tailWord_709053).sum := by decide
  have hdescent : baseEnd_709053 < baseStart_709053 := by decide
  rcases family_descends (prefixWord ++ tailWord_709053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709060 : List Nat := [2, 3, 3, 2, 3, 1, 1, 2, 2, 4]
def baseStart_709060 : Nat := 118140960795 + 709060 * 2 ^ 59
def prefixEnd_709060 : Nat := 4983230072969 + 3 ^ 40 * 709060 * 2
def baseEnd_709060 : Nat := 121362864292367011063033

theorem tailTrace_709060 : CollatzResearch.WordTrace tailWord_709060 prefixEnd_709060 121362864292367011063033 := by
  unfold tailWord_709060
  simp only [CollatzResearch.WordTrace]
  refine ⟨12930771405602096326010317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17241028540802795101347089 12930771405602096326010317)
  ·
    refine ⟨4849039277100786122253869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12930771405602096326010317 4849039277100786122253869)
    ·
      refine ⟨1818389728912794795845201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4849039277100786122253869 1818389728912794795845201)
      ·
        refine ⟨1363792296684596096883901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1818389728912794795845201 1363792296684596096883901)
        ·
          refine ⟨511422111256723536331463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1363792296684596096883901 511422111256723536331463)
          ·
            refine ⟨767133166885085304497195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511422111256723536331463 767133166885085304497195)
            ·
              refine ⟨1150699750327627956745793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767133166885085304497195 1150699750327627956745793)
              ·
                refine ⟨863024812745720967559345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1150699750327627956745793 863024812745720967559345)
                ·
                  refine ⟨647268609559290725669509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 863024812745720967559345 647268609559290725669509)
                  ·
                    refine ⟨121362864292367011063033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 647268609559290725669509 121362864292367011063033)
                    ·
                      rfl

theorem cell23_709060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_709060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709060 prefixEnd_709060 := by exact prefixLift 709060
  have htrace : WordTrace (prefixWord ++ tailWord_709060) baseStart_709060 baseEnd_709060 := by
    simpa [prefixWord, tailWord_709060, baseEnd_709060] using wordTrace_append hprefix tailTrace_709060
  have hstable : (prefixWord ++ tailWord_709060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709060).length < 2 ^ (prefixWord ++ tailWord_709060).sum := by decide
  have hdescent : baseEnd_709060 < baseStart_709060 := by decide
  rcases family_descends (prefixWord ++ tailWord_709060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709082 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 2, 6]
def baseStart_709082 : Nat := 118140960795 + 709082 * 2 ^ 59
def prefixEnd_709082 : Nat := 4983230072969 + 3 ^ 40 * 709082 * 2
def baseEnd_709082 : Nat := 121366629817166649037999

theorem tailTrace_709082 : CollatzResearch.WordTrace tailWord_709082 prefixEnd_709082 121366629817166649037999 := by
  unfold tailWord_709082
  simp only [CollatzResearch.WordTrace]
  refine ⟨6465586304281122602330375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17241563478082993606214333 6465586304281122602330375)
  ·
    refine ⟨9698379456421683903495563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6465586304281122602330375 9698379456421683903495563)
    ·
      refine ⟨14547569184632525855243345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9698379456421683903495563 14547569184632525855243345)
      ·
        refine ⟨10910676888474394391432509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14547569184632525855243345 10910676888474394391432509)
        ·
          refine ⟨4091503833177897896787191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10910676888474394391432509 4091503833177897896787191)
          ·
            refine ⟨6137255749766846845180787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4091503833177897896787191 6137255749766846845180787)
            ·
              refine ⟨9205883624650270267771181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6137255749766846845180787 9205883624650270267771181)
              ·
                refine ⟨3452206359243851350414193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9205883624650270267771181 3452206359243851350414193)
                ·
                  refine ⟨2589154769432888512810645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3452206359243851350414193 2589154769432888512810645)
                  ·
                    refine ⟨121366629817166649037999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2589154769432888512810645 121366629817166649037999)
                    ·
                      rfl

theorem cell23_709082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_709082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709082 prefixEnd_709082 := by exact prefixLift 709082
  have htrace : WordTrace (prefixWord ++ tailWord_709082) baseStart_709082 baseEnd_709082 := by
    simpa [prefixWord, tailWord_709082, baseEnd_709082] using wordTrace_append hprefix tailTrace_709082
  have hstable : (prefixWord ++ tailWord_709082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709082).length < 2 ^ (prefixWord ++ tailWord_709082).sum := by decide
  have hdescent : baseEnd_709082 < baseStart_709082 := by decide
  rcases family_descends (prefixWord ++ tailWord_709082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709090 : List Nat := [3, 3, 3, 2, 2, 1, 2, 7]
def baseStart_709090 : Nat := 118140960795 + 709090 * 2 ^ 59
def prefixEnd_709090 : Nat := 4983230072969 + 3 ^ 40 * 709090 * 2
def baseEnd_709090 : Nat := 13485333233212441326443

theorem tailTrace_709090 : CollatzResearch.WordTrace tailWord_709090 prefixEnd_709090 13485333233212441326443 := by
  unfold tailWord_709090
  simp only [CollatzResearch.WordTrace]
  refine ⟨6465659250273876943903181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17241758000730338517075149 6465659250273876943903181)
  ·
    refine ⟨2424622218852703853963693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6465659250273876943903181 2424622218852703853963693)
    ·
      refine ⟨909233332069763945236385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2424622218852703853963693 909233332069763945236385)
      ·
        refine ⟨681924999052322958927289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 909233332069763945236385 681924999052322958927289)
        ·
          refine ⟨511443749289242219195467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 681924999052322958927289 511443749289242219195467)
          ·
            refine ⟨767165623933863328793201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511443749289242219195467 767165623933863328793201)
            ·
              refine ⟨575374217950397496594901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 767165623933863328793201 575374217950397496594901)
              ·
                refine ⟨13485333233212441326443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 575374217950397496594901 13485333233212441326443)
                ·
                  rfl

theorem cell23_709090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 7].length) (baseStart_709090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709090 prefixEnd_709090 := by exact prefixLift 709090
  have htrace : WordTrace (prefixWord ++ tailWord_709090) baseStart_709090 baseEnd_709090 := by
    simpa [prefixWord, tailWord_709090, baseEnd_709090] using wordTrace_append hprefix tailTrace_709090
  have hstable : (prefixWord ++ tailWord_709090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709090).length < 2 ^ (prefixWord ++ tailWord_709090).sum := by decide
  have hdescent : baseEnd_709090 < baseStart_709090 := by decide
  rcases family_descends (prefixWord ++ tailWord_709090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709196 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 2, 4, 2]
def baseStart_709196 : Nat := 118140960795 + 709196 * 2 ^ 59
def prefixEnd_709196 : Nat := 4983230072969 + 3 ^ 40 * 709196 * 2
def baseEnd_709196 : Nat := 364158426246112501088473

theorem tailTrace_709196 : CollatzResearch.WordTrace tailWord_709196 prefixEnd_709196 364158426246112501088473 := by
  unfold tailWord_709196
  simp only [CollatzResearch.WordTrace]
  refine ⟨12933251569355743939485721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17244335425807658585980961 12933251569355743939485721)
  ·
    refine ⟨9699938677016807954614291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12933251569355743939485721 9699938677016807954614291)
    ·
      refine ⟨14549908015525211931921437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9699938677016807954614291 14549908015525211931921437)
      ·
        refine ⟨5456215505821954474470539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14549908015525211931921437 5456215505821954474470539)
        ·
          refine ⟨8184323258732931711705809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5456215505821954474470539 8184323258732931711705809)
          ·
            refine ⟨6138242444049698783779357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8184323258732931711705809 6138242444049698783779357)
            ·
              refine ⟨2301840916518637043917259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6138242444049698783779357 2301840916518637043917259)
              ·
                refine ⟨3452761374777955565875889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2301840916518637043917259 3452761374777955565875889)
                ·
                  refine ⟨2589571031083466674406917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3452761374777955565875889 2589571031083466674406917)
                  ·
                    refine ⟨485544568328150001451297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2589571031083466674406917 485544568328150001451297)
                    ·
                      refine ⟨364158426246112501088473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 485544568328150001451297 364158426246112501088473)
                      ·
                        rfl

theorem cell23_709196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_709196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709196 prefixEnd_709196 := by exact prefixLift 709196
  have htrace : WordTrace (prefixWord ++ tailWord_709196) baseStart_709196 baseEnd_709196 := by
    simpa [prefixWord, tailWord_709196, baseEnd_709196] using wordTrace_append hprefix tailTrace_709196
  have hstable : (prefixWord ++ tailWord_709196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709196).length < 2 ^ (prefixWord ++ tailWord_709196).sum := by decide
  have hdescent : baseEnd_709196 < baseStart_709196 := by decide
  rcases family_descends (prefixWord ++ tailWord_709196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709199 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 3]
def baseStart_709199 : Nat := 118140960795 + 709199 * 2 ^ 59
def prefixEnd_709199 : Nat := 4983230072969 + 3 ^ 40 * 709199 * 2
def baseEnd_709199 : Nat := 364159966688075989350959

theorem tailTrace_709199 : CollatzResearch.WordTrace tailWord_709199 prefixEnd_709199 364159966688075989350959 := by
  unfold tailWord_709199
  simp only [CollatzResearch.WordTrace]
  refine ⟨25866612557700619391330651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17244408371800412927553767 25866612557700619391330651)
  ·
    refine ⟨38799918836550929086995977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25866612557700619391330651 38799918836550929086995977)
    ·
      refine ⟨29099939127413196815246983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38799918836550929086995977 29099939127413196815246983)
      ·
        refine ⟨43649908691119795222870475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29099939127413196815246983 43649908691119795222870475)
        ·
          refine ⟨65474863036679692834305713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43649908691119795222870475 65474863036679692834305713)
          ·
            refine ⟨49106147277509769625729285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65474863036679692834305713 49106147277509769625729285)
            ·
              refine ⟨9207402614533081804824241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49106147277509769625729285 9207402614533081804824241)
              ·
                refine ⟨6905551960899811353618181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9207402614533081804824241 6905551960899811353618181)
                ·
                  refine ⟨1294790992668714628803409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6905551960899811353618181 1294790992668714628803409)
                  ·
                    refine ⟨971093244501535971602557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1294790992668714628803409 971093244501535971602557)
                    ·
                      refine ⟨364159966688075989350959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 971093244501535971602557 364159966688075989350959)
                      ·
                        rfl

theorem cell23_709199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 3].length) (baseStart_709199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709199 prefixEnd_709199 := by exact prefixLift 709199
  have htrace : WordTrace (prefixWord ++ tailWord_709199) baseStart_709199 baseEnd_709199 := by
    simpa [prefixWord, tailWord_709199, baseEnd_709199] using wordTrace_append hprefix tailTrace_709199
  have hstable : (prefixWord ++ tailWord_709199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709199).length < 2 ^ (prefixWord ++ tailWord_709199).sum := by decide
  have hdescent : baseEnd_709199 < baseStart_709199 := by decide
  rcases family_descends (prefixWord ++ tailWord_709199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709216 : List Nat := [2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 3]
def baseStart_709216 : Nat := 118140960795 + 709216 * 2 ^ 59
def prefixEnd_709216 : Nat := 4983230072969 + 3 ^ 40 * 709216 * 2
def baseEnd_709216 : Nat := 364168695859202422838381

theorem tailTrace_709216 : CollatzResearch.WordTrace tailWord_709216 prefixEnd_709216 364168695859202422838381 := by
  unfold tailWord_709216
  simp only [CollatzResearch.WordTrace]
  refine ⟨12933616299319515647349751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17244821732426020863133001 12933616299319515647349751)
  ·
    refine ⟨19400424448979273471024627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12933616299319515647349751 19400424448979273471024627)
    ·
      refine ⟨29100636673468910206536941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19400424448979273471024627 29100636673468910206536941)
      ·
        refine ⟨10912738752550841327451353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29100636673468910206536941 10912738752550841327451353)
        ·
          refine ⟨8184554064413130995588515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10912738752550841327451353 8184554064413130995588515)
          ·
            refine ⟨12276831096619696493382773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8184554064413130995588515 12276831096619696493382773)
            ·
              refine ⟨1150952915308096546254635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12276831096619696493382773 1150952915308096546254635)
              ·
                refine ⟨1726429372962144819381953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1150952915308096546254635 1726429372962144819381953)
                ·
                  refine ⟨1294822029721608614536465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1726429372962144819381953 1294822029721608614536465)
                  ·
                    refine ⟨971116522291206460902349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1294822029721608614536465 971116522291206460902349)
                    ·
                      refine ⟨364168695859202422838381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 971116522291206460902349 364168695859202422838381)
                      ·
                        rfl

theorem cell23_709216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_709216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709216 prefixEnd_709216 := by exact prefixLift 709216
  have htrace : WordTrace (prefixWord ++ tailWord_709216) baseStart_709216 baseEnd_709216 := by
    simpa [prefixWord, tailWord_709216, baseEnd_709216] using wordTrace_append hprefix tailTrace_709216
  have hstable : (prefixWord ++ tailWord_709216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709216).length < 2 ^ (prefixWord ++ tailWord_709216).sum := by decide
  have hdescent : baseEnd_709216 < baseStart_709216 := by decide
  rcases family_descends (prefixWord ++ tailWord_709216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709274 : List Nat := [3, 1, 1, 6, 2, 1, 1, 3, 1, 4]
def baseStart_709274 : Nat := 118140960795 + 709274 * 2 ^ 59
def prefixEnd_709274 : Nat := 4983230072969 + 3 ^ 40 * 709274 * 2
def baseEnd_709274 : Nat := 121399492579054398637705

theorem tailTrace_709274 : CollatzResearch.WordTrace tailWord_709274 prefixEnd_709274 121399492579054398637705 := by
  unfold tailWord_709274
  simp only [CollatzResearch.WordTrace]
  refine ⟨6467337008107226800077719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17246232021619271466873917 6467337008107226800077719)
  ·
    refine ⟨9701005512160840200116579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6467337008107226800077719 9701005512160840200116579)
    ·
      refine ⟨14551508268241260300174869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9701005512160840200116579 14551508268241260300174869)
      ·
        refine ⟨682101950073809076570697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14551508268241260300174869 682101950073809076570697)
        ·
          refine ⟨511576462555356807428023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 682101950073809076570697 511576462555356807428023)
          ·
            refine ⟨767364693833035211142035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511576462555356807428023 767364693833035211142035)
            ·
              refine ⟨1151047040749552816713053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767364693833035211142035 1151047040749552816713053)
              ·
                refine ⟨431642640281082306267395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1151047040749552816713053 431642640281082306267395)
                ·
                  refine ⟨647463960421623459401093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 431642640281082306267395 647463960421623459401093)
                  ·
                    refine ⟨121399492579054398637705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 647463960421623459401093 121399492579054398637705)
                    ·
                      rfl

theorem cell23_709274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 1, 4].length) (baseStart_709274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709274 prefixEnd_709274 := by exact prefixLift 709274
  have htrace : WordTrace (prefixWord ++ tailWord_709274) baseStart_709274 baseEnd_709274 := by
    simpa [prefixWord, tailWord_709274, baseEnd_709274] using wordTrace_append hprefix tailTrace_709274
  have hstable : (prefixWord ++ tailWord_709274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709274).length < 2 ^ (prefixWord ++ tailWord_709274).sum := by decide
  have hdescent : baseEnd_709274 < baseStart_709274 := by decide
  rcases family_descends (prefixWord ++ tailWord_709274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709289 : List Nat := [1, 2, 1, 1, 1, 1, 2, 7, 1, 1, 5]
def baseStart_709289 : Nat := 118140960795 + 709289 * 2 ^ 59
def prefixEnd_709289 : Nat := 4983230072969 + 3 ^ 40 * 709289 * 2
def baseEnd_709289 : Nat := 364206179946980637225545

theorem tailTrace_709289 : CollatzResearch.WordTrace tailWord_709289 prefixEnd_709289 364206179946980637225545 := by
  unfold tailWord_709289
  simp only [CollatzResearch.WordTrace]
  refine ⟨25869895127374564762106921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17246596751583043174737947 25869895127374564762106921)
  ·
    refine ⟨19402421345530923571580191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25869895127374564762106921 19402421345530923571580191)
    ·
      refine ⟨29103632018296385357370287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19402421345530923571580191 29103632018296385357370287)
      ·
        refine ⟨43655448027444578036055431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29103632018296385357370287 43655448027444578036055431)
        ·
          refine ⟨65483172041166867054083147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43655448027444578036055431 65483172041166867054083147)
          ·
            refine ⟨98224758061750300581124721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65483172041166867054083147 98224758061750300581124721)
            ·
              refine ⟨73668568546312725435843541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98224758061750300581124721 73668568546312725435843541)
              ·
                refine ⟨1726607075304204502402583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 73668568546312725435843541 1726607075304204502402583)
                ·
                  refine ⟨2589910612956306753603875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1726607075304204502402583 2589910612956306753603875)
                  ·
                    refine ⟨3884865919434460130405813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2589910612956306753603875 3884865919434460130405813)
                    ·
                      refine ⟨364206179946980637225545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3884865919434460130405813 364206179946980637225545)
                      ·
                        rfl

theorem cell23_709289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 1, 5].length) (baseStart_709289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709289 prefixEnd_709289 := by exact prefixLift 709289
  have htrace : WordTrace (prefixWord ++ tailWord_709289) baseStart_709289 baseEnd_709289 := by
    simpa [prefixWord, tailWord_709289, baseEnd_709289] using wordTrace_append hprefix tailTrace_709289
  have hstable : (prefixWord ++ tailWord_709289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709289).length < 2 ^ (prefixWord ++ tailWord_709289).sum := by decide
  have hdescent : baseEnd_709289 < baseStart_709289 := by decide
  rcases family_descends (prefixWord ++ tailWord_709289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709296 : List Nat := [2, 1, 1, 1, 2, 1, 3, 6, 2, 4]
def baseStart_709296 : Nat := 118140960795 + 709296 * 2 ^ 59
def prefixEnd_709296 : Nat := 4983230072969 + 3 ^ 40 * 709296 * 2
def baseEnd_709296 : Nat := 121403258103854036612671

theorem tailTrace_709296 : CollatzResearch.WordTrace tailWord_709296 prefixEnd_709296 121403258103854036612671 := by
  unfold tailWord_709296
  simp only [CollatzResearch.WordTrace]
  refine ⟨12935075219174602478805871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17246766958899469971741161 12935075219174602478805871)
  ·
    refine ⟨19402612828761903718208807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12935075219174602478805871 19402612828761903718208807)
    ·
      refine ⟨29103919243142855577313211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19402612828761903718208807 29103919243142855577313211)
      ·
        refine ⟨43655878864714283365969817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29103919243142855577313211 43655878864714283365969817)
        ·
          refine ⟨32741909148535712524477363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43655878864714283365969817 32741909148535712524477363)
          ·
            refine ⟨49112863722803568786716045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32741909148535712524477363 49112863722803568786716045)
            ·
              refine ⟨18417323896051338295018517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49112863722803568786716045 18417323896051338295018517)
              ·
                refine ⟨863312057627406482578993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18417323896051338295018517 863312057627406482578993)
                ·
                  refine ⟨647484043220554861934245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 863312057627406482578993 647484043220554861934245)
                  ·
                    refine ⟨121403258103854036612671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 647484043220554861934245 121403258103854036612671)
                    ·
                      rfl

theorem cell23_709296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 2, 4].length) (baseStart_709296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709296 prefixEnd_709296 := by exact prefixLift 709296
  have htrace : WordTrace (prefixWord ++ tailWord_709296) baseStart_709296 baseEnd_709296 := by
    simpa [prefixWord, tailWord_709296, baseEnd_709296] using wordTrace_append hprefix tailTrace_709296
  have hstable : (prefixWord ++ tailWord_709296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709296).length < 2 ^ (prefixWord ++ tailWord_709296).sum := by decide
  have hdescent : baseEnd_709296 < baseStart_709296 := by decide
  rcases family_descends (prefixWord ++ tailWord_709296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709297 : List Nat := [1, 2, 2, 6, 1, 2, 1, 1, 3, 1, 3]
def baseStart_709297 : Nat := 118140960795 + 709297 * 2 ^ 59
def prefixEnd_709297 : Nat := 4983230072969 + 3 ^ 40 * 709297 * 2
def baseEnd_709297 : Nat := 364210287792216605925509

theorem tailTrace_709297 : CollatzResearch.WordTrace tailWord_709297 prefixEnd_709297 364210287792216605925509 := by
  unfold tailWord_709297
  simp only [CollatzResearch.WordTrace]
  refine ⟨25870186911345582128398145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17246791274230388085598763 25870186911345582128398145)
  ·
    refine ⟨19402640183509186596298609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25870186911345582128398145 19402640183509186596298609)
    ·
      refine ⟨14551980137631889947223957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19402640183509186596298609 14551980137631889947223957)
      ·
        refine ⟨682124068951494841276123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14551980137631889947223957 682124068951494841276123)
        ·
          refine ⟨1023186103427242261914185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682124068951494841276123 1023186103427242261914185)
          ·
            refine ⟨767389577570431696435639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1023186103427242261914185 767389577570431696435639)
            ·
              refine ⟨1151084366355647544653459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767389577570431696435639 1151084366355647544653459)
              ·
                refine ⟨1726626549533471316980189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1151084366355647544653459 1726626549533471316980189)
                ·
                  refine ⟨647484956075051743867571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1726626549533471316980189 647484956075051743867571)
                  ·
                    refine ⟨971227434112577615801357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 647484956075051743867571 971227434112577615801357)
                    ·
                      refine ⟨364210287792216605925509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 971227434112577615801357 364210287792216605925509)
                      ·
                        rfl

theorem cell23_709297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_709297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709297 prefixEnd_709297 := by exact prefixLift 709297
  have htrace : WordTrace (prefixWord ++ tailWord_709297) baseStart_709297 baseEnd_709297 := by
    simpa [prefixWord, tailWord_709297, baseEnd_709297] using wordTrace_append hprefix tailTrace_709297
  have hstable : (prefixWord ++ tailWord_709297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709297).length < 2 ^ (prefixWord ++ tailWord_709297).sum := by decide
  have hdescent : baseEnd_709297 < baseStart_709297 := by decide
  rcases family_descends (prefixWord ++ tailWord_709297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709299 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 6]
def baseStart_709299 : Nat := 118140960795 + 709299 * 2 ^ 59
def prefixEnd_709299 : Nat := 4983230072969 + 3 ^ 40 * 709299 * 2
def baseEnd_709299 : Nat := 364211314753525598100499

theorem tailTrace_709299 : CollatzResearch.WordTrace tailWord_709299 prefixEnd_709299 364211314753525598100499 := by
  unfold tailWord_709299
  simp only [CollatzResearch.WordTrace]
  refine ⟨25870259857338336469970951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17246839904892224313313967 25870259857338336469970951)
  ·
    refine ⟨38805389786007504704956427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25870259857338336469970951 38805389786007504704956427)
    ·
      refine ⟨58208084679011257057434641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38805389786007504704956427 58208084679011257057434641)
      ·
        refine ⟨43656063509258442793075981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58208084679011257057434641 43656063509258442793075981)
        ·
          refine ⟨16371023815971916047403493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43656063509258442793075981 16371023815971916047403493)
          ·
            refine ⟨3069566965494734258888155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16371023815971916047403493 3069566965494734258888155)
            ·
              refine ⟨4604350448242101388332233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3069566965494734258888155 4604350448242101388332233)
              ·
                refine ⟨3453262836181576041249175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4604350448242101388332233 3453262836181576041249175)
                ·
                  refine ⟨5179894254272364061873763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3453262836181576041249175 5179894254272364061873763)
                  ·
                    refine ⟨7769841381408546092810645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5179894254272364061873763 7769841381408546092810645)
                    ·
                      refine ⟨364211314753525598100499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7769841381408546092810645 364211314753525598100499)
                      ·
                        rfl

theorem cell23_709299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 6].length) (baseStart_709299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709299 prefixEnd_709299 := by exact prefixLift 709299
  have htrace : WordTrace (prefixWord ++ tailWord_709299) baseStart_709299 baseEnd_709299 := by
    simpa [prefixWord, tailWord_709299, baseEnd_709299] using wordTrace_append hprefix tailTrace_709299
  have hstable : (prefixWord ++ tailWord_709299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709299).length < 2 ^ (prefixWord ++ tailWord_709299).sum := by decide
  have hdescent : baseEnd_709299 < baseStart_709299 := by decide
  rcases family_descends (prefixWord ++ tailWord_709299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709306 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3]
def baseStart_709306 : Nat := 118140960795 + 709306 * 2 ^ 59
def prefixEnd_709306 : Nat := 4983230072969 + 3 ^ 40 * 709306 * 2
def baseEnd_709306 : Nat := 364214909118107070712967

theorem tailTrace_709306 : CollatzResearch.WordTrace tailWord_709306 prefixEnd_709306 364214909118107070712967 := by
  unfold tailWord_709306
  simp only [CollatzResearch.WordTrace]
  refine ⟨6467628792078244166368943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17247010112208651110317181 6467628792078244166368943)
  ·
    refine ⟨9701443188117366249553415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6467628792078244166368943 9701443188117366249553415)
    ·
      refine ⟨14552164782176049374330123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9701443188117366249553415 14552164782176049374330123)
      ·
        refine ⟨21828247173264074061495185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14552164782176049374330123 21828247173264074061495185)
        ·
          refine ⟨16371185379948055546121389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21828247173264074061495185 16371185379948055546121389)
          ·
            refine ⟨6139194517480520829795521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16371185379948055546121389 6139194517480520829795521)
            ·
              refine ⟨4604395888110390622346641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6139194517480520829795521 4604395888110390622346641)
              ·
                refine ⟨3453296916082792966759981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4604395888110390622346641 3453296916082792966759981)
                ·
                  refine ⟨1294986343531047362534993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3453296916082792966759981 1294986343531047362534993)
                  ·
                    refine ⟨971239757648285521901245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1294986343531047362534993 971239757648285521901245)
                    ·
                      refine ⟨364214909118107070712967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 971239757648285521901245 364214909118107070712967)
                      ·
                        rfl

theorem cell23_709306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3].length) (baseStart_709306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709306 prefixEnd_709306 := by exact prefixLift 709306
  have htrace : WordTrace (prefixWord ++ tailWord_709306) baseStart_709306 baseEnd_709306 := by
    simpa [prefixWord, tailWord_709306, baseEnd_709306] using wordTrace_append hprefix tailTrace_709306
  have hstable : (prefixWord ++ tailWord_709306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709306).length < 2 ^ (prefixWord ++ tailWord_709306).sum := by decide
  have hdescent : baseEnd_709306 < baseStart_709306 := by decide
  rcases family_descends (prefixWord ++ tailWord_709306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709309 : List Nat := [1, 4, 1, 2, 1, 3, 1, 10]
def baseStart_709309 : Nat := 118140960795 + 709309 * 2 ^ 59
def prefixEnd_709309 : Nat := 4983230072969 + 3 ^ 40 * 709309 * 2
def baseEnd_709309 : Nat := 13489498131854465147239

theorem tailTrace_709309 : CollatzResearch.WordTrace tailWord_709309 prefixEnd_709309 13489498131854465147239 := by
  unfold tailWord_709309
  simp only [CollatzResearch.WordTrace]
  refine ⟨25870624587302108177834981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17247083058201405451889987 25870624587302108177834981)
  ·
    refine ⟨4850742110119145283344059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25870624587302108177834981 4850742110119145283344059)
    ·
      refine ⟨7276113165178717925016089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4850742110119145283344059 7276113165178717925016089)
      ·
        refine ⟨5457084873884038443762067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7276113165178717925016089 5457084873884038443762067)
        ·
          refine ⟨8185627310826057665643101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5457084873884038443762067 8185627310826057665643101)
          ·
            refine ⟨3069610241559771624616163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8185627310826057665643101 3069610241559771624616163)
            ·
              refine ⟨4604415362339657436924245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3069610241559771624616163 4604415362339657436924245)
              ·
                refine ⟨13489498131854465147239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4604415362339657436924245 13489498131854465147239)
                ·
                  rfl

theorem cell23_709309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 10].length) (baseStart_709309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709309 prefixEnd_709309 := by exact prefixLift 709309
  have htrace : WordTrace (prefixWord ++ tailWord_709309) baseStart_709309 baseEnd_709309 := by
    simpa [prefixWord, tailWord_709309, baseEnd_709309] using wordTrace_append hprefix tailTrace_709309
  have hstable : (prefixWord ++ tailWord_709309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709309).length < 2 ^ (prefixWord ++ tailWord_709309).sum := by decide
  have hdescent : baseEnd_709309 < baseStart_709309 := by decide
  rcases family_descends (prefixWord ++ tailWord_709309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709316 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_709316 : Nat := 118140960795 + 709316 * 2 ^ 59
def prefixEnd_709316 : Nat := 4983230072969 + 3 ^ 40 * 709316 * 2
def baseEnd_709316 : Nat := 364220043924652031587921

theorem tailTrace_709316 : CollatzResearch.WordTrace tailWord_709316 prefixEnd_709316 364220043924652031587921 := by
  unfold tailWord_709316
  simp only [CollatzResearch.WordTrace]
  refine ⟨12935439949138374186669901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17247253265517832248893201 12935439949138374186669901)
  ·
    refine ⟨4850789980926890320001213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12935439949138374186669901 4850789980926890320001213)
    ·
      refine ⟨1819046242847583870000455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4850789980926890320001213 1819046242847583870000455)
      ·
        refine ⟨2728569364271375805000683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1819046242847583870000455 2728569364271375805000683)
        ·
          refine ⟨4092854046407063707501025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2728569364271375805000683 4092854046407063707501025)
          ·
            refine ⟨3069640534805297780625769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4092854046407063707501025 3069640534805297780625769)
            ·
              refine ⟨2302230401103973335469327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3069640534805297780625769 2302230401103973335469327)
              ·
                refine ⟨3453345601655960003203991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2302230401103973335469327 3453345601655960003203991)
                ·
                  refine ⟨5180018402483940004805987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3453345601655960003203991 5180018402483940004805987)
                  ·
                    refine ⟨7770027603725910007208981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5180018402483940004805987 7770027603725910007208981)
                    ·
                      refine ⟨364220043924652031587921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7770027603725910007208981 364220043924652031587921)
                      ·
                        rfl

theorem cell23_709316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_709316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709316 prefixEnd_709316 := by exact prefixLift 709316
  have htrace : WordTrace (prefixWord ++ tailWord_709316) baseStart_709316 baseEnd_709316 := by
    simpa [prefixWord, tailWord_709316, baseEnd_709316] using wordTrace_append hprefix tailTrace_709316
  have hstable : (prefixWord ++ tailWord_709316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709316).length < 2 ^ (prefixWord ++ tailWord_709316).sum := by decide
  have hdescent : baseEnd_709316 < baseStart_709316 := by decide
  rcases family_descends (prefixWord ++ tailWord_709316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709336 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 3, 3, 3]
def baseStart_709336 : Nat := 118140960795 + 709336 * 2 ^ 59
def prefixEnd_709336 : Nat := 4983230072969 + 3 ^ 40 * 709336 * 2
def baseEnd_709336 : Nat := 364230313537741953337829

theorem tailTrace_709336 : CollatzResearch.WordTrace tailWord_709336 prefixEnd_709336 364230313537741953337829 := by
  unfold tailWord_709336
  simp only [CollatzResearch.WordTrace]
  refine ⟨12935804679102145894533931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17247739572136194526045241 12935804679102145894533931)
  ·
    refine ⟨19403707018653218841800897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12935804679102145894533931 19403707018653218841800897)
    ·
      refine ⟨14552780263989914131350673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19403707018653218841800897 14552780263989914131350673)
      ·
        refine ⟨10914585197992435598513005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14552780263989914131350673 10914585197992435598513005)
        ·
          refine ⟨4092969449247163349442377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10914585197992435598513005 4092969449247163349442377)
          ·
            refine ⟨3069727086935372512081783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4092969449247163349442377 3069727086935372512081783)
            ·
              refine ⟨4604590630403058768122675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3069727086935372512081783 4604590630403058768122675)
              ·
                refine ⟨6906885945604588152184013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4604590630403058768122675 6906885945604588152184013)
                ·
                  refine ⟨2590082229601720557069005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6906885945604588152184013 2590082229601720557069005)
                  ·
                    refine ⟨971280836100645208900877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2590082229601720557069005 971280836100645208900877)
                    ·
                      refine ⟨364230313537741953337829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 971280836100645208900877 364230313537741953337829)
                      ·
                        rfl

theorem cell23_709336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_709336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709336 prefixEnd_709336 := by exact prefixLift 709336
  have htrace : WordTrace (prefixWord ++ tailWord_709336) baseStart_709336 baseEnd_709336 := by
    simpa [prefixWord, tailWord_709336, baseEnd_709336] using wordTrace_append hprefix tailTrace_709336
  have hstable : (prefixWord ++ tailWord_709336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709336).length < 2 ^ (prefixWord ++ tailWord_709336).sum := by decide
  have hdescent : baseEnd_709336 < baseStart_709336 := by decide
  rcases family_descends (prefixWord ++ tailWord_709336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709340 : List Nat := [2, 2, 5, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_709340 : Nat := 118140960795 + 709340 * 2 ^ 59
def prefixEnd_709340 : Nat := 4983230072969 + 3 ^ 40 * 709340 * 2
def baseEnd_709340 : Nat := 364232367460359937687811

theorem tailTrace_709340 : CollatzResearch.WordTrace tailWord_709340 prefixEnd_709340 364232367460359937687811 := by
  unfold tailWord_709340
  simp only [CollatzResearch.WordTrace]
  refine ⟨12935877625094900236106737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17247836833459866981475649 12935877625094900236106737)
  ·
    refine ⟨9701908218821175177080053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12935877625094900236106737 9701908218821175177080053)
    ·
      refine ⟨909553895514485172851255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9701908218821175177080053 909553895514485172851255)
      ·
        refine ⟨1364330843271727759276883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 909553895514485172851255 1364330843271727759276883)
        ·
          refine ⟨2046496264907591638915325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1364330843271727759276883 2046496264907591638915325)
          ·
            refine ⟨767436099340346864593247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2046496264907591638915325 767436099340346864593247)
            ·
              refine ⟨1151154149010520296889871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767436099340346864593247 1151154149010520296889871)
              ·
                refine ⟨1726731223515780445334807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1151154149010520296889871 1726731223515780445334807)
                ·
                  refine ⟨2590096835273670668002211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1726731223515780445334807 2590096835273670668002211)
                  ·
                    refine ⟨3885145252910506002003317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2590096835273670668002211 3885145252910506002003317)
                    ·
                      refine ⟨364232367460359937687811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3885145252910506002003317 364232367460359937687811)
                      ·
                        rfl

theorem cell23_709340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_709340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709340 prefixEnd_709340 := by exact prefixLift 709340
  have htrace : WordTrace (prefixWord ++ tailWord_709340) baseStart_709340 baseEnd_709340 := by
    simpa [prefixWord, tailWord_709340, baseEnd_709340] using wordTrace_append hprefix tailTrace_709340
  have hstable : (prefixWord ++ tailWord_709340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709340).length < 2 ^ (prefixWord ++ tailWord_709340).sum := by decide
  have hdescent : baseEnd_709340 < baseStart_709340 := by decide
  rcases family_descends (prefixWord ++ tailWord_709340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709353 : List Nat := [1, 2, 1, 1, 1, 2, 5, 4, 2, 1, 3]
def baseStart_709353 : Nat := 118140960795 + 709353 * 2 ^ 59
def prefixEnd_709353 : Nat := 4983230072969 + 3 ^ 40 * 709353 * 2
def baseEnd_709353 : Nat := 364239042708868386825251

theorem tailTrace_709353 : CollatzResearch.WordTrace tailWord_709353 prefixEnd_709353 364239042708868386825251 := by
  unfold tailWord_709353
  simp only [CollatzResearch.WordTrace]
  refine ⟨25872229399142703692436713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17248152932761802461624475 25872229399142703692436713)
  ·
    refine ⟨19404172049357027769327535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25872229399142703692436713 19404172049357027769327535)
    ·
      refine ⟨29106258074035541653991303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19404172049357027769327535 29106258074035541653991303)
      ·
        refine ⟨43659387111053312480986955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29106258074035541653991303 43659387111053312480986955)
        ·
          refine ⟨65489080666579968721480433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43659387111053312480986955 65489080666579968721480433)
          ·
            refine ⟨49116810499934976541110325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65489080666579968721480433 49116810499934976541110325)
            ·
              refine ⟨4604700984368904050729093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49116810499934976541110325 4604700984368904050729093)
              ·
                refine ⟨863381434569169509511705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4604700984368904050729093 863381434569169509511705)
                ·
                  refine ⟨647536075926877132133779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 863381434569169509511705 647536075926877132133779)
                  ·
                    refine ⟨971304113890315698200669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 647536075926877132133779 971304113890315698200669)
                    ·
                      refine ⟨364239042708868386825251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 971304113890315698200669 364239042708868386825251)
                      ·
                        rfl

theorem cell23_709353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 1, 3].length) (baseStart_709353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709353 prefixEnd_709353 := by exact prefixLift 709353
  have htrace : WordTrace (prefixWord ++ tailWord_709353) baseStart_709353 baseEnd_709353 := by
    simpa [prefixWord, tailWord_709353, baseEnd_709353] using wordTrace_append hprefix tailTrace_709353
  have hstable : (prefixWord ++ tailWord_709353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709353).length < 2 ^ (prefixWord ++ tailWord_709353).sum := by decide
  have hdescent : baseEnd_709353 < baseStart_709353 := by decide
  rcases family_descends (prefixWord ++ tailWord_709353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709380 : List Nat := [2, 3, 2, 2, 1, 1, 2, 4, 1, 3, 2]
def baseStart_709380 : Nat := 118140960795 + 709380 * 2 ^ 59
def prefixEnd_709380 : Nat := 4983230072969 + 3 ^ 40 * 709380 * 2
def baseEnd_709380 : Nat := 364252906686539781187627

theorem tailTrace_709380 : CollatzResearch.WordTrace tailWord_709380 prefixEnd_709380 364252906686539781187627 := by
  unfold tailWord_709380
  simp only [CollatzResearch.WordTrace]
  refine ⟨12936607085022443651834797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17248809446696591535779729 12936607085022443651834797)
  ·
    refine ⟨4851227656883416369438049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12936607085022443651834797 4851227656883416369438049)
    ·
      refine ⟨3638420742662562277078537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4851227656883416369438049 3638420742662562277078537)
      ·
        refine ⟨2728815556996921707808903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3638420742662562277078537 2728815556996921707808903)
        ·
          refine ⟨4093223335495382561713355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2728815556996921707808903 4093223335495382561713355)
          ·
            refine ⟨6139835003243073842570033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4093223335495382561713355 6139835003243073842570033)
            ·
              refine ⟨4604876252432305381927525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6139835003243073842570033 4604876252432305381927525)
              ·
                refine ⟨863414297331057259111411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4604876252432305381927525 863414297331057259111411)
                ·
                  refine ⟨1295121445996585888667117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 863414297331057259111411 1295121445996585888667117)
                  ·
                    refine ⟨485670542248719708250169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1295121445996585888667117 485670542248719708250169)
                    ·
                      refine ⟨364252906686539781187627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 485670542248719708250169 364252906686539781187627)
                      ·
                        rfl

theorem cell23_709380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_709380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709380 prefixEnd_709380 := by exact prefixLift 709380
  have htrace : WordTrace (prefixWord ++ tailWord_709380) baseStart_709380 baseEnd_709380 := by
    simpa [prefixWord, tailWord_709380, baseEnd_709380] using wordTrace_append hprefix tailTrace_709380
  have hstable : (prefixWord ++ tailWord_709380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709380).length < 2 ^ (prefixWord ++ tailWord_709380).sum := by decide
  have hdescent : baseEnd_709380 < baseStart_709380 := by decide
  rcases family_descends (prefixWord ++ tailWord_709380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709393 : List Nat := [1, 2, 2, 1, 1, 3, 4, 2, 1, 4, 2]
def baseStart_709393 : Nat := 118140960795 + 709393 * 2 ^ 59
def prefixEnd_709393 : Nat := 4983230072969 + 3 ^ 40 * 709393 * 2
def baseEnd_709393 : Nat := 364259581935048230325067

theorem tailTrace_709393 : CollatzResearch.WordTrace tailWord_709393 prefixEnd_709393 364259581935048230325067 := by
  unfold tailWord_709393
  simp only [CollatzResearch.WordTrace]
  refine ⟨25873688318997790523892833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17249125545998527015928555 25873688318997790523892833)
  ·
    refine ⟨19405266239248342892919625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25873688318997790523892833 19405266239248342892919625)
    ·
      refine ⟨14553949679436257169689719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19405266239248342892919625 14553949679436257169689719)
      ·
        refine ⟨21830924519154385754534579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14553949679436257169689719 21830924519154385754534579)
        ·
          refine ⟨32746386778731578631801869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21830924519154385754534579 32746386778731578631801869)
          ·
            refine ⟨12279895042024341986925701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32746386778731578631801869 12279895042024341986925701)
            ·
              refine ⟨2302480320379564122548569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12279895042024341986925701 2302480320379564122548569)
              ·
                refine ⟨1726860240284673091911427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2302480320379564122548569 1726860240284673091911427)
                ·
                  refine ⟨2590290360427009637867141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1726860240284673091911427 2590290360427009637867141)
                  ·
                    refine ⟨485679442580064307100089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2590290360427009637867141 485679442580064307100089)
                    ·
                      refine ⟨364259581935048230325067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 485679442580064307100089 364259581935048230325067)
                      ·
                        rfl

theorem cell23_709393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 4, 2].length) (baseStart_709393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709393 prefixEnd_709393 := by exact prefixLift 709393
  have htrace : WordTrace (prefixWord ++ tailWord_709393) baseStart_709393 baseEnd_709393 := by
    simpa [prefixWord, tailWord_709393, baseEnd_709393] using wordTrace_append hprefix tailTrace_709393
  have hstable : (prefixWord ++ tailWord_709393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709393).length < 2 ^ (prefixWord ++ tailWord_709393).sum := by decide
  have hdescent : baseEnd_709393 < baseStart_709393 := by decide
  rcases family_descends (prefixWord ++ tailWord_709393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709419 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 8]
def baseStart_709419 : Nat := 118140960795 + 709419 * 2 ^ 59
def prefixEnd_709419 : Nat := 4983230072969 + 3 ^ 40 * 709419 * 2
def baseEnd_709419 : Nat := 364272932432065128599947

theorem tailTrace_709419 : CollatzResearch.WordTrace tailWord_709419 prefixEnd_709419 364272932432065128599947 := by
  unfold tailWord_709419
  simp only [CollatzResearch.WordTrace]
  refine ⟨25874636616903596964339311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17249757744602397976226207 25874636616903596964339311)
  ·
    refine ⟨38811954925355395446508967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25874636616903596964339311 38811954925355395446508967)
    ·
      refine ⟨58217932388033093169763451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38811954925355395446508967 58217932388033093169763451)
      ·
        refine ⟨87326898582049639754645177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58217932388033093169763451 87326898582049639754645177)
        ·
          refine ⟨65495173936537229815983883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87326898582049639754645177 65495173936537229815983883)
          ·
            refine ⟨98242760904805844723975825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65495173936537229815983883 98242760904805844723975825)
            ·
              refine ⟨73682070678604383542981869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98242760904805844723975825 73682070678604383542981869)
              ·
                refine ⟨27630776504476643828618201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73682070678604383542981869 27630776504476643828618201)
                ·
                  refine ⟨20723082378357482871463651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27630776504476643828618201 20723082378357482871463651)
                  ·
                    refine ⟨31084623567536224307195477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20723082378357482871463651 31084623567536224307195477)
                    ·
                      refine ⟨364272932432065128599947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 31084623567536224307195477 364272932432065128599947)
                      ·
                        rfl

theorem cell23_709419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 8].length) (baseStart_709419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709419 prefixEnd_709419 := by exact prefixLift 709419
  have htrace : WordTrace (prefixWord ++ tailWord_709419) baseStart_709419 baseEnd_709419 := by
    simpa [prefixWord, tailWord_709419, baseEnd_709419] using wordTrace_append hprefix tailTrace_709419
  have hstable : (prefixWord ++ tailWord_709419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709419).length < 2 ^ (prefixWord ++ tailWord_709419).sum := by decide
  have hdescent : baseEnd_709419 < baseStart_709419 := by decide
  rcases family_descends (prefixWord ++ tailWord_709419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709421 : List Nat := [1, 5, 3, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_709421 : Nat := 118140960795 + 709421 * 2 ^ 59
def prefixEnd_709421 : Nat := 4983230072969 + 3 ^ 40 * 709421 * 2
def baseEnd_709421 : Nat := 364273959393374120774939

theorem tailTrace_709421 : CollatzResearch.WordTrace tailWord_709421 prefixEnd_709421 364273959393374120774939 := by
  unfold tailWord_709421
  simp only [CollatzResearch.WordTrace]
  refine ⟨25874709562896351305912117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17249806375264234203941411 25874709562896351305912117)
  ·
    refine ⟨2425754021521532934929261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25874709562896351305912117 2425754021521532934929261)
    ·
      refine ⟨909657758070574850598473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2425754021521532934929261 909657758070574850598473)
      ·
        refine ⟨682243318552931137948855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 909657758070574850598473 682243318552931137948855)
        ·
          refine ⟨1023364977829396706923283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682243318552931137948855 1023364977829396706923283)
          ·
            refine ⟨1535047466744095060384925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1023364977829396706923283 1535047466744095060384925)
            ·
              refine ⟨575642800029035647644347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1535047466744095060384925 575642800029035647644347)
              ·
                refine ⟨863464200043553471466521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 575642800029035647644347 863464200043553471466521)
                ·
                  refine ⟨647598150032665103599891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 863464200043553471466521 647598150032665103599891)
                  ·
                    refine ⟨971397225048997655399837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 647598150032665103599891 971397225048997655399837)
                    ·
                      refine ⟨364273959393374120774939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 971397225048997655399837 364273959393374120774939)
                      ·
                        rfl

theorem cell23_709421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_709421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709421 prefixEnd_709421 := by exact prefixLift 709421
  have htrace : WordTrace (prefixWord ++ tailWord_709421) baseStart_709421 baseEnd_709421 := by
    simpa [prefixWord, tailWord_709421, baseEnd_709421] using wordTrace_append hprefix tailTrace_709421
  have hstable : (prefixWord ++ tailWord_709421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709421).length < 2 ^ (prefixWord ++ tailWord_709421).sum := by decide
  have hdescent : baseEnd_709421 < baseStart_709421 := by decide
  rcases family_descends (prefixWord ++ tailWord_709421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709463 : List Nat := [1, 1, 3, 2, 4, 2, 1, 2, 2, 5]
def baseStart_709463 : Nat := 118140960795 + 709463 * 2 ^ 59
def prefixEnd_709463 : Nat := 4983230072969 + 3 ^ 40 * 709463 * 2
def baseEnd_709463 : Nat := 121431841860287652149915

theorem tailTrace_709463 : CollatzResearch.WordTrace tailWord_709463 prefixEnd_709463 121431841860287652149915 := by
  unfold tailWord_709463
  simp only [CollatzResearch.WordTrace]
  refine ⟨25876241428744192478941043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17250827619162794985960695 25876241428744192478941043)
  ·
    refine ⟨38814362143116288718411565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25876241428744192478941043 38814362143116288718411565)
    ·
      refine ⟨14555385803668608269404337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38814362143116288718411565 14555385803668608269404337)
      ·
        refine ⟨10916539352751456202053253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14555385803668608269404337 10916539352751456202053253)
        ·
          refine ⟨2046851128640898037884985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10916539352751456202053253 2046851128640898037884985)
          ·
            refine ⟨1535138346480673528413739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2046851128640898037884985 1535138346480673528413739)
            ·
              refine ⟨2302707519721010292620609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1535138346480673528413739 2302707519721010292620609)
              ·
                refine ⟨1727030639790757719465457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2302707519721010292620609 1727030639790757719465457)
                ·
                  refine ⟨1295272979843068289599093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1727030639790757719465457 1295272979843068289599093)
                  ·
                    refine ⟨121431841860287652149915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1295272979843068289599093 121431841860287652149915)
                    ·
                      rfl

theorem cell23_709463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_709463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709463 prefixEnd_709463 := by exact prefixLift 709463
  have htrace : WordTrace (prefixWord ++ tailWord_709463) baseStart_709463 baseEnd_709463 := by
    simpa [prefixWord, tailWord_709463, baseEnd_709463] using wordTrace_append hprefix tailTrace_709463
  have hstable : (prefixWord ++ tailWord_709463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709463).length < 2 ^ (prefixWord ++ tailWord_709463).sum := by decide
  have hdescent : baseEnd_709463 < baseStart_709463 := by decide
  rcases family_descends (prefixWord ++ tailWord_709463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709483 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 2, 4, 2]
def baseStart_709483 : Nat := 118140960795 + 709483 * 2 ^ 59
def prefixEnd_709483 : Nat := 4983230072969 + 3 ^ 40 * 709483 * 2
def baseEnd_709483 : Nat := 364305795193952878199653

theorem tailTrace_709483 : CollatzResearch.WordTrace tailWord_709483 prefixEnd_709483 364305795193952878199653 := by
  unfold tailWord_709483
  simp only [CollatzResearch.WordTrace]
  refine ⟨25876970888671735894669103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17251313925781157263112735 25876970888671735894669103)
  ·
    refine ⟨38815456333007603842003655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25876970888671735894669103 38815456333007603842003655)
    ·
      refine ⟨58223184499511405763005483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38815456333007603842003655 58223184499511405763005483)
      ·
        refine ⟨87334776749267108644508225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58223184499511405763005483 87334776749267108644508225)
        ·
          refine ⟨65501082561950331483381169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87334776749267108644508225 65501082561950331483381169)
          ·
            refine ⟨49125811921462748612535877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65501082561950331483381169 49125811921462748612535877)
            ·
              refine ⟨9211089735274265364850477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49125811921462748612535877 9211089735274265364850477)
              ·
                refine ⟨3454158650727849511818929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9211089735274265364850477 3454158650727849511818929)
                ·
                  refine ⟨2590618988045887133864197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3454158650727849511818929 2590618988045887133864197)
                  ·
                    refine ⟨485741060258603837599537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2590618988045887133864197 485741060258603837599537)
                    ·
                      refine ⟨364305795193952878199653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 485741060258603837599537 364305795193952878199653)
                      ·
                        rfl

theorem cell23_709483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 4, 2].length) (baseStart_709483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709483 prefixEnd_709483 := by exact prefixLift 709483
  have htrace : WordTrace (prefixWord ++ tailWord_709483) baseStart_709483 baseEnd_709483 := by
    simpa [prefixWord, tailWord_709483, baseEnd_709483] using wordTrace_append hprefix tailTrace_709483
  have hstable : (prefixWord ++ tailWord_709483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709483).length < 2 ^ (prefixWord ++ tailWord_709483).sum := by decide
  have hdescent : baseEnd_709483 < baseStart_709483 := by decide
  rcases family_descends (prefixWord ++ tailWord_709483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709503 : List Nat := [1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 3]
def baseStart_709503 : Nat := 118140960795 + 709503 * 2 ^ 59
def prefixEnd_709503 : Nat := 4983230072969 + 3 ^ 40 * 709503 * 2
def baseEnd_709503 : Nat := 364316064807042799949561

theorem tailTrace_709503 : CollatzResearch.WordTrace tailWord_709503 prefixEnd_709503 364316064807042799949561 := by
  unfold tailWord_709503
  simp only [CollatzResearch.WordTrace]
  refine ⟨25877700348599279310397163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17251800232399519540264775 25877700348599279310397163)
  ·
    refine ⟨38816550522898918965595745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25877700348599279310397163 38816550522898918965595745)
    ·
      refine ⟨29112412892174189224196809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38816550522898918965595745 29112412892174189224196809)
      ·
        refine ⟨21834309669130641918147607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29112412892174189224196809 21834309669130641918147607)
        ·
          refine ⟨32751464503695962877221411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21834309669130641918147607 32751464503695962877221411)
          ·
            refine ⟨49127196755543944315832117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32751464503695962877221411 49127196755543944315832117)
            ·
              refine ⟨4605674695832244779609261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49127196755543944315832117 4605674695832244779609261)
              ·
                refine ⟨1727128010937091792353473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4605674695832244779609261 1727128010937091792353473)
                ·
                  refine ⟨1295346008202818844265105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1727128010937091792353473 1295346008202818844265105)
                  ·
                    refine ⟨971509506152114133198829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1295346008202818844265105 971509506152114133198829)
                    ·
                      refine ⟨364316064807042799949561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 971509506152114133198829 364316064807042799949561)
                      ·
                        rfl

theorem cell23_709503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 3].length) (baseStart_709503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709503 prefixEnd_709503 := by exact prefixLift 709503
  have htrace : WordTrace (prefixWord ++ tailWord_709503) baseStart_709503 baseEnd_709503 := by
    simpa [prefixWord, tailWord_709503, baseEnd_709503] using wordTrace_append hprefix tailTrace_709503
  have hstable : (prefixWord ++ tailWord_709503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709503).length < 2 ^ (prefixWord ++ tailWord_709503).sum := by decide
  have hdescent : baseEnd_709503 < baseStart_709503 := by decide
  rcases family_descends (prefixWord ++ tailWord_709503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709560 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 1, 5, 2]
def baseStart_709560 : Nat := 118140960795 + 709560 * 2 ^ 59
def prefixEnd_709560 : Nat := 4983230072969 + 3 ^ 40 * 709560 * 2
def baseEnd_709560 : Nat := 364345333204349076936799

theorem tailTrace_709560 : CollatzResearch.WordTrace tailWord_709560 prefixEnd_709560 364345333204349076936799 := by
  unfold tailWord_709560
  simp only [CollatzResearch.WordTrace]
  refine ⟨12939889654696389022611067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17253186206261852030148089 12939889654696389022611067)
  ·
    refine ⟨19409834482044583533916601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12939889654696389022611067 19409834482044583533916601)
    ·
      refine ⟨14557375861533437650437451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19409834482044583533916601 14557375861533437650437451)
      ·
        refine ⟨21836063792300156475656177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14557375861533437650437451 21836063792300156475656177)
        ·
          refine ⟨16377047844225117356742133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21836063792300156475656177 16377047844225117356742133)
          ·
            refine ⟨1535348235396104752194575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16377047844225117356742133 1535348235396104752194575)
            ·
              refine ⟨2303022353094157128291863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1535348235396104752194575 2303022353094157128291863)
              ·
                refine ⟨3454533529641235692437795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2303022353094157128291863 3454533529641235692437795)
                ·
                  refine ⟨5181800294461853538656693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3454533529641235692437795 5181800294461853538656693)
                  ·
                    refine ⟨485793777605798769249065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5181800294461853538656693 485793777605798769249065)
                    ·
                      refine ⟨364345333204349076936799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 485793777605798769249065 364345333204349076936799)
                      ·
                        rfl

theorem cell23_709560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 1, 5, 2].length) (baseStart_709560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709560 prefixEnd_709560 := by exact prefixLift 709560
  have htrace : WordTrace (prefixWord ++ tailWord_709560) baseStart_709560 baseEnd_709560 := by
    simpa [prefixWord, tailWord_709560, baseEnd_709560] using wordTrace_append hprefix tailTrace_709560
  have hstable : (prefixWord ++ tailWord_709560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709560).length < 2 ^ (prefixWord ++ tailWord_709560).sum := by decide
  have hdescent : baseEnd_709560 < baseStart_709560 := by decide
  rcases family_descends (prefixWord ++ tailWord_709560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709593 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 3, 1, 5]
def baseStart_709593 : Nat := 118140960795 + 709593 * 2 ^ 59
def prefixEnd_709593 : Nat := 4983230072969 + 3 ^ 40 * 709593 * 2
def baseEnd_709593 : Nat := 364362278065947447824147

theorem tailTrace_709593 : CollatzResearch.WordTrace tailWord_709593 prefixEnd_709593 364362278065947447824147 := by
  unfold tailWord_709593
  simp only [CollatzResearch.WordTrace]
  refine ⟨25880982918273224681173433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17253988612182149787448955 25880982918273224681173433)
  ·
    refine ⟨19410737188704918510880075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25880982918273224681173433 19410737188704918510880075)
    ·
      refine ⟨29116105783057377766320113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19410737188704918510880075 29116105783057377766320113)
      ·
        refine ⟨21837079337293033324740085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29116105783057377766320113 21837079337293033324740085)
        ·
          refine ⟨2047226187871221874194383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21837079337293033324740085 2047226187871221874194383)
          ·
            refine ⟨3070839281806832811291575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2047226187871221874194383 3070839281806832811291575)
            ·
              refine ⟨4606258922710249216937363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3070839281806832811291575 4606258922710249216937363)
              ·
                refine ⟨6909388384065373825406045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4606258922710249216937363 6909388384065373825406045)
                ·
                  refine ⟨2591020644024515184527267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6909388384065373825406045 2591020644024515184527267)
                  ·
                    refine ⟨3886530966036772776790901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2591020644024515184527267 3886530966036772776790901)
                    ·
                      refine ⟨364362278065947447824147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3886530966036772776790901 364362278065947447824147)
                      ·
                        rfl

theorem cell23_709593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_709593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709593 prefixEnd_709593 := by exact prefixLift 709593
  have htrace : WordTrace (prefixWord ++ tailWord_709593) baseStart_709593 baseEnd_709593 := by
    simpa [prefixWord, tailWord_709593, baseEnd_709593] using wordTrace_append hprefix tailTrace_709593
  have hstable : (prefixWord ++ tailWord_709593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709593).length < 2 ^ (prefixWord ++ tailWord_709593).sum := by decide
  have hdescent : baseEnd_709593 < baseStart_709593 := by decide
  rcases family_descends (prefixWord ++ tailWord_709593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709603 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 6]
def baseStart_709603 : Nat := 118140960795 + 709603 * 2 ^ 59
def prefixEnd_709603 : Nat := 4983230072969 + 3 ^ 40 * 709603 * 2
def baseEnd_709603 : Nat := 364367412872492408699101

theorem tailTrace_709603 : CollatzResearch.WordTrace tailWord_709603 prefixEnd_709603 364367412872492408699101 := by
  unfold tailWord_709603
  simp only [CollatzResearch.WordTrace]
  refine ⟨25881347648236996389037463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17254231765491330926024975 25881347648236996389037463)
  ·
    refine ⟨38822021472355494583556195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25881347648236996389037463 38822021472355494583556195)
    ·
      refine ⟨58233032208533241875334293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38822021472355494583556195 58233032208533241875334293)
      ·
        refine ⟨2729673384774995712906295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 58233032208533241875334293 2729673384774995712906295)
        ·
          refine ⟨4094510077162493569359443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2729673384774995712906295 4094510077162493569359443)
          ·
            refine ⟨6141765115743740354039165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4094510077162493569359443 6141765115743740354039165)
            ·
              refine ⟨2303161918403902632764687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6141765115743740354039165 2303161918403902632764687)
              ·
                refine ⟨3454742877605853949147031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2303161918403902632764687 3454742877605853949147031)
                ·
                  refine ⟨5182114316408780923720547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3454742877605853949147031 5182114316408780923720547)
                  ·
                    refine ⟨7773171474613171385580821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5182114316408780923720547 7773171474613171385580821)
                    ·
                      refine ⟨364367412872492408699101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7773171474613171385580821 364367412872492408699101)
                      ·
                        rfl

theorem cell23_709603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_709603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709603 prefixEnd_709603 := by exact prefixLift 709603
  have htrace : WordTrace (prefixWord ++ tailWord_709603) baseStart_709603 baseEnd_709603 := by
    simpa [prefixWord, tailWord_709603, baseEnd_709603] using wordTrace_append hprefix tailTrace_709603
  have hstable : (prefixWord ++ tailWord_709603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709603).length < 2 ^ (prefixWord ++ tailWord_709603).sum := by decide
  have hdescent : baseEnd_709603 < baseStart_709603 := by decide
  rcases family_descends (prefixWord ++ tailWord_709603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709607 : List Nat := [1, 1, 5, 2, 2, 2, 2, 2, 1, 1, 4]
def baseStart_709607 : Nat := 118140960795 + 709607 * 2 ^ 59
def prefixEnd_709607 : Nat := 4983230072969 + 3 ^ 40 * 709607 * 2
def baseEnd_709607 : Nat := 364369466795110393049083

theorem tailTrace_709607 : CollatzResearch.WordTrace tailWord_709607 prefixEnd_709607 364369466795110393049083 := by
  unfold tailWord_709607
  simp only [CollatzResearch.WordTrace]
  refine ⟨25881493540222505072183075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17254329026815003381455383 25881493540222505072183075)
  ·
    refine ⟨38822240310333757608274613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25881493540222505072183075 38822240310333757608274613)
    ·
      refine ⟨3639585029093789775775745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38822240310333757608274613 3639585029093789775775745)
      ·
        refine ⟨2729688771820342331831809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3639585029093789775775745 2729688771820342331831809)
        ·
          refine ⟨2047266578865256748873857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2729688771820342331831809 2047266578865256748873857)
          ·
            refine ⟨1535449934148942561655393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2047266578865256748873857 1535449934148942561655393)
            ·
              refine ⟨1151587450611706921241545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1535449934148942561655393 1151587450611706921241545)
              ·
                refine ⟨863690587958780190931159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1151587450611706921241545 863690587958780190931159)
                ·
                  refine ⟨1295535881938170286396739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 863690587958780190931159 1295535881938170286396739)
                  ·
                    refine ⟨1943303822907255429595109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1295535881938170286396739 1943303822907255429595109)
                    ·
                      refine ⟨364369466795110393049083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1943303822907255429595109 364369466795110393049083)
                      ·
                        rfl

theorem cell23_709607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_709607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709607 prefixEnd_709607 := by exact prefixLift 709607
  have htrace : WordTrace (prefixWord ++ tailWord_709607) baseStart_709607 baseEnd_709607 := by
    simpa [prefixWord, tailWord_709607, baseEnd_709607] using wordTrace_append hprefix tailTrace_709607
  have hstable : (prefixWord ++ tailWord_709607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709607).length < 2 ^ (prefixWord ++ tailWord_709607).sum := by decide
  have hdescent : baseEnd_709607 < baseStart_709607 := by decide
  rcases family_descends (prefixWord ++ tailWord_709607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
