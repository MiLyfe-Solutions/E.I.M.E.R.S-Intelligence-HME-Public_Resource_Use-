import V185TrunkScan23Chunk0887

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5255541 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 1, 5, 2]
def baseStart_5255541 : Nat := 118140960795 + 5255541 * 2 ^ 59
def prefixEnd_5255541 : Nat := 4983230072969 + 3 ^ 40 * 5255541 * 2
def baseEnd_5255541 : Nat := 2698618632411127405367713

theorem tailTrace_5255541 : CollatzResearch.WordTrace tailWord_5255541 prefixEnd_5255541 2698618632411127405367713 := by
  unfold tailWord_5255541
  simp only [CollatzResearch.WordTrace]
  refine ⟨191685327853080006788318477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127790218568720004525545651 191685327853080006788318477)
  ·
    refine ⟨71881997944905002545619429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191685327853080006788318477 71881997944905002545619429)
    ·
      refine ⟨13477874614669687977303643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71881997944905002545619429 13477874614669687977303643)
      ·
        refine ⟨20216811922004531965955465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13477874614669687977303643 20216811922004531965955465)
        ·
          refine ⟨15162608941503398974466599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20216811922004531965955465 15162608941503398974466599)
          ·
            refine ⟨22743913412255098461699899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15162608941503398974466599 22743913412255098461699899)
            ·
              refine ⟨34115870118382647692549849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22743913412255098461699899 34115870118382647692549849)
              ·
                refine ⟨25586902588786985769412387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34115870118382647692549849 25586902588786985769412387)
                ·
                  refine ⟨38380353883180478654118581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25586902588786985769412387 38380353883180478654118581)
                  ·
                    refine ⟨3598158176548169873823617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38380353883180478654118581 3598158176548169873823617)
                    ·
                      refine ⟨2698618632411127405367713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3598158176548169873823617 2698618632411127405367713)
                      ·
                        rfl

theorem cell23_5255541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_5255541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255541 prefixEnd_5255541 := by exact prefixLift 5255541
  have htrace : WordTrace (prefixWord ++ tailWord_5255541) baseStart_5255541 baseEnd_5255541 := by
    simpa [prefixWord, tailWord_5255541, baseEnd_5255541] using wordTrace_append hprefix tailTrace_5255541
  have hstable : (prefixWord ++ tailWord_5255541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255541).length < 2 ^ (prefixWord ++ tailWord_5255541).sum := by decide
  have hdescent : baseEnd_5255541 < baseStart_5255541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255557 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 5, 1, 5]
def baseStart_5255557 : Nat := 118140960795 + 5255557 * 2 ^ 59
def prefixEnd_5255557 : Nat := 4983230072969 + 3 ^ 40 * 5255557 * 2
def baseEnd_5255557 : Nat := 2698626848101599342767639

theorem tailTrace_5255557 : CollatzResearch.WordTrace tailWord_5255557 prefixEnd_5255557 2698626848101599342767639 := by
  unfold tailWord_5255557
  simp only [CollatzResearch.WordTrace]
  refine ⟨191685911421022041520900925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127790607614014694347267283 191685911421022041520900925)
  ·
    refine ⟨71882216782883265570337847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191685911421022041520900925 71882216782883265570337847)
    ·
      refine ⟨107823325174324898355506771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71882216782883265570337847 107823325174324898355506771)
      ·
        refine ⟨161734987761487347533260157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107823325174324898355506771 161734987761487347533260157)
        ·
          refine ⟨60650620410557755324972559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161734987761487347533260157 60650620410557755324972559)
          ·
            refine ⟨90975930615836632987458839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60650620410557755324972559 90975930615836632987458839)
            ·
              refine ⟨136463895923754949481188259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90975930615836632987458839 136463895923754949481188259)
              ·
                refine ⟨204695843885632424221782389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136463895923754949481188259 204695843885632424221782389)
                ·
                  refine ⟨19190235364278039770792099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 204695843885632424221782389 19190235364278039770792099)
                  ·
                    refine ⟨28785353046417059656188149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19190235364278039770792099 28785353046417059656188149)
                    ·
                      refine ⟨2698626848101599342767639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28785353046417059656188149 2698626848101599342767639)
                      ·
                        rfl

theorem cell23_5255557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_5255557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255557 prefixEnd_5255557 := by exact prefixLift 5255557
  have htrace : WordTrace (prefixWord ++ tailWord_5255557) baseStart_5255557 baseEnd_5255557 := by
    simpa [prefixWord, tailWord_5255557, baseEnd_5255557] using wordTrace_append hprefix tailTrace_5255557
  have hstable : (prefixWord ++ tailWord_5255557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255557).length < 2 ^ (prefixWord ++ tailWord_5255557).sum := by decide
  have hdescent : baseEnd_5255557 < baseStart_5255557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255564 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 4, 4]
def baseStart_5255564 : Nat := 118140960795 + 5255564 * 2 ^ 59
def prefixEnd_5255564 : Nat := 4983230072969 + 3 ^ 40 * 5255564 * 2
def baseEnd_5255564 : Nat := 899543480822060271793369

theorem tailTrace_5255564 : CollatzResearch.WordTrace tailWord_5255564 prefixEnd_5255564 899543480822060271793369 := by
  unfold tailWord_5255564
  simp only [CollatzResearch.WordTrace]
  refine ⟨95843083365998340858202873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127790777821331121144270497 95843083365998340858202873)
  ·
    refine ⟨71882312524498755643652155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95843083365998340858202873 71882312524498755643652155)
    ·
      refine ⟨107823468786748133465478233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71882312524498755643652155 107823468786748133465478233)
      ·
        refine ⟨80867601590061100099108675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107823468786748133465478233 80867601590061100099108675)
        ·
          refine ⟨121301402385091650148663013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80867601590061100099108675 121301402385091650148663013)
          ·
            refine ⟨22744012947204684402874315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121301402385091650148663013 22744012947204684402874315)
            ·
              refine ⟨34116019420807026604311473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22744012947204684402874315 34116019420807026604311473)
              ·
                refine ⟨25587014565605269953233605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34116019420807026604311473 25587014565605269953233605)
                ·
                  refine ⟨4797565231050988116231301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25587014565605269953233605 4797565231050988116231301)
                  ·
                    refine ⟨899543480822060271793369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4797565231050988116231301 899543480822060271793369)
                    ·
                      rfl

theorem cell23_5255564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 4, 4].length) (baseStart_5255564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255564 prefixEnd_5255564 := by exact prefixLift 5255564
  have htrace : WordTrace (prefixWord ++ tailWord_5255564) baseStart_5255564 baseEnd_5255564 := by
    simpa [prefixWord, tailWord_5255564, baseEnd_5255564] using wordTrace_append hprefix tailTrace_5255564
  have hstable : (prefixWord ++ tailWord_5255564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255564).length < 2 ^ (prefixWord ++ tailWord_5255564).sum := by decide
  have hdescent : baseEnd_5255564 < baseStart_5255564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255588 : List Nat := [2, 3, 1, 2, 1, 1, 5, 1, 3, 2, 2]
def baseStart_5255588 : Nat := 118140960795 + 5255588 * 2 ^ 59
def prefixEnd_5255588 : Nat := 4983230072969 + 3 ^ 40 * 5255588 * 2
def baseEnd_5255588 : Nat := 2698642766001888721479997

theorem tailTrace_5255588 : CollatzResearch.WordTrace tailWord_5255588 prefixEnd_5255588 2698642766001888721479997 := by
  unfold tailWord_5255588
  simp only [CollatzResearch.WordTrace]
  refine ⟨95843521041954866907639709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127791361389273155876852945 95843521041954866907639709)
  ·
    refine ⟨35941320390733075090364891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95843521041954866907639709 35941320390733075090364891)
    ·
      refine ⟨53911980586099612635547337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35941320390733075090364891 53911980586099612635547337)
      ·
        refine ⟨40433985439574709476660503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53911980586099612635547337 40433985439574709476660503)
        ·
          refine ⟨60650978159362064214990755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40433985439574709476660503 60650978159362064214990755)
          ·
            refine ⟨90976467239043096322486133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60650978159362064214990755 90976467239043096322486133)
            ·
              refine ⟨8529043803660290280233075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90976467239043096322486133 8529043803660290280233075)
              ·
                refine ⟨12793565705490435420349613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8529043803660290280233075 12793565705490435420349613)
                ·
                  refine ⟨4797587139558913282631105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12793565705490435420349613 4797587139558913282631105)
                  ·
                    refine ⟨3598190354669184961973329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4797587139558913282631105 3598190354669184961973329)
                    ·
                      refine ⟨2698642766001888721479997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3598190354669184961973329 2698642766001888721479997)
                      ·
                        rfl

theorem cell23_5255588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_5255588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255588 prefixEnd_5255588 := by exact prefixLift 5255588
  have htrace : WordTrace (prefixWord ++ tailWord_5255588) baseStart_5255588 baseEnd_5255588 := by
    simpa [prefixWord, tailWord_5255588, baseEnd_5255588] using wordTrace_append hprefix tailTrace_5255588
  have hstable : (prefixWord ++ tailWord_5255588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255588).length < 2 ^ (prefixWord ++ tailWord_5255588).sum := by decide
  have hdescent : baseEnd_5255588 < baseStart_5255588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255605 : List Nat := [1, 3, 3, 2, 4, 1, 1, 2, 1, 1, 4]
def baseStart_5255605 : Nat := 118140960795 + 5255605 * 2 ^ 59
def prefixEnd_5255605 : Nat := 4983230072969 + 3 ^ 40 * 5255605 * 2
def baseEnd_5255605 : Nat := 2698651495173015154967419

theorem tailTrace_5255605 : CollatzResearch.WordTrace tailWord_5255605 prefixEnd_5255605 2698651495173015154967419 := by
  unfold tailWord_5255605
  simp only [CollatzResearch.WordTrace]
  refine ⟨191687662124848145718648269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127791774749898763812432179 191687662124848145718648269)
  ·
    refine ⟨71882873296818054644493101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191687662124848145718648269 71882873296818054644493101)
    ·
      refine ⟨26956077486306770491684913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71882873296818054644493101 26956077486306770491684913)
      ·
        refine ⟨20217058114730077868763685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26956077486306770491684913 20217058114730077868763685)
        ·
          refine ⟨3790698396511889600393191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20217058114730077868763685 3790698396511889600393191)
          ·
            refine ⟨5686047594767834400589787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3790698396511889600393191 5686047594767834400589787)
            ·
              refine ⟨8529071392151751600884681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5686047594767834400589787 8529071392151751600884681)
              ·
                refine ⟨6396803544113813700663511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8529071392151751600884681 6396803544113813700663511)
                ·
                  refine ⟨9595205316170720550995267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6396803544113813700663511 9595205316170720550995267)
                  ·
                    refine ⟨14392807974256080826492901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9595205316170720550995267 14392807974256080826492901)
                    ·
                      refine ⟨2698651495173015154967419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14392807974256080826492901 2698651495173015154967419)
                      ·
                        rfl

theorem cell23_5255605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_5255605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255605 prefixEnd_5255605 := by exact prefixLift 5255605
  have htrace : WordTrace (prefixWord ++ tailWord_5255605) baseStart_5255605 baseEnd_5255605 := by
    simpa [prefixWord, tailWord_5255605, baseEnd_5255605] using wordTrace_append hprefix tailTrace_5255605
  have hstable : (prefixWord ++ tailWord_5255605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255605).length < 2 ^ (prefixWord ++ tailWord_5255605).sum := by decide
  have hdescent : baseEnd_5255605 < baseStart_5255605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255664 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 3]
def baseStart_5255664 : Nat := 118140960795 + 5255664 * 2 ^ 59
def prefixEnd_5255664 : Nat := 4983230072969 + 3 ^ 40 * 5255664 * 2
def baseEnd_5255664 : Nat := 2698681790531630424129647

theorem tailTrace_5255664 : CollatzResearch.WordTrace tailWord_5255664 prefixEnd_5255664 2698681790531630424129647 := by
  unfold tailWord_5255664
  simp only [CollatzResearch.WordTrace]
  refine ⟨95844907015817199397523023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127793209354422932530030697 95844907015817199397523023)
  ·
    refine ⟨143767360523725799096284535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95844907015817199397523023 143767360523725799096284535)
    ·
      refine ⟨215651040785588698644426803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143767360523725799096284535 215651040785588698644426803)
      ·
        refine ⟨323476561178383047966640205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215651040785588698644426803 323476561178383047966640205)
        ·
          refine ⟨121303710441893642987490077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 323476561178383047966640205 121303710441893642987490077)
          ·
            refine ⟨45488891415710116120308779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121303710441893642987490077 45488891415710116120308779)
            ·
              refine ⟨68233337123565174180463169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45488891415710116120308779 68233337123565174180463169)
              ·
                refine ⟨51175002842673880635347377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68233337123565174180463169 51175002842673880635347377)
                ·
                  refine ⟨38381252132005410476510533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51175002842673880635347377 38381252132005410476510533)
                  ·
                    refine ⟨7196484774751014464345725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38381252132005410476510533 7196484774751014464345725)
                    ·
                      refine ⟨2698681790531630424129647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7196484774751014464345725 2698681790531630424129647)
                      ·
                        rfl

theorem cell23_5255664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 3].length) (baseStart_5255664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255664 prefixEnd_5255664 := by exact prefixLift 5255664
  have htrace : WordTrace (prefixWord ++ tailWord_5255664) baseStart_5255664 baseEnd_5255664 := by
    simpa [prefixWord, tailWord_5255664, baseEnd_5255664] using wordTrace_append hprefix tailTrace_5255664
  have hstable : (prefixWord ++ tailWord_5255664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255664).length < 2 ^ (prefixWord ++ tailWord_5255664).sum := by decide
  have hdescent : baseEnd_5255664 < baseStart_5255664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255682 : List Nat := [3, 4, 1, 2, 2, 1, 1, 3, 1, 3, 2]
def baseStart_5255682 : Nat := 118140960795 + 5255682 * 2 ^ 59
def prefixEnd_5255682 : Nat := 4983230072969 + 3 ^ 40 * 5255682 * 2
def baseEnd_5255682 : Nat := 2698691033183411353704565

theorem tailTrace_5255682 : CollatzResearch.WordTrace tailWord_5255682 prefixEnd_5255682 2698691033183411353704565 := by
  unfold tailWord_5255682
  simp only [CollatzResearch.WordTrace]
  refine ⟨47922617636392296967300325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127793647030379458579467533 47922617636392296967300325)
  ·
    refine ⟨8985490806823555681368811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47922617636392296967300325 8985490806823555681368811)
    ·
      refine ⟨13478236210235333522053217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8985490806823555681368811 13478236210235333522053217)
      ·
        refine ⟨10108677157676500141539913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13478236210235333522053217 10108677157676500141539913)
        ·
          refine ⟨7581507868257375106154935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10108677157676500141539913 7581507868257375106154935)
          ·
            refine ⟨11372261802386062659232403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7581507868257375106154935 11372261802386062659232403)
            ·
              refine ⟨17058392703579093988848605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11372261802386062659232403 17058392703579093988848605)
              ·
                refine ⟨6396897263842160245818227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17058392703579093988848605 6396897263842160245818227)
                ·
                  refine ⟨9595345895763240368727341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6396897263842160245818227 9595345895763240368727341)
                  ·
                    refine ⟨3598254710911215138272753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9595345895763240368727341 3598254710911215138272753)
                    ·
                      refine ⟨2698691033183411353704565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3598254710911215138272753 2698691033183411353704565)
                      ·
                        rfl

theorem cell23_5255682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_5255682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255682 prefixEnd_5255682 := by exact prefixLift 5255682
  have htrace : WordTrace (prefixWord ++ tailWord_5255682) baseStart_5255682 baseEnd_5255682 := by
    simpa [prefixWord, tailWord_5255682, baseEnd_5255682] using wordTrace_append hprefix tailTrace_5255682
  have hstable : (prefixWord ++ tailWord_5255682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255682).length < 2 ^ (prefixWord ++ tailWord_5255682).sum := by decide
  have hdescent : baseEnd_5255682 < baseStart_5255682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255701 : List Nat := [1, 3, 2, 1, 3, 1, 1, 6, 5]
def baseStart_5255701 : Nat := 118140960795 + 5255701 * 2 ^ 59
def prefixEnd_5255701 : Nat := 4983230072969 + 3 ^ 40 * 5255701 * 2
def baseEnd_5255701 : Nat := 299855643257316308818553

theorem tailTrace_5255701 : CollatzResearch.WordTrace tailWord_5255701 prefixEnd_5255701 299855643257316308818553 := by
  unfold tailWord_5255701
  simp only [CollatzResearch.WordTrace]
  refine ⟨191691163532500354114142957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127794109021666902742761971 191691163532500354114142957)
  ·
    refine ⟨71884186324687632792803609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191691163532500354114142957 71884186324687632792803609)
    ·
      refine ⟨53913139743515724594602707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71884186324687632792803609 53913139743515724594602707)
      ·
        refine ⟨80869709615273586891904061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53913139743515724594602707 80869709615273586891904061)
        ·
          refine ⟨30326141105727595084464023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80869709615273586891904061 30326141105727595084464023)
          ·
            refine ⟨45489211658591392626696035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30326141105727595084464023 45489211658591392626696035)
            ·
              refine ⟨68233817487887088940044053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45489211658591392626696035 68233817487887088940044053)
              ·
                refine ⟨3198460194744707294064565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68233817487887088940044053 3198460194744707294064565)
                ·
                  refine ⟨299855643257316308818553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3198460194744707294064565 299855643257316308818553)
                  ·
                    rfl

theorem cell23_5255701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 5].length) (baseStart_5255701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255701 prefixEnd_5255701 := by exact prefixLift 5255701
  have htrace : WordTrace (prefixWord ++ tailWord_5255701) baseStart_5255701 baseEnd_5255701 := by
    simpa [prefixWord, tailWord_5255701, baseEnd_5255701] using wordTrace_append hprefix tailTrace_5255701
  have hstable : (prefixWord ++ tailWord_5255701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255701).length < 2 ^ (prefixWord ++ tailWord_5255701).sum := by decide
  have hdescent : baseEnd_5255701 < baseStart_5255701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255712 : List Nat := [2, 1, 1, 6, 3, 1, 1, 1, 1, 4, 2]
def baseStart_5255712 : Nat := 118140960795 + 5255712 * 2 ^ 59
def prefixEnd_5255712 : Nat := 4983230072969 + 3 ^ 40 * 5255712 * 2
def baseEnd_5255712 : Nat := 2698706437603046236329427

theorem tailTrace_5255712 : CollatzResearch.WordTrace tailWord_5255712 prefixEnd_5255712 2698706437603046236329427 := by
  unfold tailWord_5255712
  simp only [CollatzResearch.WordTrace]
  refine ⟨95845782367730251496396695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127794376490307001995195593 95845782367730251496396695)
  ·
    refine ⟨143768673551595377244595043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95845782367730251496396695 143768673551595377244595043)
    ·
      refine ⟨215653010327393065866892565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143768673551595377244595043 215653010327393065866892565)
      ·
        refine ⟨10108734859096549962510589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 215653010327393065866892565 10108734859096549962510589)
        ·
          refine ⟨3790775572161206235941471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10108734859096549962510589 3790775572161206235941471)
          ·
            refine ⟨5686163358241809353912207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3790775572161206235941471 5686163358241809353912207)
            ·
              refine ⟨8529245037362714030868311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5686163358241809353912207 8529245037362714030868311)
              ·
                refine ⟨12793867556044071046302467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8529245037362714030868311 12793867556044071046302467)
                ·
                  refine ⟨19190801334066106569453701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12793867556044071046302467 19190801334066106569453701)
                  ·
                    refine ⟨3598275250137394981772569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19190801334066106569453701 3598275250137394981772569)
                    ·
                      refine ⟨2698706437603046236329427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3598275250137394981772569 2698706437603046236329427)
                      ·
                        rfl

theorem cell23_5255712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_5255712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255712 prefixEnd_5255712 := by exact prefixLift 5255712
  have htrace : WordTrace (prefixWord ++ tailWord_5255712) baseStart_5255712 baseEnd_5255712 := by
    simpa [prefixWord, tailWord_5255712, baseEnd_5255712] using wordTrace_append hprefix tailTrace_5255712
  have hstable : (prefixWord ++ tailWord_5255712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255712).length < 2 ^ (prefixWord ++ tailWord_5255712).sum := by decide
  have hdescent : baseEnd_5255712 < baseStart_5255712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255751 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 4]
def baseStart_5255751 : Nat := 118140960795 + 5255751 * 2 ^ 59
def prefixEnd_5255751 : Nat := 4983230072969 + 3 ^ 40 * 5255751 * 2
def baseEnd_5255751 : Nat := 2698726463348571583741747

theorem tailTrace_5255751 : CollatzResearch.WordTrace tailWord_5255751 prefixEnd_5255751 2698726463348571583741747 := by
  unfold tailWord_5255751
  simp only [CollatzResearch.WordTrace]
  refine ⟨191692987182319212653463107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127795324788212808435642071 191692987182319212653463107)
  ·
    refine ⟨287539480773478818980194661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191692987182319212653463107 287539480773478818980194661)
    ·
      refine ⟨53913652645027278558786499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 287539480773478818980194661 53913652645027278558786499)
      ·
        refine ⟨80870478967540917838179749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53913652645027278558786499 80870478967540917838179749)
        ·
          refine ⟨15163214806413922094658703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80870478967540917838179749 15163214806413922094658703)
          ·
            refine ⟨22744822209620883141988055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15163214806413922094658703 22744822209620883141988055)
            ·
              refine ⟨34117233314431324712982083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22744822209620883141988055 34117233314431324712982083)
              ·
                refine ⟨51175849971646987069473125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34117233314431324712982083 51175849971646987069473125)
                ·
                  refine ⟨9595471869683810075526211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51175849971646987069473125 9595471869683810075526211)
                  ·
                    refine ⟨14393207804525715113289317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9595471869683810075526211 14393207804525715113289317)
                    ·
                      refine ⟨2698726463348571583741747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14393207804525715113289317 2698726463348571583741747)
                      ·
                        rfl

theorem cell23_5255751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_5255751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255751 prefixEnd_5255751 := by exact prefixLift 5255751
  have htrace : WordTrace (prefixWord ++ tailWord_5255751) baseStart_5255751 baseEnd_5255751 := by
    simpa [prefixWord, tailWord_5255751, baseEnd_5255751] using wordTrace_append hprefix tailTrace_5255751
  have hstable : (prefixWord ++ tailWord_5255751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255751).length < 2 ^ (prefixWord ++ tailWord_5255751).sum := by decide
  have hdescent : baseEnd_5255751 < baseStart_5255751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255812 : List Nat := [2, 3, 2, 1, 3, 1, 4, 2, 1, 4]
def baseStart_5255812 : Nat := 118140960795 + 5255812 * 2 ^ 59
def prefixEnd_5255812 : Nat := 4983230072969 + 3 ^ 40 * 5255812 * 2
def baseEnd_5255812 : Nat := 899585928556165281692989

theorem tailTrace_5255812 : CollatzResearch.WordTrace tailWord_5255812 prefixEnd_5255812 899585928556165281692989 := by
  unfold tailWord_5255812
  simp only [CollatzResearch.WordTrace]
  refine ⟨95847606017549110035716845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127796808023398813380955793 95847606017549110035716845)
  ·
    refine ⟨35942852256580916263393817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95847606017549110035716845 35942852256580916263393817)
    ·
      refine ⟨26957139192435687197545363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35942852256580916263393817 26957139192435687197545363)
      ·
        refine ⟨40435708788653530796318045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26957139192435687197545363 40435708788653530796318045)
        ·
          refine ⟨15163390795745074048619267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40435708788653530796318045 15163390795745074048619267)
          ·
            refine ⟨22745086193617611072928901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15163390795745074048619267 22745086193617611072928901)
            ·
              refine ⟨4264703661303302076174169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22745086193617611072928901 4264703661303302076174169)
              ·
                refine ⟨3198527745977476557130627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4264703661303302076174169 3198527745977476557130627)
                ·
                  refine ⟨4797791618966214835695941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3198527745977476557130627 4797791618966214835695941)
                  ·
                    refine ⟨899585928556165281692989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4797791618966214835695941 899585928556165281692989)
                    ·
                      rfl

theorem cell23_5255812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_5255812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255812 prefixEnd_5255812 := by exact prefixLift 5255812
  have htrace : WordTrace (prefixWord ++ tailWord_5255812) baseStart_5255812 baseEnd_5255812 := by
    simpa [prefixWord, tailWord_5255812, baseEnd_5255812] using wordTrace_append hprefix tailTrace_5255812
  have hstable : (prefixWord ++ tailWord_5255812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255812).length < 2 ^ (prefixWord ++ tailWord_5255812).sum := by decide
  have hdescent : baseEnd_5255812 < baseStart_5255812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255838 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_5255838 : Nat := 118140960795 + 5255838 * 2 ^ 59
def prefixEnd_5255838 : Nat := 4983230072969 + 3 ^ 40 * 5255838 * 2
def baseEnd_5255838 : Nat := 899590378721837581117949

theorem tailTrace_5255838 : CollatzResearch.WordTrace tailWord_5255838 prefixEnd_5255838 899590378721837581117949 := by
  unfold tailWord_5255838
  simp only [CollatzResearch.WordTrace]
  refine ⟨23962020041625503313985021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127797440222002684341253445 23962020041625503313985021)
  ·
    refine ⟨8985757515609563742744383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23962020041625503313985021 8985757515609563742744383)
    ·
      refine ⟨13478636273414345614116575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8985757515609563742744383 13478636273414345614116575)
      ·
        refine ⟨20217954410121518421174863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13478636273414345614116575 20217954410121518421174863)
        ·
          refine ⟨30326931615182277631762295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20217954410121518421174863 30326931615182277631762295)
          ·
            refine ⟨45490397422773416447643443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30326931615182277631762295 45490397422773416447643443)
            ·
              refine ⟨68235596134160124671465165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45490397422773416447643443 68235596134160124671465165)
              ·
                refine ⟨25588348550310046751799437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68235596134160124671465165 25588348550310046751799437)
                ·
                  refine ⟨9595630706366267531924789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25588348550310046751799437 9595630706366267531924789)
                  ·
                    refine ⟨899590378721837581117949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9595630706366267531924789 899590378721837581117949)
                    ·
                      rfl

theorem cell23_5255838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_5255838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255838 prefixEnd_5255838 := by exact prefixLift 5255838
  have htrace : WordTrace (prefixWord ++ tailWord_5255838) baseStart_5255838 baseEnd_5255838 := by
    simpa [prefixWord, tailWord_5255838, baseEnd_5255838] using wordTrace_append hprefix tailTrace_5255838
  have hstable : (prefixWord ++ tailWord_5255838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255838).length < 2 ^ (prefixWord ++ tailWord_5255838).sum := by decide
  have hdescent : baseEnd_5255838 < baseStart_5255838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255855 : List Nat := [1, 1, 2, 1, 2, 7, 2, 1, 1, 5]
def baseStart_5255855 : Nat := 118140960795 + 5255855 * 2 ^ 59
def prefixEnd_5255855 : Nat := 4983230072969 + 3 ^ 40 * 5255855 * 2
def baseEnd_5255855 : Nat := 899593288445546392280423

theorem tailTrace_5255855 : CollatzResearch.WordTrace tailWord_5255855 prefixEnd_5255855 899593288445546392280423 := by
  unfold tailWord_5255855
  simp only [CollatzResearch.WordTrace]
  refine ⟨191696780373942438415249019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127797853582628292276832679 191696780373942438415249019)
  ·
    refine ⟨287545170560913657622873529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191696780373942438415249019 287545170560913657622873529)
    ·
      refine ⟨215658877920685243217155147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287545170560913657622873529 215658877920685243217155147)
      ·
        refine ⟨323488316881027864825732721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215658877920685243217155147 323488316881027864825732721)
        ·
          refine ⟨242616237660770898619299541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323488316881027864825732721 242616237660770898619299541)
          ·
            refine ⟨5686318070174317936389833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 242616237660770898619299541 5686318070174317936389833)
            ·
              refine ⟨4264738552630738452292375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5686318070174317936389833 4264738552630738452292375)
              ·
                refine ⟨6397107828946107678438563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4264738552630738452292375 6397107828946107678438563)
                ·
                  refine ⟨9595661743419161517657845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6397107828946107678438563 9595661743419161517657845)
                  ·
                    refine ⟨899593288445546392280423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9595661743419161517657845 899593288445546392280423)
                    ·
                      rfl

theorem cell23_5255855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 1, 5].length) (baseStart_5255855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255855 prefixEnd_5255855 := by exact prefixLift 5255855
  have htrace : WordTrace (prefixWord ++ tailWord_5255855) baseStart_5255855 baseEnd_5255855 := by
    simpa [prefixWord, tailWord_5255855, baseEnd_5255855] using wordTrace_append hprefix tailTrace_5255855
  have hstable : (prefixWord ++ tailWord_5255855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255855).length < 2 ^ (prefixWord ++ tailWord_5255855).sum := by decide
  have hdescent : baseEnd_5255855 < baseStart_5255855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255868 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 4, 4]
def baseStart_5255868 : Nat := 118140960795 + 5255868 * 2 ^ 59
def prefixEnd_5255868 : Nat := 4983230072969 + 3 ^ 40 * 5255868 * 2
def baseEnd_5255868 : Nat := 899595513528382541992903

theorem tailTrace_5255868 : CollatzResearch.WordTrace tailWord_5255868 prefixEnd_5255868 899595513528382541992903 := by
  unfold tailWord_5255868
  simp only [CollatzResearch.WordTrace]
  refine ⟨95848627261447670817736129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127798169681930227756981505 95848627261447670817736129)
  ·
    refine ⟨71886470446085753113302097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95848627261447670817736129 71886470446085753113302097)
    ·
      refine ⟨53914852834564314834976573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71886470446085753113302097 53914852834564314834976573)
      ·
        refine ⟨20218069812961618063116215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53914852834564314834976573 20218069812961618063116215)
        ·
          refine ⟨30327104719442427094674323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20218069812961618063116215 30327104719442427094674323)
          ·
            refine ⟨45490657079163640642011485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30327104719442427094674323 45490657079163640642011485)
            ·
              refine ⟨17058996404686365240754307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45490657079163640642011485 17058996404686365240754307)
              ·
                refine ⟨25588494607029547861131461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17058996404686365240754307 25588494607029547861131461)
                ·
                  refine ⟨4797842738818040223962149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25588494607029547861131461 4797842738818040223962149)
                  ·
                    refine ⟨899595513528382541992903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4797842738818040223962149 899595513528382541992903)
                    ·
                      rfl

theorem cell23_5255868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_5255868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255868 prefixEnd_5255868 := by exact prefixLift 5255868
  have htrace : WordTrace (prefixWord ++ tailWord_5255868) baseStart_5255868 baseEnd_5255868 := by
    simpa [prefixWord, tailWord_5255868, baseEnd_5255868] using wordTrace_append hprefix tailTrace_5255868
  have hstable : (prefixWord ++ tailWord_5255868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255868).length < 2 ^ (prefixWord ++ tailWord_5255868).sum := by decide
  have hdescent : baseEnd_5255868 < baseStart_5255868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255892 : List Nat := [2, 4, 1, 3, 2, 1, 2, 2, 1, 1, 4]
def baseStart_5255892 : Nat := 118140960795 + 5255892 * 2 ^ 59
def prefixEnd_5255892 : Nat := 4983230072969 + 3 ^ 40 * 5255892 * 2
def baseEnd_5255892 : Nat := 2698798864120855532078599

theorem tailTrace_5255892 : CollatzResearch.WordTrace tailWord_5255892 prefixEnd_5255892 2698798864120855532078599 := by
  unfold tailWord_5255892
  simp only [CollatzResearch.WordTrace]
  refine ⟨95849064937404196867172965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127798753249872262489563953 95849064937404196867172965)
  ·
    refine ⟨17971699675763286912594931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95849064937404196867172965 17971699675763286912594931)
    ·
      refine ⟨26957549513644930368892397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17971699675763286912594931 26957549513644930368892397)
      ·
        refine ⟨10109081067616848888334649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26957549513644930368892397 10109081067616848888334649)
        ·
          refine ⟨7581810800712636666250987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10109081067616848888334649 7581810800712636666250987)
          ·
            refine ⟨11372716201068954999376481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7581810800712636666250987 11372716201068954999376481)
            ·
              refine ⟨8529537150801716249532361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11372716201068954999376481 8529537150801716249532361)
              ·
                refine ⟨6397152863101287187149271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8529537150801716249532361 6397152863101287187149271)
                ·
                  refine ⟨9595729294651930780723907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6397152863101287187149271 9595729294651930780723907)
                  ·
                    refine ⟨14393593941977896171085861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9595729294651930780723907 14393593941977896171085861)
                    ·
                      refine ⟨2698798864120855532078599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14393593941977896171085861 2698798864120855532078599)
                      ·
                        rfl

theorem cell23_5255892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_5255892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255892 prefixEnd_5255892 := by exact prefixLift 5255892
  have htrace : WordTrace (prefixWord ++ tailWord_5255892) baseStart_5255892 baseEnd_5255892 := by
    simpa [prefixWord, tailWord_5255892, baseEnd_5255892] using wordTrace_append hprefix tailTrace_5255892
  have hstable : (prefixWord ++ tailWord_5255892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255892).length < 2 ^ (prefixWord ++ tailWord_5255892).sum := by decide
  have hdescent : baseEnd_5255892 < baseStart_5255892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255895 : List Nat := [1, 1, 3, 2, 1, 5, 2, 2, 1, 2, 3]
def baseStart_5255895 : Nat := 118140960795 + 5255895 * 2 ^ 59
def prefixEnd_5255895 : Nat := 4983230072969 + 3 ^ 40 * 5255895 * 2
def baseEnd_5255895 : Nat := 2698800404562819020341085

theorem tailTrace_5255895 : CollatzResearch.WordTrace tailWord_5255895 prefixEnd_5255895 2698800404562819020341085 := by
  unfold tailWord_5255895
  simp only [CollatzResearch.WordTrace]
  refine ⟨191698239293797525246705139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127798826195865016831136759 191698239293797525246705139)
  ·
    refine ⟨287547358940696287870057709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191698239293797525246705139 287547358940696287870057709)
    ·
      refine ⟨107830259602761107951271641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287547358940696287870057709 107830259602761107951271641)
      ·
        refine ⟨80872694702070830963453731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107830259602761107951271641 80872694702070830963453731)
        ·
          refine ⟨121309042053106246445180597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80872694702070830963453731 121309042053106246445180597)
          ·
            refine ⟨11372722692478710604235681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121309042053106246445180597 11372722692478710604235681)
            ·
              refine ⟨8529542019359032953176761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11372722692478710604235681 8529542019359032953176761)
              ·
                refine ⟨6397156514519274714882571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8529542019359032953176761 6397156514519274714882571)
                ·
                  refine ⟨9595734771778912072323857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6397156514519274714882571 9595734771778912072323857)
                  ·
                    refine ⟨7196801078834184054242893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9595734771778912072323857 7196801078834184054242893)
                    ·
                      refine ⟨2698800404562819020341085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7196801078834184054242893 2698800404562819020341085)
                      ·
                        rfl

theorem cell23_5255895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_5255895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255895 prefixEnd_5255895 := by exact prefixLift 5255895
  have htrace : WordTrace (prefixWord ++ tailWord_5255895) baseStart_5255895 baseEnd_5255895 := by
    simpa [prefixWord, tailWord_5255895, baseEnd_5255895] using wordTrace_append hprefix tailTrace_5255895
  have hstable : (prefixWord ++ tailWord_5255895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255895).length < 2 ^ (prefixWord ++ tailWord_5255895).sum := by decide
  have hdescent : baseEnd_5255895 < baseStart_5255895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255909 : List Nat := [1, 3, 1, 4, 1, 2, 3, 3, 1, 2, 2]
def baseStart_5255909 : Nat := 118140960795 + 5255909 * 2 ^ 59
def prefixEnd_5255909 : Nat := 4983230072969 + 3 ^ 40 * 5255909 * 2
def baseEnd_5255909 : Nat := 2698807593291981965566021

theorem tailTrace_5255909 : CollatzResearch.WordTrace tailWord_5255909 prefixEnd_5255909 2698807593291981965566021 := by
  unfold tailWord_5255909
  simp only [CollatzResearch.WordTrace]
  refine ⟨191698749915746805637714781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127799166610497870425143187 191698749915746805637714781)
  ·
    refine ⟨71887031218405052114143043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191698749915746805637714781 71887031218405052114143043)
    ·
      refine ⟨107830546827607578171214565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71887031218405052114143043 107830546827607578171214565)
      ·
        refine ⟨20218227530176420907102731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107830546827607578171214565 20218227530176420907102731)
        ·
          refine ⟨30327341295264631360654097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20218227530176420907102731 30327341295264631360654097)
          ·
            refine ⟨22745505971448473520490573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30327341295264631360654097 22745505971448473520490573)
            ·
              refine ⟨8529564739293177570183965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22745505971448473520490573 8529564739293177570183965)
              ·
                refine ⟨3198586777234941588818987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8529564739293177570183965 3198586777234941588818987)
                ·
                  refine ⟨4797880165852412383228481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3198586777234941588818987 4797880165852412383228481)
                  ·
                    refine ⟨3598410124389309287421361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4797880165852412383228481 3598410124389309287421361)
                    ·
                      refine ⟨2698807593291981965566021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3598410124389309287421361 2698807593291981965566021)
                      ·
                        rfl

theorem cell23_5255909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_5255909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255909 prefixEnd_5255909 := by exact prefixLift 5255909
  have htrace : WordTrace (prefixWord ++ tailWord_5255909) baseStart_5255909 baseEnd_5255909 := by
    simpa [prefixWord, tailWord_5255909, baseEnd_5255909] using wordTrace_append hprefix tailTrace_5255909
  have hstable : (prefixWord ++ tailWord_5255909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255909).length < 2 ^ (prefixWord ++ tailWord_5255909).sum := by decide
  have hdescent : baseEnd_5255909 < baseStart_5255909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255921 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 2, 2, 5]
def baseStart_5255921 : Nat := 118140960795 + 5255921 * 2 ^ 59
def prefixEnd_5255921 : Nat := 4983230072969 + 3 ^ 40 * 5255921 * 2
def baseEnd_5255921 : Nat := 2698813755059835918615965

theorem tailTrace_5255921 : CollatzResearch.WordTrace tailWord_5255921 prefixEnd_5255921 2698813755059835918615965 := by
  unfold tailWord_5255921
  simp only [CollatzResearch.WordTrace]
  refine ⟨191699187591703331687151617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127799458394468887791434411 191699187591703331687151617)
  ·
    refine ⟨143774390693777498765363713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191699187591703331687151617 143774390693777498765363713)
    ·
      refine ⟨107830793020333124074022785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143774390693777498765363713 107830793020333124074022785)
      ·
        refine ⟨80873094765249843055517089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107830793020333124074022785 80873094765249843055517089)
        ·
          refine ⟨60654821073937382291637817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80873094765249843055517089 60654821073937382291637817)
          ·
            refine ⟨45491115805453036718728363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60654821073937382291637817 45491115805453036718728363)
            ·
              refine ⟨68236673708179555078092545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45491115805453036718728363 68236673708179555078092545)
              ·
                refine ⟨51177505281134666308569409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68236673708179555078092545 51177505281134666308569409)
                ·
                  refine ⟨38383128960850999731427057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51177505281134666308569409 38383128960850999731427057)
                  ·
                    refine ⟨28787346720638249798570293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38383128960850999731427057 28787346720638249798570293)
                    ·
                      refine ⟨2698813755059835918615965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28787346720638249798570293 2698813755059835918615965)
                      ·
                        rfl

theorem cell23_5255921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_5255921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255921 prefixEnd_5255921 := by exact prefixLift 5255921
  have htrace : WordTrace (prefixWord ++ tailWord_5255921) baseStart_5255921 baseEnd_5255921 := by
    simpa [prefixWord, tailWord_5255921, baseEnd_5255921] using wordTrace_append hprefix tailTrace_5255921
  have hstable : (prefixWord ++ tailWord_5255921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255921).length < 2 ^ (prefixWord ++ tailWord_5255921).sum := by decide
  have hdescent : baseEnd_5255921 < baseStart_5255921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255926 : List Nat := [5, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2]
def baseStart_5255926 : Nat := 118140960795 + 5255926 * 2 ^ 59
def prefixEnd_5255926 : Nat := 4983230072969 + 3 ^ 40 * 5255926 * 2
def baseEnd_5255926 : Nat := 2698816322463108399053443

theorem tailTrace_5255926 : CollatzResearch.WordTrace tailWord_5255926 prefixEnd_5255926 2698816322463108399053443 := by
  unfold tailWord_5255926
  simp only [CollatzResearch.WordTrace]
  refine ⟨11981210622292826096317727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127799579971123478360722421 11981210622292826096317727)
  ·
    refine ⟨17971815933439239144476591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11981210622292826096317727 17971815933439239144476591)
    ·
      refine ⟨26957723900158858716714887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17971815933439239144476591 26957723900158858716714887)
      ·
        refine ⟨40436585850238288075072331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26957723900158858716714887 40436585850238288075072331)
        ·
          refine ⟨60654878775357432112608497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40436585850238288075072331 60654878775357432112608497)
          ·
            refine ⟨45491159081518074084456373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60654878775357432112608497 45491159081518074084456373)
            ·
              refine ⟨4264796163892319445417785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45491159081518074084456373 4264796163892319445417785)
              ·
                refine ⟨3198597122919239584063339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4264796163892319445417785 3198597122919239584063339)
                ·
                  refine ⟨4797895684378859376095009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3198597122919239584063339 4797895684378859376095009)
                  ·
                    refine ⟨3598421763284144532071257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4797895684378859376095009 3598421763284144532071257)
                    ·
                      refine ⟨2698816322463108399053443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3598421763284144532071257 2698816322463108399053443)
                      ·
                        rfl

theorem cell23_5255926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_5255926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255926 prefixEnd_5255926 := by exact prefixLift 5255926
  have htrace : WordTrace (prefixWord ++ tailWord_5255926) baseStart_5255926 baseEnd_5255926 := by
    simpa [prefixWord, tailWord_5255926, baseEnd_5255926] using wordTrace_append hprefix tailTrace_5255926
  have hstable : (prefixWord ++ tailWord_5255926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255926).length < 2 ^ (prefixWord ++ tailWord_5255926).sum := by decide
  have hdescent : baseEnd_5255926 < baseStart_5255926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255941 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 2, 6]
def baseStart_5255941 : Nat := 118140960795 + 5255941 * 2 ^ 59
def prefixEnd_5255941 : Nat := 4983230072969 + 3 ^ 40 * 5255941 * 2
def baseEnd_5255941 : Nat := 899608008224308613455291

theorem tailTrace_5255941 : CollatzResearch.WordTrace tailWord_5255941 prefixEnd_5255941 899608008224308613455291 := by
  unfold tailWord_5255941
  simp only [CollatzResearch.WordTrace]
  refine ⟨191699917051630875102879677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127799944701087250068586451 191699917051630875102879677)
  ·
    refine ⟨71887468894361578163579879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191699917051630875102879677 71887468894361578163579879)
    ·
      refine ⟨107831203341542367245369819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71887468894361578163579879 107831203341542367245369819)
      ·
        refine ⟨161746805012313550868054729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107831203341542367245369819 161746805012313550868054729)
        ·
          refine ⟨121310103759235163151041047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161746805012313550868054729 121310103759235163151041047)
          ·
            refine ⟨181965155638852744726561571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121310103759235163151041047 181965155638852744726561571)
            ·
              refine ⟨272947733458279117089842357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181965155638852744726561571 272947733458279117089842357)
              ·
                refine ⟨25588850011713667227172721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 272947733458279117089842357 25588850011713667227172721)
                ·
                  refine ⟨19191637508785250420379541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25588850011713667227172721 19191637508785250420379541)
                  ·
                    refine ⟨899608008224308613455291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19191637508785250420379541 899608008224308613455291)
                    ·
                      rfl

theorem cell23_5255941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_5255941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255941 prefixEnd_5255941 := by exact prefixLift 5255941
  have htrace : WordTrace (prefixWord ++ tailWord_5255941) baseStart_5255941 baseEnd_5255941 := by
    simpa [prefixWord, tailWord_5255941, baseEnd_5255941] using wordTrace_append hprefix tailTrace_5255941
  have hstable : (prefixWord ++ tailWord_5255941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255941).length < 2 ^ (prefixWord ++ tailWord_5255941).sum := by decide
  have hdescent : baseEnd_5255941 < baseStart_5255941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255951 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 5]
def baseStart_5255951 : Nat := 118140960795 + 5255951 * 2 ^ 59
def prefixEnd_5255951 : Nat := 4983230072969 + 3 ^ 40 * 5255951 * 2
def baseEnd_5255951 : Nat := 2698829159479470801240827

theorem tailTrace_5255951 : CollatzResearch.WordTrace tailWord_5255951 prefixEnd_5255951 2698829159479470801240827 := by
  unfold tailWord_5255951
  simp only [CollatzResearch.WordTrace]
  refine ⟨191700281781594646810743707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127800187854396431207162471 191700281781594646810743707)
  ·
    refine ⟨287550422672391970216115561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191700281781594646810743707 287550422672391970216115561)
    ·
      refine ⟨215662817004293977662086671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287550422672391970216115561 215662817004293977662086671)
      ·
        refine ⟨323494225506440966493130007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215662817004293977662086671 323494225506440966493130007)
        ·
          refine ⟨485241338259661449739695011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323494225506440966493130007 485241338259661449739695011)
          ·
            refine ⟨727862007389492174609542517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485241338259661449739695011 727862007389492174609542517)
            ·
              refine ⟨68237063192764891369644611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 727862007389492174609542517 68237063192764891369644611)
              ·
                refine ⟨102355594789147337054466917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68237063192764891369644611 102355594789147337054466917)
                ·
                  refine ⟨19191674022965125697712547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102355594789147337054466917 19191674022965125697712547)
                  ·
                    refine ⟨28787511034447688546568821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19191674022965125697712547 28787511034447688546568821)
                    ·
                      refine ⟨2698829159479470801240827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28787511034447688546568821 2698829159479470801240827)
                      ·
                        rfl

theorem cell23_5255951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 5].length) (baseStart_5255951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255951 prefixEnd_5255951 := by exact prefixLift 5255951
  have htrace : WordTrace (prefixWord ++ tailWord_5255951) baseStart_5255951 baseEnd_5255951 := by
    simpa [prefixWord, tailWord_5255951, baseEnd_5255951] using wordTrace_append hprefix tailTrace_5255951
  have hstable : (prefixWord ++ tailWord_5255951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255951).length < 2 ^ (prefixWord ++ tailWord_5255951).sum := by decide
  have hdescent : baseEnd_5255951 < baseStart_5255951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255961 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 3, 4, 4]
def baseStart_5255961 : Nat := 118140960795 + 5255961 * 2 ^ 59
def prefixEnd_5255961 : Nat := 4983230072969 + 3 ^ 40 * 5255961 * 2
def baseEnd_5255961 : Nat := 2698834294286015762115781

theorem tailTrace_5255961 : CollatzResearch.WordTrace tailWord_5255961 prefixEnd_5255961 2698834294286015762115781 := by
  unfold tailWord_5255961
  simp only [CollatzResearch.WordTrace]
  refine ⟨191700646511558418518607737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127800431007705612345738491 191700646511558418518607737)
  ·
    refine ⟨143775484883668813888955803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191700646511558418518607737 143775484883668813888955803)
    ·
      refine ⟨215663227325503220833433705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143775484883668813888955803 215663227325503220833433705)
      ·
        refine ⟨161747420494127415625075279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215663227325503220833433705 161747420494127415625075279)
        ·
          refine ⟨242621130741191123437612919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161747420494127415625075279 242621130741191123437612919)
          ·
            refine ⟨363931696111786685156419379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242621130741191123437612919 363931696111786685156419379)
            ·
              refine ⟨545897544167680027734629069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363931696111786685156419379 545897544167680027734629069)
              ·
                refine ⟨204711579062880010400485901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 545897544167680027734629069 204711579062880010400485901)
                ·
                  refine ⟨76766842148580003900182213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204711579062880010400485901 76766842148580003900182213)
                  ·
                    refine ⟨14393782902858750731284165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 76766842148580003900182213 14393782902858750731284165)
                    ·
                      refine ⟨2698834294286015762115781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14393782902858750731284165 2698834294286015762115781)
                      ·
                        rfl

theorem cell23_5255961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_5255961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255961 prefixEnd_5255961 := by exact prefixLift 5255961
  have htrace : WordTrace (prefixWord ++ tailWord_5255961) baseStart_5255961 baseEnd_5255961 := by
    simpa [prefixWord, tailWord_5255961, baseEnd_5255961] using wordTrace_append hprefix tailTrace_5255961
  have hstable : (prefixWord ++ tailWord_5255961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255961).length < 2 ^ (prefixWord ++ tailWord_5255961).sum := by decide
  have hdescent : baseEnd_5255961 < baseStart_5255961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255968 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 5]
def baseStart_5255968 : Nat := 118140960795 + 5255968 * 2 ^ 59
def prefixEnd_5255968 : Nat := 4983230072969 + 3 ^ 40 * 5255968 * 2
def baseEnd_5255968 : Nat := 2698837888650597234728249

theorem tailTrace_5255968 : CollatzResearch.WordTrace tailWord_5255968 prefixEnd_5255968 2698837888650597234728249 := by
  unfold tailWord_5255968
  simp only [CollatzResearch.WordTrace]
  refine ⟨95850450911266529357056279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127800601215022039142741705 95850450911266529357056279)
  ·
    refine ⟨143775676366899794035584419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95850450911266529357056279 143775676366899794035584419)
    ·
      refine ⟨215663514550349691053376629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143775676366899794035584419 215663514550349691053376629)
      ·
        refine ⟨20218454489095283536254059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 215663514550349691053376629 20218454489095283536254059)
        ·
          refine ⟨30327681733642925304381089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20218454489095283536254059 30327681733642925304381089)
          ·
            refine ⟨22745761300232193978285817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30327681733642925304381089 22745761300232193978285817)
            ·
              refine ⟨17059320975174145483714363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22745761300232193978285817 17059320975174145483714363)
              ·
                refine ⟨25588981462761218225571545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17059320975174145483714363 25588981462761218225571545)
                ·
                  refine ⟨19191736097070913669178659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25588981462761218225571545 19191736097070913669178659)
                  ·
                    refine ⟨28787604145606370503767989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19191736097070913669178659 28787604145606370503767989)
                    ·
                      refine ⟨2698837888650597234728249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28787604145606370503767989 2698837888650597234728249)
                      ·
                        rfl

theorem cell23_5255968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_5255968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255968 prefixEnd_5255968 := by exact prefixLift 5255968
  have htrace : WordTrace (prefixWord ++ tailWord_5255968) baseStart_5255968 baseEnd_5255968 := by
    simpa [prefixWord, tailWord_5255968, baseEnd_5255968] using wordTrace_append hprefix tailTrace_5255968
  have hstable : (prefixWord ++ tailWord_5255968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255968).length < 2 ^ (prefixWord ++ tailWord_5255968).sum := by decide
  have hdescent : baseEnd_5255968 < baseStart_5255968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256011 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 5]
def baseStart_5256011 : Nat := 118140960795 + 5256011 * 2 ^ 59
def prefixEnd_5256011 : Nat := 4983230072969 + 3 ^ 40 * 5256011 * 2
def baseEnd_5256011 : Nat := 2698859968318740566490551

theorem tailTrace_5256011 : CollatzResearch.WordTrace tailWord_5256011 prefixEnd_5256011 2698859968318740566490551 := by
  unfold tailWord_5256011
  simp only [CollatzResearch.WordTrace]
  refine ⟨191702470161377277057927887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127801646774251518038618591 191702470161377277057927887)
  ·
    refine ⟨287553705242065915586891831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191702470161377277057927887 287553705242065915586891831)
    ·
      refine ⟨431330557863098873380337747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287553705242065915586891831 431330557863098873380337747)
      ·
        refine ⟨646995836794648310070506621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431330557863098873380337747 646995836794648310070506621)
        ·
          refine ⟨242623438797993116276439983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 646995836794648310070506621 242623438797993116276439983)
          ·
            refine ⟨363935158196989674414659975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242623438797993116276439983 363935158196989674414659975)
            ·
              refine ⟨545902737295484511621989963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363935158196989674414659975 545902737295484511621989963)
              ·
                refine ⟨818854105943226767432984945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545902737295484511621989963 818854105943226767432984945)
                ·
                  refine ⟨614140579457420075574738709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 818854105943226767432984945 614140579457420075574738709)
                  ·
                    refine ⟨28787839662066566042565877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 614140579457420075574738709 28787839662066566042565877)
                    ·
                      refine ⟨2698859968318740566490551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28787839662066566042565877 2698859968318740566490551)
                      ·
                        rfl

theorem cell23_5256011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 5].length) (baseStart_5256011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256011 prefixEnd_5256011 := by exact prefixLift 5256011
  have htrace : WordTrace (prefixWord ++ tailWord_5256011) baseStart_5256011 baseEnd_5256011 := by
    simpa [prefixWord, tailWord_5256011, baseEnd_5256011] using wordTrace_append hprefix tailTrace_5256011
  have hstable : (prefixWord ++ tailWord_5256011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256011).length < 2 ^ (prefixWord ++ tailWord_5256011).sum := by decide
  have hdescent : baseEnd_5256011 < baseStart_5256011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256018 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 1, 7]
def baseStart_5256018 : Nat := 118140960795 + 5256018 * 2 ^ 59
def prefixEnd_5256018 : Nat := 4983230072969 + 3 ^ 40 * 5256018 * 2
def baseEnd_5256018 : Nat := 899621187561107346367673

theorem tailTrace_5256018 : CollatzResearch.WordTrace tailWord_5256018 prefixEnd_5256018 899621187561107346367673 := by
  unfold tailWord_5256018
  simp only [CollatzResearch.WordTrace]
  refine ⟨47925681368087979313358177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127801816981567944835621805 47925681368087979313358177)
  ·
    refine ⟨35944261026065984485018633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47925681368087979313358177 35944261026065984485018633)
    ·
      refine ⟨26958195769549488363763975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35944261026065984485018633 26958195769549488363763975)
      ·
        refine ⟨40437293654324232545645963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26958195769549488363763975 40437293654324232545645963)
        ·
          refine ⟨60655940481486348818468945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40437293654324232545645963 60655940481486348818468945)
          ·
            refine ⟨45491955361114761613851709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60655940481486348818468945 45491955361114761613851709)
            ·
              refine ⟨17059483260418035605194391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45491955361114761613851709 17059483260418035605194391)
              ·
                refine ⟨25589224890627053407791587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17059483260418035605194391 25589224890627053407791587)
                ·
                  refine ⟨38383837335940580111687381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25589224890627053407791587 38383837335940580111687381)
                  ·
                    refine ⟨899621187561107346367673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38383837335940580111687381 899621187561107346367673)
                    ·
                      rfl

theorem cell23_5256018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_5256018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256018 prefixEnd_5256018 := by exact prefixLift 5256018
  have htrace : WordTrace (prefixWord ++ tailWord_5256018) baseStart_5256018 baseEnd_5256018 := by
    simpa [prefixWord, tailWord_5256018, baseEnd_5256018] using wordTrace_append hprefix tailTrace_5256018
  have hstable : (prefixWord ++ tailWord_5256018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256018).length < 2 ^ (prefixWord ++ tailWord_5256018).sum := by decide
  have hdescent : baseEnd_5256018 < baseStart_5256018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256068 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_5256068 : Nat := 118140960795 + 5256068 * 2 ^ 59
def prefixEnd_5256068 : Nat := 4983230072969 + 3 ^ 40 * 5256068 * 2
def baseEnd_5256068 : Nat := 2698889236716046843477789

theorem tailTrace_5256068 : CollatzResearch.WordTrace tailWord_5256068 prefixEnd_5256068 2698889236716046843477789 := by
  unfold tailWord_5256068
  simp only [CollatzResearch.WordTrace]
  refine ⟨95852274561085387896376429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127803032748113850528501905 95852274561085387896376429)
  ·
    refine ⟨35944602960407020461141161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95852274561085387896376429 35944602960407020461141161)
    ·
      refine ⟨26958452220305265345855871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35944602960407020461141161 26958452220305265345855871)
      ·
        refine ⟨40437678330457898018783807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26958452220305265345855871 40437678330457898018783807)
        ·
          refine ⟨60656517495686847028175711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40437678330457898018783807 60656517495686847028175711)
          ·
            refine ⟨90984776243530270542263567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60656517495686847028175711 90984776243530270542263567)
            ·
              refine ⟨136477164365295405813395351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90984776243530270542263567 136477164365295405813395351)
              ·
                refine ⟨204715746547943108720093027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136477164365295405813395351 204715746547943108720093027)
                ·
                  refine ⟨307073619821914663080139541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204715746547943108720093027 307073619821914663080139541)
                  ·
                    refine ⟨14394075929152249831881541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 307073619821914663080139541 14394075929152249831881541)
                    ·
                      refine ⟨2698889236716046843477789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14394075929152249831881541 2698889236716046843477789)
                      ·
                        rfl

theorem cell23_5256068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_5256068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256068 prefixEnd_5256068 := by exact prefixLift 5256068
  have htrace : WordTrace (prefixWord ++ tailWord_5256068) baseStart_5256068 baseEnd_5256068 := by
    simpa [prefixWord, tailWord_5256068, baseEnd_5256068] using wordTrace_append hprefix tailTrace_5256068
  have hstable : (prefixWord ++ tailWord_5256068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256068).length < 2 ^ (prefixWord ++ tailWord_5256068).sum := by decide
  have hdescent : baseEnd_5256068 < baseStart_5256068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256108 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 5, 5]
def baseStart_5256108 : Nat := 118140960795 + 5256108 * 2 ^ 59
def prefixEnd_5256108 : Nat := 4983230072969 + 3 ^ 40 * 5256108 * 2
def baseEnd_5256108 : Nat := 899636591980742228992535

theorem tailTrace_5256108 : CollatzResearch.WordTrace tailWord_5256108 prefixEnd_5256108 899636591980742228992535 := by
  unfold tailWord_5256108
  simp only [CollatzResearch.WordTrace]
  refine ⟨95853004021012931312104489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127804005361350575082805985 95853004021012931312104489)
  ·
    refine ⟨71889753015759698484078367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95853004021012931312104489 71889753015759698484078367)
    ·
      refine ⟨107834629523639547726117551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71889753015759698484078367 107834629523639547726117551)
      ·
        refine ⟨161751944285459321589176327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107834629523639547726117551 161751944285459321589176327)
        ·
          refine ⟨242627916428188982383764491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161751944285459321589176327 242627916428188982383764491)
          ·
            refine ⟨363941874642283473575646737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242627916428188982383764491 363941874642283473575646737)
            ·
              refine ⟨272956405981712605181735053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363941874642283473575646737 272956405981712605181735053)
              ·
                refine ⟨102358652243142226943150645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 272956405981712605181735053 102358652243142226943150645)
                ·
                  refine ⟨9596123647794583775920373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102358652243142226943150645 9596123647794583775920373)
                  ·
                    refine ⟨899636591980742228992535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9596123647794583775920373 899636591980742228992535)
                    ·
                      rfl

theorem cell23_5256108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_5256108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256108 prefixEnd_5256108 := by exact prefixLift 5256108
  have htrace : WordTrace (prefixWord ++ tailWord_5256108) baseStart_5256108 baseEnd_5256108 := by
    simpa [prefixWord, tailWord_5256108, baseEnd_5256108] using wordTrace_append hprefix tailTrace_5256108
  have hstable : (prefixWord ++ tailWord_5256108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256108).length < 2 ^ (prefixWord ++ tailWord_5256108).sum := by decide
  have hdescent : baseEnd_5256108 < baseStart_5256108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256115 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 1, 5, 2]
def baseStart_5256115 : Nat := 118140960795 + 5256115 * 2 ^ 59
def prefixEnd_5256115 : Nat := 4983230072969 + 3 ^ 40 * 5256115 * 2
def baseEnd_5256115 : Nat := 2698913370306808159590073

theorem tailTrace_5256115 : CollatzResearch.WordTrace tailWord_5256115 prefixEnd_5256115 2698913370306808159590073 := by
  unfold tailWord_5256115
  simp only [CollatzResearch.WordTrace]
  refine ⟨191706263353000502819713799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127804175568667001879809199 191706263353000502819713799)
  ·
    refine ⟨287559395029500754229570699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191706263353000502819713799 287559395029500754229570699)
    ·
      refine ⟨431339092544251131344356049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287559395029500754229570699 431339092544251131344356049)
      ·
        refine ⟨323504319408188348508267037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 431339092544251131344356049 323504319408188348508267037)
        ·
          refine ⟨121314119778070630690600139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 323504319408188348508267037 121314119778070630690600139)
          ·
            refine ⟨181971179667105946035900209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121314119778070630690600139 181971179667105946035900209)
            ·
              refine ⟨136478384750329459526925157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181971179667105946035900209 136478384750329459526925157)
              ·
                refine ⟨25589697140686773661298467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136478384750329459526925157 25589697140686773661298467)
                ·
                  refine ⟨38384545711030160491947701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25589697140686773661298467 38384545711030160491947701)
                  ·
                    refine ⟨3598551160409077546120097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38384545711030160491947701 3598551160409077546120097)
                    ·
                      refine ⟨2698913370306808159590073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3598551160409077546120097 2698913370306808159590073)
                      ·
                        rfl

theorem cell23_5256115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 5, 2].length) (baseStart_5256115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256115 prefixEnd_5256115 := by exact prefixLift 5256115
  have htrace : WordTrace (prefixWord ++ tailWord_5256115) baseStart_5256115 baseEnd_5256115 := by
    simpa [prefixWord, tailWord_5256115, baseEnd_5256115] using wordTrace_append hprefix tailTrace_5256115
  have hstable : (prefixWord ++ tailWord_5256115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256115).length < 2 ^ (prefixWord ++ tailWord_5256115).sum := by decide
  have hdescent : baseEnd_5256115 < baseStart_5256115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256175 : List Nat := [1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 4]
def baseStart_5256175 : Nat := 118140960795 + 5256175 * 2 ^ 59
def prefixEnd_5256175 : Nat := 4983230072969 + 3 ^ 40 * 5256175 * 2
def baseEnd_5256175 : Nat := 2698944179146077924839797

theorem tailTrace_5256175 : CollatzResearch.WordTrace tailWord_5256175 prefixEnd_5256175 2698944179146077924839797 := by
  unfold tailWord_5256175
  simp only [CollatzResearch.WordTrace]
  refine ⟨191708451732783133066897979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127805634488522088711265319 191708451732783133066897979)
  ·
    refine ⟨287562677599174699600346969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191708451732783133066897979 287562677599174699600346969)
    ·
      refine ⟨215672008199381024700260227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287562677599174699600346969 215672008199381024700260227)
      ·
        refine ⟨323508012299071537050390341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215672008199381024700260227 323508012299071537050390341)
        ·
          refine ⟨60657752306075913196948189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 323508012299071537050390341 60657752306075913196948189)
          ·
            refine ⟨22746657114778467448855571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60657752306075913196948189 22746657114778467448855571)
            ·
              refine ⟨34119985672167701173283357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22746657114778467448855571 34119985672167701173283357)
              ·
                refine ⟨12794994627062887939981259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34119985672167701173283357 12794994627062887939981259)
                ·
                  refine ⟨19192491940594331909971889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12794994627062887939981259 19192491940594331909971889)
                  ·
                    refine ⟨14394368955445748932478917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19192491940594331909971889 14394368955445748932478917)
                    ·
                      refine ⟨2698944179146077924839797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14394368955445748932478917 2698944179146077924839797)
                      ·
                        rfl

theorem cell23_5256175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 4].length) (baseStart_5256175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256175 prefixEnd_5256175 := by exact prefixLift 5256175
  have htrace : WordTrace (prefixWord ++ tailWord_5256175) baseStart_5256175 baseEnd_5256175 := by
    simpa [prefixWord, tailWord_5256175, baseEnd_5256175] using wordTrace_append hprefix tailTrace_5256175
  have hstable : (prefixWord ++ tailWord_5256175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256175).length < 2 ^ (prefixWord ++ tailWord_5256175).sum := by decide
  have hdescent : baseEnd_5256175 < baseStart_5256175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256185 : List Nat := [1, 2, 1, 3, 1, 3, 5, 7]
def baseStart_5256185 : Nat := 118140960795 + 5256185 * 2 ^ 59
def prefixEnd_5256185 : Nat := 4983230072969 + 3 ^ 40 * 5256185 * 2
def baseEnd_5256185 : Nat := 99961085701948995767213

theorem tailTrace_5256185 : CollatzResearch.WordTrace tailWord_5256185 prefixEnd_5256185 99961085701948995767213 := by
  unfold tailWord_5256185
  simp only [CollatzResearch.WordTrace]
  refine ⟨191708816462746904774762009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127805877641831269849841339 191708816462746904774762009)
  ·
    refine ⟨143781612347060178581071507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191708816462746904774762009 143781612347060178581071507)
    ·
      refine ⟨215672418520590267871607261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143781612347060178581071507 215672418520590267871607261)
      ·
        refine ⟨80877156945221350451852723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215672418520590267871607261 80877156945221350451852723)
        ·
          refine ⟨121315735417832025677779085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80877156945221350451852723 121315735417832025677779085)
          ·
            refine ⟨45493400781687009629167157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121315735417832025677779085 45493400781687009629167157)
            ·
              refine ⟨4265006323283157152734421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45493400781687009629167157 4265006323283157152734421)
              ·
                refine ⟨99961085701948995767213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4265006323283157152734421 99961085701948995767213)
                ·
                  rfl

theorem cell23_5256185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 7].length) (baseStart_5256185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256185 prefixEnd_5256185 := by exact prefixLift 5256185
  have htrace : WordTrace (prefixWord ++ tailWord_5256185) baseStart_5256185 baseEnd_5256185 := by
    simpa [prefixWord, tailWord_5256185, baseEnd_5256185] using wordTrace_append hprefix tailTrace_5256185
  have hstable : (prefixWord ++ tailWord_5256185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256185).length < 2 ^ (prefixWord ++ tailWord_5256185).sum := by decide
  have hdescent : baseEnd_5256185 < baseStart_5256185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256208 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 7]
def baseStart_5256208 : Nat := 118140960795 + 5256208 * 2 ^ 59
def prefixEnd_5256208 : Nat := 4983230072969 + 3 ^ 40 * 5256208 * 2
def baseEnd_5256208 : Nat := 2698961124007676295727145

theorem tailTrace_5256208 : CollatzResearch.WordTrace tailWord_5256208 prefixEnd_5256208 2698961124007676295727145 := by
  unfold tailWord_5256208
  simp only [CollatzResearch.WordTrace]
  refine ⟨95854827670831789851424639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127806436894442386468566185 95854827670831789851424639)
  ·
    refine ⟨143782241506247684777136959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95854827670831789851424639 143782241506247684777136959)
    ·
      refine ⟨215673362259371527165705439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143782241506247684777136959 215673362259371527165705439)
      ·
        refine ⟨323510043389057290748558159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215673362259371527165705439 323510043389057290748558159)
        ·
          refine ⟨485265065083585936122837239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323510043389057290748558159 485265065083585936122837239)
          ·
            refine ⟨727897597625378904184255859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485265065083585936122837239 727897597625378904184255859)
            ·
              refine ⟨1091846396438068356276383789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727897597625378904184255859 1091846396438068356276383789)
              ·
                refine ⟨409442398664275633603643921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1091846396438068356276383789 409442398664275633603643921)
                ·
                  refine ⟨307081798998206725202732941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 409442398664275633603643921 307081798998206725202732941)
                  ·
                    refine ⟨115155674624327521951024853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 307081798998206725202732941 115155674624327521951024853)
                    ·
                      refine ⟨2698961124007676295727145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115155674624327521951024853 2698961124007676295727145)
                      ·
                        rfl

theorem cell23_5256208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_5256208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256208 prefixEnd_5256208 := by exact prefixLift 5256208
  have htrace : WordTrace (prefixWord ++ tailWord_5256208) baseStart_5256208 baseEnd_5256208 := by
    simpa [prefixWord, tailWord_5256208, baseEnd_5256208] using wordTrace_append hprefix tailTrace_5256208
  have hstable : (prefixWord ++ tailWord_5256208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256208).length < 2 ^ (prefixWord ++ tailWord_5256208).sum := by decide
  have hdescent : baseEnd_5256208 < baseStart_5256208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256255 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 3]
def baseStart_5256255 : Nat := 118140960795 + 5256255 * 2 ^ 59
def prefixEnd_5256255 : Nat := 4983230072969 + 3 ^ 40 * 5256255 * 2
def baseEnd_5256255 : Nat := 2698985257598437611839429

theorem tailTrace_5256255 : CollatzResearch.WordTrace tailWord_5256255 prefixEnd_5256255 2698985257598437611839429 := by
  unfold tailWord_5256255
  simp only [CollatzResearch.WordTrace]
  refine ⟨191711369572493306729810219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127807579714995537819873479 191711369572493306729810219)
  ·
    refine ⟨287567054358739960094715329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191711369572493306729810219 287567054358739960094715329)
    ·
      refine ⟨215675290769054970071036497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287567054358739960094715329 215675290769054970071036497)
      ·
        refine ⟨161756468076791227553277373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215675290769054970071036497 161756468076791227553277373)
        ·
          refine ⟨60658675528796710332479015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161756468076791227553277373 60658675528796710332479015)
          ·
            refine ⟨90988013293195065498718523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60658675528796710332479015 90988013293195065498718523)
            ·
              refine ⟨136482019939792598248077785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90988013293195065498718523 136482019939792598248077785)
              ·
                refine ⟨102361514954844448686058339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136482019939792598248077785 102361514954844448686058339)
                ·
                  refine ⟨153542272432266673029087509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102361514954844448686058339 153542272432266673029087509)
                  ·
                    refine ⟨7197294020262500298238477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 153542272432266673029087509 7197294020262500298238477)
                    ·
                      refine ⟨2698985257598437611839429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7197294020262500298238477 2698985257598437611839429)
                      ·
                        rfl

theorem cell23_5256255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 3].length) (baseStart_5256255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256255 prefixEnd_5256255 := by exact prefixLift 5256255
  have htrace : WordTrace (prefixWord ++ tailWord_5256255) baseStart_5256255 baseEnd_5256255 := by
    simpa [prefixWord, tailWord_5256255, baseEnd_5256255] using wordTrace_append hprefix tailTrace_5256255
  have hstable : (prefixWord ++ tailWord_5256255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256255).length < 2 ^ (prefixWord ++ tailWord_5256255).sum := by decide
  have hdescent : baseEnd_5256255 < baseStart_5256255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256265 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 2, 2, 4]
def baseStart_5256265 : Nat := 118140960795 + 5256265 * 2 ^ 59
def prefixEnd_5256265 : Nat := 4983230072969 + 3 ^ 40 * 5256265 * 2
def baseEnd_5256265 : Nat := 2698990392404982572714383

theorem tailTrace_5256265 : CollatzResearch.WordTrace tailWord_5256265 prefixEnd_5256265 2698990392404982572714383 := by
  unfold tailWord_5256265
  simp only [CollatzResearch.WordTrace]
  refine ⟨191711734302457078437674249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127807822868304718958449499 191711734302457078437674249)
  ·
    refine ⟨143783800726842808828255687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191711734302457078437674249 143783800726842808828255687)
    ·
      refine ⟨215675701090264213242383531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143783800726842808828255687 215675701090264213242383531)
      ·
        refine ⟨323513551635396319863575297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215675701090264213242383531 323513551635396319863575297)
        ·
          refine ⟨242635163726547239897681473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323513551635396319863575297 242635163726547239897681473)
          ·
            refine ⟨181976372794910429923261105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242635163726547239897681473 181976372794910429923261105)
            ·
              refine ⟨136482279596182822442445829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181976372794910429923261105 136482279596182822442445829)
              ·
                refine ⟨25590427424284279207958593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136482279596182822442445829 25590427424284279207958593)
                ·
                  refine ⟨19192820568213209405968945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25590427424284279207958593 19192820568213209405968945)
                  ·
                    refine ⟨14394615426159907054476709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19192820568213209405968945 14394615426159907054476709)
                    ·
                      refine ⟨2698990392404982572714383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14394615426159907054476709 2698990392404982572714383)
                      ·
                        rfl

theorem cell23_5256265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 2, 4].length) (baseStart_5256265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256265 prefixEnd_5256265 := by exact prefixLift 5256265
  have htrace : WordTrace (prefixWord ++ tailWord_5256265) baseStart_5256265 baseEnd_5256265 := by
    simpa [prefixWord, tailWord_5256265, baseEnd_5256265] using wordTrace_append hprefix tailTrace_5256265
  have hstable : (prefixWord ++ tailWord_5256265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256265).length < 2 ^ (prefixWord ++ tailWord_5256265).sum := by decide
  have hdescent : baseEnd_5256265 < baseStart_5256265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256355 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 6]
def baseStart_5256355 : Nat := 118140960795 + 5256355 * 2 ^ 59
def prefixEnd_5256355 : Nat := 4983230072969 + 3 ^ 40 * 5256355 * 2
def baseEnd_5256355 : Nat := 2699036605663887220588969

theorem tailTrace_5256355 : CollatzResearch.WordTrace tailWord_5256355 prefixEnd_5256355 2699036605663887220588969 := by
  unfold tailWord_5256355
  simp only [CollatzResearch.WordTrace]
  refine ⟨191715016872131023808450519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127810011248087349205633679 191715016872131023808450519)
  ·
    refine ⟨287572525308196535712675779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191715016872131023808450519 287572525308196535712675779)
    ·
      refine ⟨431358787962294803569013669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287572525308196535712675779 431358787962294803569013669)
      ·
        refine ⟨80879772742930275669190063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 431358787962294803569013669 80879772742930275669190063)
        ·
          refine ⟨121319659114395413503785095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80879772742930275669190063 121319659114395413503785095)
          ·
            refine ⟨181979488671593120255677643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121319659114395413503785095 181979488671593120255677643)
            ·
              refine ⟨272969233007389680383516465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181979488671593120255677643 272969233007389680383516465)
              ·
                refine ⟨204726924755542260287637349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272969233007389680383516465 204726924755542260287637349)
                ·
                  refine ⟨38386298391664173803932003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 204726924755542260287637349 38386298391664173803932003)
                  ·
                    refine ⟨57579447587496260705898005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38386298391664173803932003 57579447587496260705898005)
                    ·
                      refine ⟨2699036605663887220588969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57579447587496260705898005 2699036605663887220588969)
                      ·
                        rfl

theorem cell23_5256355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_5256355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256355 prefixEnd_5256355 := by exact prefixLift 5256355
  have htrace : WordTrace (prefixWord ++ tailWord_5256355) baseStart_5256355 baseEnd_5256355 := by
    simpa [prefixWord, tailWord_5256355, baseEnd_5256355] using wordTrace_append hprefix tailTrace_5256355
  have hstable : (prefixWord ++ tailWord_5256355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256355).length < 2 ^ (prefixWord ++ tailWord_5256355).sum := by decide
  have hdescent : baseEnd_5256355 < baseStart_5256355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256359 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_5256359 : Nat := 118140960795 + 5256359 * 2 ^ 59
def prefixEnd_5256359 : Nat := 4983230072969 + 3 ^ 40 * 5256359 * 2
def baseEnd_5256359 : Nat := 2699038659586505204938951

theorem tailTrace_5256359 : CollatzResearch.WordTrace tailWord_5256359 prefixEnd_5256359 2699038659586505204938951 := by
  unfold tailWord_5256359
  simp only [CollatzResearch.WordTrace]
  refine ⟨191715162764116532491596131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127810108509411021661064087 191715162764116532491596131)
  ·
    refine ⟨287572744146174798737394197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191715162764116532491596131 287572744146174798737394197)
    ·
      refine ⟨13479972381851943690815353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 287572744146174798737394197 13479972381851943690815353)
      ·
        refine ⟨10109979286388957768111515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13479972381851943690815353 10109979286388957768111515)
        ·
          refine ⟨15164968929583436652167273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10109979286388957768111515 15164968929583436652167273)
          ·
            refine ⟨11373726697187577489125455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15164968929583436652167273 11373726697187577489125455)
            ·
              refine ⟨17060590045781366233688183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11373726697187577489125455 17060590045781366233688183)
              ·
                refine ⟨25590885068672049350532275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17060590045781366233688183 25590885068672049350532275)
                ·
                  refine ⟨38386327603008074025798413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25590885068672049350532275 38386327603008074025798413)
                  ·
                    refine ⟨14394872851128027759674405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38386327603008074025798413 14394872851128027759674405)
                    ·
                      refine ⟨2699038659586505204938951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14394872851128027759674405 2699038659586505204938951)
                      ·
                        rfl

theorem cell23_5256359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_5256359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256359 prefixEnd_5256359 := by exact prefixLift 5256359
  have htrace : WordTrace (prefixWord ++ tailWord_5256359) baseStart_5256359 baseEnd_5256359 := by
    simpa [prefixWord, tailWord_5256359, baseEnd_5256359] using wordTrace_append hprefix tailTrace_5256359
  have hstable : (prefixWord ++ tailWord_5256359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256359).length < 2 ^ (prefixWord ++ tailWord_5256359).sum := by decide
  have hdescent : baseEnd_5256359 < baseStart_5256359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256395 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 2, 9]
def baseStart_5256395 : Nat := 118140960795 + 5256395 * 2 ^ 59
def prefixEnd_5256395 : Nat := 4983230072969 + 3 ^ 40 * 5256395 * 2
def baseEnd_5256395 : Nat := 899685714963355688029595

theorem tailTrace_5256395 : CollatzResearch.WordTrace tailWord_5256395 prefixEnd_5256395 899685714963355688029595 := by
  unfold tailWord_5256395
  simp only [CollatzResearch.WordTrace]
  refine ⟨191716475791986110639906639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127810983861324073759937759 191716475791986110639906639)
  ·
    refine ⟨287574713687979165959859959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191716475791986110639906639 287574713687979165959859959)
    ·
      refine ⟨431362070531968748939789939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287574713687979165959859959 431362070531968748939789939)
      ·
        refine ⟨647043105797953123409684909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431362070531968748939789939 647043105797953123409684909)
        ·
          refine ⟨242641164674232421278631841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 647043105797953123409684909 242641164674232421278631841)
          ·
            refine ⟨181980873505674315958973881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242641164674232421278631841 181980873505674315958973881)
            ·
              refine ⟨136485655129255736969230411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181980873505674315958973881 136485655129255736969230411)
              ·
                refine ⟨204728482693883605453845617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136485655129255736969230411 204728482693883605453845617)
                ·
                  refine ⟨153546362020412704090384213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204728482693883605453845617 153546362020412704090384213)
                  ·
                    refine ⟨899685714963355688029595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 153546362020412704090384213 899685714963355688029595)
                    ·
                      rfl

theorem cell23_5256395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 9].length) (baseStart_5256395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256395 prefixEnd_5256395 := by exact prefixLift 5256395
  have htrace : WordTrace (prefixWord ++ tailWord_5256395) baseStart_5256395 baseEnd_5256395 := by
    simpa [prefixWord, tailWord_5256395, baseEnd_5256395] using wordTrace_append hprefix tailTrace_5256395
  have hstable : (prefixWord ++ tailWord_5256395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256395).length < 2 ^ (prefixWord ++ tailWord_5256395).sum := by decide
  have hdescent : baseEnd_5256395 < baseStart_5256395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256402 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_5256402 : Nat := 118140960795 + 5256402 * 2 ^ 59
def prefixEnd_5256402 : Nat := 4983230072969 + 3 ^ 40 * 5256402 * 2
def baseEnd_5256402 : Nat := 2699060739254648536701253

theorem tailTrace_5256402 : CollatzResearch.WordTrace tailWord_5256402 prefixEnd_5256402 2699060739254648536701253 := by
  unfold tailWord_5256402
  simp only [CollatzResearch.WordTrace]
  refine ⟨47929182775740187708852865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127811154068640500556940973 47929182775740187708852865)
  ·
    refine ⟨35946887081805140781639649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47929182775740187708852865 35946887081805140781639649)
    ·
      refine ⟨26960165311353855586229737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35946887081805140781639649 26960165311353855586229737)
      ·
        refine ⟨20220123983515391689672303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26960165311353855586229737 20220123983515391689672303)
        ·
          refine ⟨30330185975273087534508455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20220123983515391689672303 30330185975273087534508455)
          ·
            refine ⟨45495278962909631301762683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30330185975273087534508455 45495278962909631301762683)
            ·
              refine ⟨68242918444364446952644025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45495278962909631301762683 68242918444364446952644025)
              ·
                refine ⟨51182188833273335214483019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68242918444364446952644025 51182188833273335214483019)
                ·
                  refine ⟨76773283249910002821724529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51182188833273335214483019 76773283249910002821724529)
                  ·
                    refine ⟨57579962437432502116293397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76773283249910002821724529 57579962437432502116293397)
                    ·
                      refine ⟨2699060739254648536701253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57579962437432502116293397 2699060739254648536701253)
                      ·
                        rfl

theorem cell23_5256402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_5256402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256402 prefixEnd_5256402 := by exact prefixLift 5256402
  have htrace : WordTrace (prefixWord ++ tailWord_5256402) baseStart_5256402 baseEnd_5256402 := by
    simpa [prefixWord, tailWord_5256402, baseEnd_5256402] using wordTrace_append hprefix tailTrace_5256402
  have hstable : (prefixWord ++ tailWord_5256402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256402).length < 2 ^ (prefixWord ++ tailWord_5256402).sum := by decide
  have hdescent : baseEnd_5256402 < baseStart_5256402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256432 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 4]
def baseStart_5256432 : Nat := 118140960795 + 5256432 * 2 ^ 59
def prefixEnd_5256432 : Nat := 4983230072969 + 3 ^ 40 * 5256432 * 2
def baseEnd_5256432 : Nat := 2699076143674283419326115

theorem tailTrace_5256432 : CollatzResearch.WordTrace tailWord_5256432 prefixEnd_5256432 2699076143674283419326115 := by
  unfold tailWord_5256432
  simp only [CollatzResearch.WordTrace]
  refine ⟨95858912646426032979501775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127811883528568043972669033 95858912646426032979501775)
  ·
    refine ⟨143788368969639049469252663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95858912646426032979501775 143788368969639049469252663)
    ·
      refine ⟨215682553454458574203878995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143788368969639049469252663 215682553454458574203878995)
      ·
        refine ⟨323523830181687861305818493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215682553454458574203878995 323523830181687861305818493)
        ·
          refine ⟨121321436318132947989681935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 323523830181687861305818493 121321436318132947989681935)
          ·
            refine ⟨181982154477199421984522903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121321436318132947989681935 181982154477199421984522903)
            ·
              refine ⟨272973231715799132976784355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181982154477199421984522903 272973231715799132976784355)
              ·
                refine ⟨409459847573698699465176533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272973231715799132976784355 409459847573698699465176533)
                ·
                  refine ⟨9596715177508563268715075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 409459847573698699465176533 9596715177508563268715075)
                  ·
                    refine ⟨14395072766262844903072613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9596715177508563268715075 14395072766262844903072613)
                    ·
                      refine ⟨2699076143674283419326115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14395072766262844903072613 2699076143674283419326115)
                      ·
                        rfl

theorem cell23_5256432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 4].length) (baseStart_5256432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256432 prefixEnd_5256432 := by exact prefixLift 5256432
  have htrace : WordTrace (prefixWord ++ tailWord_5256432) baseStart_5256432 baseEnd_5256432 := by
    simpa [prefixWord, tailWord_5256432, baseEnd_5256432] using wordTrace_append hprefix tailTrace_5256432
  have hstable : (prefixWord ++ tailWord_5256432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256432).length < 2 ^ (prefixWord ++ tailWord_5256432).sum := by decide
  have hdescent : baseEnd_5256432 < baseStart_5256432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256450 : List Nat := [3, 4, 1, 1, 4, 1, 2, 1, 6]
def baseStart_5256450 : Nat := 118140960795 + 5256450 * 2 ^ 59
def prefixEnd_5256450 : Nat := 4983230072969 + 3 ^ 40 * 5256450 * 2
def baseEnd_5256450 : Nat := 299898376258451594322337

theorem tailTrace_5256450 : CollatzResearch.WordTrace tailWord_5256450 prefixEnd_5256450 299898376258451594322337 := by
  unfold tailWord_5256450
  simp only [CollatzResearch.WordTrace]
  refine ⟨47929620451696713758289701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127812321204524570022105869 47929620451696713758289701)
  ·
    refine ⟨8986803834693133829679319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47929620451696713758289701 8986803834693133829679319)
    ·
      refine ⟨13480205752039700744518979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8986803834693133829679319 13480205752039700744518979)
      ·
        refine ⟨20220308628059551116778469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13480205752039700744518979 20220308628059551116778469)
        ·
          refine ⟨3791307867761165834395963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20220308628059551116778469 3791307867761165834395963)
          ·
            refine ⟨5686961801641748751593945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3791307867761165834395963 5686961801641748751593945)
            ·
              refine ⟨4265221351231311563695459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5686961801641748751593945 4265221351231311563695459)
              ·
                refine ⟨6397832026846967345543189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4265221351231311563695459 6397832026846967345543189)
                ·
                  refine ⟨299898376258451594322337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6397832026846967345543189 299898376258451594322337)
                  ·
                    rfl

theorem cell23_5256450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_5256450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256450 prefixEnd_5256450 := by exact prefixLift 5256450
  have htrace : WordTrace (prefixWord ++ tailWord_5256450) baseStart_5256450 baseEnd_5256450 := by
    simpa [prefixWord, tailWord_5256450, baseEnd_5256450] using wordTrace_append hprefix tailTrace_5256450
  have hstable : (prefixWord ++ tailWord_5256450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256450).length < 2 ^ (prefixWord ++ tailWord_5256450).sum := by decide
  have hdescent : baseEnd_5256450 < baseStart_5256450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256472 : List Nat := [2, 1, 2, 3, 1, 3, 2, 9]
def baseStart_5256472 : Nat := 118140960795 + 5256472 * 2 ^ 59
def prefixEnd_5256472 : Nat := 4983230072969 + 3 ^ 40 * 5256472 * 2
def baseEnd_5256472 : Nat := 99966543811128268993553

theorem tailTrace_5256472 : CollatzResearch.WordTrace tailWord_5256472 prefixEnd_5256472 99966543811128268993553 := by
  unfold tailWord_5256472
  simp only [CollatzResearch.WordTrace]
  refine ⟨95859642106353576395229835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127812856141804768526973113 95859642106353576395229835)
  ·
    refine ⟨143789463159530364592844753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95859642106353576395229835 143789463159530364592844753)
    ·
      refine ⟨107842097369647773444633565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143789463159530364592844753 107842097369647773444633565)
      ·
        refine ⟨40440786513617915041737587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107842097369647773444633565 40440786513617915041737587)
        ·
          refine ⟨60661179770426872562606381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40440786513617915041737587 60661179770426872562606381)
          ·
            refine ⟨22747942413910077210977393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60661179770426872562606381 22747942413910077210977393)
            ·
              refine ⟨17060956810432557908233045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22747942413910077210977393 17060956810432557908233045)
              ·
                refine ⟨99966543811128268993553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17060956810432557908233045 99966543811128268993553)
                ·
                  rfl

theorem cell23_5256472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 9].length) (baseStart_5256472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256472 prefixEnd_5256472 := by exact prefixLift 5256472
  have htrace : WordTrace (prefixWord ++ tailWord_5256472) baseStart_5256472 baseEnd_5256472 := by
    simpa [prefixWord, tailWord_5256472, baseEnd_5256472] using wordTrace_append hprefix tailTrace_5256472
  have hstable : (prefixWord ++ tailWord_5256472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256472).length < 2 ^ (prefixWord ++ tailWord_5256472).sum := by decide
  have hdescent : baseEnd_5256472 < baseStart_5256472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256493 : List Nat := [1, 5, 3, 1, 1, 1, 1, 4, 2, 4]
def baseStart_5256493 : Nat := 118140960795 + 5256493 * 2 ^ 59
def prefixEnd_5256493 : Nat := 4983230072969 + 3 ^ 40 * 5256493 * 2
def baseEnd_5256493 : Nat := 899702488664735893554445

theorem tailTrace_5256493 : CollatzResearch.WordTrace tailWord_5256493 prefixEnd_5256493 899702488664735893554445 := by
  unfold tailWord_5256493
  simp only [CollatzResearch.WordTrace]
  refine ⟨191720050145631073376974133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127813366763754048917982755 191720050145631073376974133)
  ·
    refine ⟨17973754701152913129091325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191720050145631073376974133 17973754701152913129091325)
    ·
      refine ⟨6740158012932342423409247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17973754701152913129091325 6740158012932342423409247)
      ·
        refine ⟨10110237019398513635113871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6740158012932342423409247 10110237019398513635113871)
        ·
          refine ⟨15165355529097770452670807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10110237019398513635113871 15165355529097770452670807)
          ·
            refine ⟨22748033293646655679006211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15165355529097770452670807 22748033293646655679006211)
            ·
              refine ⟨34122049940469983518509317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22748033293646655679006211 34122049940469983518509317)
              ·
                refine ⟨6397884363838121909720497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34122049940469983518509317 6397884363838121909720497)
                ·
                  refine ⟨4798413272878591432290373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6397884363838121909720497 4798413272878591432290373)
                  ·
                    refine ⟨899702488664735893554445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4798413272878591432290373 899702488664735893554445)
                    ·
                      rfl

theorem cell23_5256493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_5256493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256493 prefixEnd_5256493 := by exact prefixLift 5256493
  have htrace : WordTrace (prefixWord ++ tailWord_5256493) baseStart_5256493 baseEnd_5256493 := by
    simpa [prefixWord, tailWord_5256493, baseEnd_5256493] using wordTrace_append hprefix tailTrace_5256493
  have hstable : (prefixWord ++ tailWord_5256493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256493).length < 2 ^ (prefixWord ++ tailWord_5256493).sum := by decide
  have hdescent : baseEnd_5256493 < baseStart_5256493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256526 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2]
def baseStart_5256526 : Nat := 118140960795 + 5256526 * 2 ^ 59
def prefixEnd_5256526 : Nat := 4983230072969 + 3 ^ 40 * 5256526 * 2
def baseEnd_5256526 : Nat := 2699124410855806051550683

theorem tailTrace_5256526 : CollatzResearch.WordTrace tailWord_5256526 prefixEnd_5256526 2699124410855806051550683 := by
  unfold tailWord_5256526
  simp only [CollatzResearch.WordTrace]
  refine ⟨23965156719313940001615679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127814169169674346675283621 23965156719313940001615679)
  ·
    refine ⟨35947735078970910002423519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23965156719313940001615679 35947735078970910002423519)
    ·
      refine ⟨53921602618456365003635279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35947735078970910002423519 53921602618456365003635279)
      ·
        refine ⟨80882403927684547505452919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53921602618456365003635279 80882403927684547505452919)
        ·
          refine ⟨121323605891526821258179379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80882403927684547505452919 121323605891526821258179379)
          ·
            refine ⟨181985408837290231887269069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121323605891526821258179379 181985408837290231887269069)
            ·
              refine ⟨68244528313983836957725901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181985408837290231887269069 68244528313983836957725901)
              ·
                refine ⟨25591698117743938859147213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68244528313983836957725901 25591698117743938859147213)
                ·
                  refine ⟨9596886794153977072180205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25591698117743938859147213 9596886794153977072180205)
                  ·
                    refine ⟨3598832547807741402067577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9596886794153977072180205 3598832547807741402067577)
                    ·
                      refine ⟨2699124410855806051550683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3598832547807741402067577 2699124410855806051550683)
                      ·
                        rfl

theorem cell23_5256526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2].length) (baseStart_5256526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256526 prefixEnd_5256526 := by exact prefixLift 5256526
  have htrace : WordTrace (prefixWord ++ tailWord_5256526) baseStart_5256526 baseEnd_5256526 := by
    simpa [prefixWord, tailWord_5256526, baseEnd_5256526] using wordTrace_append hprefix tailTrace_5256526
  have hstable : (prefixWord ++ tailWord_5256526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256526).length < 2 ^ (prefixWord ++ tailWord_5256526).sum := by decide
  have hdescent : baseEnd_5256526 < baseStart_5256526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256569 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 2, 2, 4]
def baseStart_5256569 : Nat := 118140960795 + 5256569 * 2 ^ 59
def prefixEnd_5256569 : Nat := 4983230072969 + 3 ^ 40 * 5256569 * 2
def baseEnd_5256569 : Nat := 2699146490523949383312985

theorem tailTrace_5256569 : CollatzResearch.WordTrace tailWord_5256569 prefixEnd_5256569 2699146490523949383312985 := by
  unfold tailWord_5256569
  simp only [CollatzResearch.WordTrace]
  refine ⟨191722822093355738356740761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127815214728903825571160507 191722822093355738356740761)
  ·
    refine ⟨143792116570016803767555571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191722822093355738356740761 143792116570016803767555571)
    ·
      refine ⟨215688174855025205651333357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143792116570016803767555571 215688174855025205651333357)
      ·
        refine ⟨80883065570634452119250009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215688174855025205651333357 80883065570634452119250009)
        ·
          refine ⟨60662299177975839089437507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80883065570634452119250009 60662299177975839089437507)
          ·
            refine ⟨90993448766963758634156261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60662299177975839089437507 90993448766963758634156261)
            ·
              refine ⟨17061271643805704743904299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90993448766963758634156261 17061271643805704743904299)
              ·
                refine ⟨25591907465708557115856449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17061271643805704743904299 25591907465708557115856449)
                ·
                  refine ⟨19193930599281417836892337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25591907465708557115856449 19193930599281417836892337)
                  ·
                    refine ⟨14395447949461063377669253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19193930599281417836892337 14395447949461063377669253)
                    ·
                      refine ⟨2699146490523949383312985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14395447949461063377669253 2699146490523949383312985)
                      ·
                        rfl

theorem cell23_5256569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_5256569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256569 prefixEnd_5256569 := by exact prefixLift 5256569
  have htrace : WordTrace (prefixWord ++ tailWord_5256569) baseStart_5256569 baseEnd_5256569 := by
    simpa [prefixWord, tailWord_5256569, baseEnd_5256569] using wordTrace_append hprefix tailTrace_5256569
  have hstable : (prefixWord ++ tailWord_5256569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256569).length < 2 ^ (prefixWord ++ tailWord_5256569).sum := by decide
  have hdescent : baseEnd_5256569 < baseStart_5256569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256579 : List Nat := [1, 1, 1, 3, 5, 1, 2, 2, 7]
def baseStart_5256579 : Nat := 118140960795 + 5256579 * 2 ^ 59
def prefixEnd_5256579 : Nat := 4983230072969 + 3 ^ 40 * 5256579 * 2
def baseEnd_5256579 : Nat := 299905736147832704909771

theorem tailTrace_5256579 : CollatzResearch.WordTrace tailWord_5256579 prefixEnd_5256579 299905736147832704909771 := by
  unfold tailWord_5256579
  simp only [CollatzResearch.WordTrace]
  refine ⟨191723186823319510064604791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127815457882213006709736527 191723186823319510064604791)
  ·
    refine ⟨287584780234979265096907187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191723186823319510064604791 287584780234979265096907187)
    ·
      refine ⟨431377170352468897645360781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287584780234979265096907187 431377170352468897645360781)
      ·
        refine ⟨161766438882175836617010293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 431377170352468897645360781 161766438882175836617010293)
        ·
          refine ⟨15165603645203984682844715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 161766438882175836617010293 15165603645203984682844715)
          ·
            refine ⟨22748405467805977024267073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15165603645203984682844715 22748405467805977024267073)
            ·
              refine ⟨17061304100854482768200305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22748405467805977024267073 17061304100854482768200305)
              ·
                refine ⟨12795978075640862076150229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17061304100854482768200305 12795978075640862076150229)
                ·
                  refine ⟨299905736147832704909771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12795978075640862076150229 299905736147832704909771)
                  ·
                    rfl

theorem cell23_5256579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 7].length) (baseStart_5256579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256579 prefixEnd_5256579 := by exact prefixLift 5256579
  have htrace : WordTrace (prefixWord ++ tailWord_5256579) baseStart_5256579 baseEnd_5256579 := by
    simpa [prefixWord, tailWord_5256579, baseEnd_5256579] using wordTrace_append hprefix tailTrace_5256579
  have hstable : (prefixWord ++ tailWord_5256579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256579).length < 2 ^ (prefixWord ++ tailWord_5256579).sum := by decide
  have hdescent : baseEnd_5256579 < baseStart_5256579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256686 : List Nat := [4, 1, 2, 1, 2, 1, 1, 5, 6]
def baseStart_5256686 : Nat := 118140960795 + 5256686 * 2 ^ 59
def prefixEnd_5256686 : Nat := 4983230072969 + 3 ^ 40 * 5256686 * 2
def baseEnd_5256686 : Nat := 299911840862280602838883

theorem tailTrace_5256686 : CollatzResearch.WordTrace tailWord_5256686 prefixEnd_5256686 299911840862280602838883 := by
  unfold tailWord_5256686
  simp only [CollatzResearch.WordTrace]
  refine ⟨23965886179241483417343739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127818059622621244892499941 23965886179241483417343739)
  ·
    refine ⟨35948829268862225126015609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23965886179241483417343739 35948829268862225126015609)
    ·
      refine ⟨26961621951646668844511707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35948829268862225126015609 26961621951646668844511707)
      ·
        refine ⟨40442432927470003266767561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26961621951646668844511707 40442432927470003266767561)
        ·
          refine ⟨30331824695602502450075671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40442432927470003266767561 30331824695602502450075671)
          ·
            refine ⟨45497737043403753675113507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30331824695602502450075671 45497737043403753675113507)
            ·
              refine ⟨68246605565105630512670261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45497737043403753675113507 68246605565105630512670261)
              ·
                refine ⟨6398119271728652860562837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68246605565105630512670261 6398119271728652860562837)
                ·
                  refine ⟨299911840862280602838883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6398119271728652860562837 299911840862280602838883)
                  ·
                    rfl

theorem cell23_5256686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_5256686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256686 prefixEnd_5256686 := by exact prefixLift 5256686
  have htrace : WordTrace (prefixWord ++ tailWord_5256686) baseStart_5256686 baseEnd_5256686 := by
    simpa [prefixWord, tailWord_5256686, baseEnd_5256686] using wordTrace_append hprefix tailTrace_5256686
  have hstable : (prefixWord ++ tailWord_5256686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256686).length < 2 ^ (prefixWord ++ tailWord_5256686).sum := by decide
  have hdescent : baseEnd_5256686 < baseStart_5256686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256709 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 2, 4, 5]
def baseStart_5256709 : Nat := 118140960795 + 5256709 * 2 ^ 59
def prefixEnd_5256709 : Nat := 4983230072969 + 3 ^ 40 * 5256709 * 2
def baseEnd_5256709 : Nat := 2699218377815578835562341

theorem tailTrace_5256709 : CollatzResearch.WordTrace tailWord_5256709 prefixEnd_5256709 2699218377815578835562341 := by
  unfold tailWord_5256709
  simp only [CollatzResearch.WordTrace]
  refine ⟨191727928312848542266837181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127818618875232361511224787 191727928312848542266837181)
  ·
    refine ⟨71897973117318203350063943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191727928312848542266837181 71897973117318203350063943)
    ·
      refine ⟨107846959675977305025095915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71897973117318203350063943 107846959675977305025095915)
      ·
        refine ⟨161770439513965957537643873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107846959675977305025095915 161770439513965957537643873)
        ·
          refine ⟨121327829635474468153232905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161770439513965957537643873 121327829635474468153232905)
          ·
            refine ⟨90995872226605851114924679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121327829635474468153232905 90995872226605851114924679)
            ·
              refine ⟨136493808339908776672387019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90995872226605851114924679 136493808339908776672387019)
              ·
                refine ⟨204740712509863165008580529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136493808339908776672387019 204740712509863165008580529)
                ·
                  refine ⟨153555534382397373756435397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204740712509863165008580529 153555534382397373756435397)
                  ·
                    refine ⟨28791662696699507579331637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 153555534382397373756435397 28791662696699507579331637)
                    ·
                      refine ⟨2699218377815578835562341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28791662696699507579331637 2699218377815578835562341)
                      ·
                        rfl

theorem cell23_5256709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_5256709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256709 prefixEnd_5256709 := by exact prefixLift 5256709
  have htrace : WordTrace (prefixWord ++ tailWord_5256709) baseStart_5256709 baseEnd_5256709 := by
    simpa [prefixWord, tailWord_5256709, baseEnd_5256709] using wordTrace_append hprefix tailTrace_5256709
  have hstable : (prefixWord ++ tailWord_5256709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256709).length < 2 ^ (prefixWord ++ tailWord_5256709).sum := by decide
  have hdescent : baseEnd_5256709 < baseStart_5256709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256719 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 4]
def baseStart_5256719 : Nat := 118140960795 + 5256719 * 2 ^ 59
def prefixEnd_5256719 : Nat := 4983230072969 + 3 ^ 40 * 5256719 * 2
def baseEnd_5256719 : Nat := 2699223512622123796437295

theorem tailTrace_5256719 : CollatzResearch.WordTrace tailWord_5256719 prefixEnd_5256719 2699223512622123796437295 := by
  unfold tailWord_5256719
  simp only [CollatzResearch.WordTrace]
  refine ⟨191728293042812313974701211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127818862028541542649800807 191728293042812313974701211)
  ·
    refine ⟨287592439564218470962051817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191728293042812313974701211 287592439564218470962051817)
    ·
      refine ⟨215694329673163853221538863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287592439564218470962051817 215694329673163853221538863)
      ·
        refine ⟨323541494509745779832308295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215694329673163853221538863 323541494509745779832308295)
        ·
          refine ⟨485312241764618669748462443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323541494509745779832308295 485312241764618669748462443)
          ·
            refine ⟨727968362646928004622693665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485312241764618669748462443 727968362646928004622693665)
            ·
              refine ⟨545976271985196003467020249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 727968362646928004622693665 545976271985196003467020249)
              ·
                refine ⟨409482203988897002600265187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 545976271985196003467020249 409482203988897002600265187)
                ·
                  refine ⟨614223305983345503900397781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 409482203988897002600265187 614223305983345503900397781)
                  ·
                    refine ⟨14395858733984660247665573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 614223305983345503900397781 14395858733984660247665573)
                    ·
                      refine ⟨2699223512622123796437295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14395858733984660247665573 2699223512622123796437295)
                      ·
                        rfl

theorem cell23_5256719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 4].length) (baseStart_5256719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256719 prefixEnd_5256719 := by exact prefixLift 5256719
  have htrace : WordTrace (prefixWord ++ tailWord_5256719) baseStart_5256719 baseEnd_5256719 := by
    simpa [prefixWord, tailWord_5256719, baseEnd_5256719] using wordTrace_append hprefix tailTrace_5256719
  have hstable : (prefixWord ++ tailWord_5256719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256719).length < 2 ^ (prefixWord ++ tailWord_5256719).sum := by decide
  have hdescent : baseEnd_5256719 < baseStart_5256719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256750 : List Nat := [4, 1, 3, 1, 2, 2, 2, 2, 1, 5]
def baseStart_5256750 : Nat := 118140960795 + 5256750 * 2 ^ 59
def prefixEnd_5256750 : Nat := 4983230072969 + 3 ^ 40 * 5256750 * 2
def baseEnd_5256750 : Nat := 899746476840804391716551

theorem tailTrace_5256750 : CollatzResearch.WordTrace tailWord_5256750 prefixEnd_5256750 899746476840804391716551 := by
  unfold tailWord_5256750
  simp only [CollatzResearch.WordTrace]
  refine ⟨23966177963212500783634963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127819615803800004179386469 23966177963212500783634963)
  ·
    refine ⟨35949266944818751175452445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23966177963212500783634963 35949266944818751175452445)
    ·
      refine ⟨13480975104307031690794667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35949266944818751175452445 13480975104307031690794667)
      ·
        refine ⟨20221462656460547536192001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13480975104307031690794667 20221462656460547536192001)
        ·
          refine ⟨15166096992345410652144001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20221462656460547536192001 15166096992345410652144001)
          ·
            refine ⟨11374572744259057989108001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15166096992345410652144001 11374572744259057989108001)
            ·
              refine ⟨8530929558194293491831001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11374572744259057989108001 8530929558194293491831001)
              ·
                refine ⟨6398197168645720118873251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8530929558194293491831001 6398197168645720118873251)
                ·
                  refine ⟨9597295752968580178309877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6398197168645720118873251 9597295752968580178309877)
                  ·
                    refine ⟨899746476840804391716551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9597295752968580178309877 899746476840804391716551)
                    ·
                      rfl

theorem cell23_5256750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_5256750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256750 prefixEnd_5256750 := by exact prefixLift 5256750
  have htrace : WordTrace (prefixWord ++ tailWord_5256750) baseStart_5256750 baseEnd_5256750 := by
    simpa [prefixWord, tailWord_5256750, baseEnd_5256750] using wordTrace_append hprefix tailTrace_5256750
  have hstable : (prefixWord ++ tailWord_5256750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256750).length < 2 ^ (prefixWord ++ tailWord_5256750).sum := by decide
  have hdescent : baseEnd_5256750 < baseStart_5256750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256764 : List Nat := [2, 2, 2, 2, 4, 2, 1, 3, 1, 1, 3]
def baseStart_5256764 : Nat := 118140960795 + 5256764 * 2 ^ 59
def prefixEnd_5256764 : Nat := 4983230072969 + 3 ^ 40 * 5256764 * 2
def baseEnd_5256764 : Nat := 2699246619251576120374589

theorem tailTrace_5256764 : CollatzResearch.WordTrace tailWord_5256764 prefixEnd_5256764 2699246619251576120374589 := by
  unfold tailWord_5256764
  simp only [CollatzResearch.WordTrace]
  refine ⟨95864967163824643330044673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127819956218432857773392897 95864967163824643330044673)
  ·
    refine ⟨71898725372868482497533505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95864967163824643330044673 71898725372868482497533505)
    ·
      refine ⟨53924044029651361873150129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71898725372868482497533505 53924044029651361873150129)
      ·
        refine ⟨40443033022238521404862597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53924044029651361873150129 40443033022238521404862597)
        ·
          refine ⟨7583068691669722763411737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40443033022238521404862597 7583068691669722763411737)
          ·
            refine ⟨5687301518752292072558803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7583068691669722763411737 5687301518752292072558803)
            ·
              refine ⟨8530952278128438108838205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5687301518752292072558803 8530952278128438108838205)
              ·
                refine ⟨3199107104298164290814327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8530952278128438108838205 3199107104298164290814327)
                ·
                  refine ⟨4798660656447246436221491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3199107104298164290814327 4798660656447246436221491)
                  ·
                    refine ⟨7197990984670869654332237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4798660656447246436221491 7197990984670869654332237)
                    ·
                      refine ⟨2699246619251576120374589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7197990984670869654332237 2699246619251576120374589)
                      ·
                        rfl

theorem cell23_5256764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_5256764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256764 prefixEnd_5256764 := by exact prefixLift 5256764
  have htrace : WordTrace (prefixWord ++ tailWord_5256764) baseStart_5256764 baseEnd_5256764 := by
    simpa [prefixWord, tailWord_5256764, baseEnd_5256764] using wordTrace_append hprefix tailTrace_5256764
  have hstable : (prefixWord ++ tailWord_5256764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256764).length < 2 ^ (prefixWord ++ tailWord_5256764).sum := by decide
  have hdescent : baseEnd_5256764 < baseStart_5256764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256773 : List Nat := [1, 3, 1, 1, 1, 4, 1, 5, 1, 2, 3]
def baseStart_5256773 : Nat := 118140960795 + 5256773 * 2 ^ 59
def prefixEnd_5256773 : Nat := 4983230072969 + 3 ^ 40 * 5256773 * 2
def baseEnd_5256773 : Nat := 2699251240577466585162047

theorem tailTrace_5256773 : CollatzResearch.WordTrace tailWord_5256773 prefixEnd_5256773 2699251240577466585162047 := by
  unfold tailWord_5256773
  simp only [CollatzResearch.WordTrace]
  refine ⟨191730262584616681197166973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127820175056411120798111315 191730262584616681197166973)
  ·
    refine ⟨71898848469231255448937615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191730262584616681197166973 71898848469231255448937615)
    ·
      refine ⟨107848272703846883173406423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71898848469231255448937615 107848272703846883173406423)
      ·
        refine ⟨161772409055770324760109635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107848272703846883173406423 161772409055770324760109635)
        ·
          refine ⟨242658613583655487140164453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161772409055770324760109635 242658613583655487140164453)
          ·
            refine ⟨45498490046935403838780835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 242658613583655487140164453 45498490046935403838780835)
            ·
              refine ⟨68247735070403105758171253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45498490046935403838780835 68247735070403105758171253)
              ·
                refine ⟨6398225162850291164828555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68247735070403105758171253 6398225162850291164828555)
                ·
                  refine ⟨9597337744275436747242833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6398225162850291164828555 9597337744275436747242833)
                  ·
                    refine ⟨7198003308206577560432125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9597337744275436747242833 7198003308206577560432125)
                    ·
                      refine ⟨2699251240577466585162047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7198003308206577560432125 2699251240577466585162047)
                      ·
                        rfl

theorem cell23_5256773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 2, 3].length) (baseStart_5256773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256773 prefixEnd_5256773 := by exact prefixLift 5256773
  have htrace : WordTrace (prefixWord ++ tailWord_5256773) baseStart_5256773 baseEnd_5256773 := by
    simpa [prefixWord, tailWord_5256773, baseEnd_5256773] using wordTrace_append hprefix tailTrace_5256773
  have hstable : (prefixWord ++ tailWord_5256773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256773).length < 2 ^ (prefixWord ++ tailWord_5256773).sum := by decide
  have hdescent : baseEnd_5256773 < baseStart_5256773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256774 : List Nat := [6, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2]
def baseStart_5256774 : Nat := 118140960795 + 5256774 * 2 ^ 59
def prefixEnd_5256774 : Nat := 4983230072969 + 3 ^ 40 * 5256774 * 2
def baseEnd_5256774 : Nat := 2699251754058121081249543

theorem tailTrace_5256774 : CollatzResearch.WordTrace tailWord_5256774 prefixEnd_5256774 2699251754058121081249543 := by
  unfold tailWord_5256774
  simp only [CollatzResearch.WordTrace]
  refine ⟨5991571845550408073998543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 127820199371742038911968917 5991571845550408073998543)
  ·
    refine ⟨8987357768325612110997815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5991571845550408073998543 8987357768325612110997815)
    ·
      refine ⟨13481036652488418166496723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8987357768325612110997815 13481036652488418166496723)
      ·
        refine ⟨20221554978732627249745085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13481036652488418166496723 20221554978732627249745085)
        ·
          refine ⟨7583083117024735218654407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20221554978732627249745085 7583083117024735218654407)
          ·
            refine ⟨11374624675537102827981611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7583083117024735218654407 11374624675537102827981611)
            ·
              refine ⟨17061937013305654241972417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11374624675537102827981611 17061937013305654241972417)
              ·
                refine ⟨12796452759979240681479313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17061937013305654241972417 12796452759979240681479313)
                ·
                  refine ⟨9597339569984430511109485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12796452759979240681479313 9597339569984430511109485)
                  ·
                    refine ⟨3599002338744161441666057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9597339569984430511109485 3599002338744161441666057)
                    ·
                      refine ⟨2699251754058121081249543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3599002338744161441666057 2699251754058121081249543)
                      ·
                        rfl

theorem cell23_5256774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_5256774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256774 prefixEnd_5256774 := by exact prefixLift 5256774
  have htrace : WordTrace (prefixWord ++ tailWord_5256774) baseStart_5256774 baseEnd_5256774 := by
    simpa [prefixWord, tailWord_5256774, baseEnd_5256774] using wordTrace_append hprefix tailTrace_5256774
  have hstable : (prefixWord ++ tailWord_5256774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256774).length < 2 ^ (prefixWord ++ tailWord_5256774).sum := by decide
  have hdescent : baseEnd_5256774 < baseStart_5256774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256781 : List Nat := [1, 6, 1, 1, 3, 1, 3, 2, 1, 1, 3]
def baseStart_5256781 : Nat := 118140960795 + 5256781 * 2 ^ 59
def prefixEnd_5256781 : Nat := 4983230072969 + 3 ^ 40 * 5256781 * 2
def baseEnd_5256781 : Nat := 2699255348422702553862011

theorem tailTrace_5256781 : CollatzResearch.WordTrace tailWord_5256781 prefixEnd_5256781 2699255348422702553862011 := by
  unfold tailWord_5256781
  simp only [CollatzResearch.WordTrace]
  refine ⟨191730554368587698563458197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127820369579058465708972131 191730554368587698563458197)
  ·
    refine ⟨8987369736027548370162103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 191730554368587698563458197 8987369736027548370162103)
    ·
      refine ⟨13481054604041322555243155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8987369736027548370162103 13481054604041322555243155)
      ·
        refine ⟨20221581906061983832864733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13481054604041322555243155 20221581906061983832864733)
        ·
          refine ⟨7583093214773243937324275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20221581906061983832864733 7583093214773243937324275)
          ·
            refine ⟨11374639822159865905986413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7583093214773243937324275 11374639822159865905986413)
            ·
              refine ⟨4265489933309949714744905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11374639822159865905986413 4265489933309949714744905)
              ·
                refine ⟨3199117449982462286058679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4265489933309949714744905 3199117449982462286058679)
                ·
                  refine ⟨4798676174973693429088019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3199117449982462286058679 4798676174973693429088019)
                  ·
                    refine ⟨7198014262460540143632029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4798676174973693429088019 7198014262460540143632029)
                    ·
                      refine ⟨2699255348422702553862011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7198014262460540143632029 2699255348422702553862011)
                      ·
                        rfl

theorem cell23_5256781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_5256781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256781 prefixEnd_5256781 := by exact prefixLift 5256781
  have htrace : WordTrace (prefixWord ++ tailWord_5256781) baseStart_5256781 baseEnd_5256781 := by
    simpa [prefixWord, tailWord_5256781, baseEnd_5256781] using wordTrace_append hprefix tailTrace_5256781
  have hstable : (prefixWord ++ tailWord_5256781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256781).length < 2 ^ (prefixWord ++ tailWord_5256781).sum := by decide
  have hdescent : baseEnd_5256781 < baseStart_5256781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256843 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 3, 4, 2]
def baseStart_5256843 : Nat := 118140960795 + 5256843 * 2 ^ 59
def prefixEnd_5256843 : Nat := 4983230072969 + 3 ^ 40 * 5256843 * 2
def baseEnd_5256843 : Nat := 2699287184223281311286725

theorem tailTrace_5256843 : CollatzResearch.WordTrace tailWord_5256843 prefixEnd_5256843 2699287184223281311286725 := by
  unfold tailWord_5256843
  simp only [CollatzResearch.WordTrace]
  refine ⟨191732815694363083152215183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127821877129575388768143455 191732815694363083152215183)
  ·
    refine ⟨287599223541544624728322775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191732815694363083152215183 287599223541544624728322775)
    ·
      refine ⟨431398835312316937092484163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287599223541544624728322775 431398835312316937092484163)
      ·
        refine ⟨647098252968475405638726245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431398835312316937092484163 647098252968475405638726245)
        ·
          refine ⟨121330922431589138557261171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 647098252968475405638726245 121330922431589138557261171)
          ·
            refine ⟨181996383647383707835891757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121330922431589138557261171 181996383647383707835891757)
            ·
              refine ⟨68248643867768890438459409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181996383647383707835891757 68248643867768890438459409)
              ·
                refine ⟨51186482900826667828844557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68248643867768890438459409 51186482900826667828844557)
                ·
                  refine ⟨19194931087810000435816709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51186482900826667828844557 19194931087810000435816709)
                  ·
                    refine ⟨3599049578964375081715633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19194931087810000435816709 3599049578964375081715633)
                    ·
                      refine ⟨2699287184223281311286725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3599049578964375081715633 2699287184223281311286725)
                      ·
                        rfl

theorem cell23_5256843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 4, 2].length) (baseStart_5256843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256843 prefixEnd_5256843 := by exact prefixLift 5256843
  have htrace : WordTrace (prefixWord ++ tailWord_5256843) baseStart_5256843 baseEnd_5256843 := by
    simpa [prefixWord, tailWord_5256843, baseEnd_5256843] using wordTrace_append hprefix tailTrace_5256843
  have hstable : (prefixWord ++ tailWord_5256843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256843).length < 2 ^ (prefixWord ++ tailWord_5256843).sum := by decide
  have hdescent : baseEnd_5256843 < baseStart_5256843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256877 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 4, 2, 2]
def baseStart_5256877 : Nat := 118140960795 + 5256877 * 2 ^ 59
def prefixEnd_5256877 : Nat := 4983230072969 + 3 ^ 40 * 5256877 * 2
def baseEnd_5256877 : Nat := 2699304642565534178261569

theorem tailTrace_5256877 : CollatzResearch.WordTrace tailWord_5256877 prefixEnd_5256877 2699304642565534178261569 := by
  unfold tailWord_5256877
  simp only [CollatzResearch.WordTrace]
  refine ⟨191734055776239906958952885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127822703850826604639301923 191734055776239906958952885)
  ·
    refine ⟨17975067729022491277401833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191734055776239906958952885 17975067729022491277401833)
    ·
      refine ⟨13481300796766868458051375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17975067729022491277401833 13481300796766868458051375)
      ·
        refine ⟨20221951195150302687077063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13481300796766868458051375 20221951195150302687077063)
        ·
          refine ⟨30332926792725454030615595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20221951195150302687077063 30332926792725454030615595)
          ·
            refine ⟨45499390189088181045923393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30332926792725454030615595 45499390189088181045923393)
            ·
              refine ⟨34124542641816135784442545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45499390189088181045923393 34124542641816135784442545)
              ·
                refine ⟨25593406981362101838331909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34124542641816135784442545 25593406981362101838331909)
                ·
                  refine ⟨4798763809005394094687233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25593406981362101838331909 4798763809005394094687233)
                  ·
                    refine ⟨3599072856754045571015425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4798763809005394094687233 3599072856754045571015425)
                    ·
                      refine ⟨2699304642565534178261569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3599072856754045571015425 2699304642565534178261569)
                      ·
                        rfl

theorem cell23_5256877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_5256877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256877 prefixEnd_5256877 := by exact prefixLift 5256877
  have htrace : WordTrace (prefixWord ++ tailWord_5256877) baseStart_5256877 baseEnd_5256877 := by
    simpa [prefixWord, tailWord_5256877, baseEnd_5256877] using wordTrace_append hprefix tailTrace_5256877
  have hstable : (prefixWord ++ tailWord_5256877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256877).length < 2 ^ (prefixWord ++ tailWord_5256877).sum := by decide
  have hdescent : baseEnd_5256877 < baseStart_5256877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256893 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 4, 3, 3]
def baseStart_5256893 : Nat := 118140960795 + 5256893 * 2 ^ 59
def prefixEnd_5256893 : Nat := 4983230072969 + 3 ^ 40 * 5256893 * 2
def baseEnd_5256893 : Nat := 2699312858256006115661495

theorem tailTrace_5256893 : CollatzResearch.WordTrace tailWord_5256893 prefixEnd_5256893 2699312858256006115661495 := by
  unfold tailWord_5256893
  simp only [CollatzResearch.WordTrace]
  refine ⟨191734639344181941691535333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127823092896121294461023555 191734639344181941691535333)
  ·
    refine ⟨35950244877034114067162875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191734639344181941691535333 35950244877034114067162875)
    ·
      refine ⟨53925367315551171100744313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35950244877034114067162875 53925367315551171100744313)
      ·
        refine ⟨40444025486663378325558235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53925367315551171100744313 40444025486663378325558235)
        ·
          refine ⟨60666038229995067488337353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40444025486663378325558235 60666038229995067488337353)
          ·
            refine ⟨45499528672496300616253015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60666038229995067488337353 45499528672496300616253015)
            ·
              refine ⟨68249293008744450924379523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45499528672496300616253015 68249293008744450924379523)
              ·
                refine ⟨102373939513116676386569285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68249293008744450924379523 102373939513116676386569285)
                ·
                  refine ⟨19195113658709376822481741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102373939513116676386569285 19195113658709376822481741)
                  ·
                    refine ⟨7198167622016016308430653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19195113658709376822481741 7198167622016016308430653)
                    ·
                      refine ⟨2699312858256006115661495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7198167622016016308430653 2699312858256006115661495)
                      ·
                        rfl

theorem cell23_5256893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_5256893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256893 prefixEnd_5256893 := by exact prefixLift 5256893
  have htrace : WordTrace (prefixWord ++ tailWord_5256893) baseStart_5256893 baseEnd_5256893 := by
    simpa [prefixWord, tailWord_5256893, baseEnd_5256893] using wordTrace_append hprefix tailTrace_5256893
  have hstable : (prefixWord ++ tailWord_5256893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256893).length < 2 ^ (prefixWord ++ tailWord_5256893).sum := by decide
  have hdescent : baseEnd_5256893 < baseStart_5256893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256894 : List Nat := [4, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2]
def baseStart_5256894 : Nat := 118140960795 + 5256894 * 2 ^ 59
def prefixEnd_5256894 : Nat := 4983230072969 + 3 ^ 40 * 5256894 * 2
def baseEnd_5256894 : Nat := 2699313371736660611748991

theorem tailTrace_5256894 : CollatzResearch.WordTrace tailWord_5256894 prefixEnd_5256894 2699313371736660611748991 := by
  unfold tailWord_5256894
  simp only [CollatzResearch.WordTrace]
  refine ⟨23966834477147289857790217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127823117211452212574881157 23966834477147289857790217)
  ·
    refine ⟨17975125857860467393342663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23966834477147289857790217 17975125857860467393342663)
    ·
      refine ⟨26962688786790701090013995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17975125857860467393342663 26962688786790701090013995)
      ·
        refine ⟨40444033180186051635020993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26962688786790701090013995 40444033180186051635020993)
        ·
          refine ⟨30333024885139538726265745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40444033180186051635020993 30333024885139538726265745)
          ·
            refine ⟨22749768663854654044699309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30333024885139538726265745 22749768663854654044699309)
            ·
              refine ⟨8531163248945495266762241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22749768663854654044699309 8531163248945495266762241)
              ·
                refine ⟨6398372436709121450071681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8531163248945495266762241 6398372436709121450071681)
                ·
                  refine ⟨4798779327531841087553761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6398372436709121450071681 4798779327531841087553761)
                  ·
                    refine ⟨3599084495648880815665321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4798779327531841087553761 3599084495648880815665321)
                    ·
                      refine ⟨2699313371736660611748991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3599084495648880815665321 2699313371736660611748991)
                      ·
                        rfl

theorem cell23_5256894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_5256894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256894 prefixEnd_5256894 := by exact prefixLift 5256894
  have htrace : WordTrace (prefixWord ++ tailWord_5256894) baseStart_5256894 baseEnd_5256894 := by
    simpa [prefixWord, tailWord_5256894, baseEnd_5256894] using wordTrace_append hprefix tailTrace_5256894
  have hstable : (prefixWord ++ tailWord_5256894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256894).length < 2 ^ (prefixWord ++ tailWord_5256894).sum := by decide
  have hdescent : baseEnd_5256894 < baseStart_5256894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256900 : List Nat := [2, 3, 3, 1, 1, 1, 1, 6, 5]
def baseStart_5256900 : Nat := 118140960795 + 5256900 * 2 ^ 59
def prefixEnd_5256900 : Nat := 4983230072969 + 3 ^ 40 * 5256900 * 2
def baseEnd_5256900 : Nat := 299924050291176398697107

theorem tailTrace_5256900 : CollatzResearch.WordTrace tailWord_5256900 prefixEnd_5256900 299924050291176398697107 := by
  unfold tailWord_5256900
  simp only [CollatzResearch.WordTrace]
  refine ⟨95867447327578290943520077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127823263103437721258026769 95867447327578290943520077)
  ·
    refine ⟨35950292747841859103820029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95867447327578290943520077 35950292747841859103820029)
    ·
      refine ⟨13481359780440697163932511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35950292747841859103820029 13481359780440697163932511)
      ·
        refine ⟨20222039670661045745898767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13481359780440697163932511 20222039670661045745898767)
        ·
          refine ⟨30333059505991568618848151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20222039670661045745898767 30333059505991568618848151)
          ·
            refine ⟨45499589258987352928272227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30333059505991568618848151 45499589258987352928272227)
            ·
              refine ⟨68249383888481029392408341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45499589258987352928272227 68249383888481029392408341)
              ·
                refine ⟨3199189869772548252769141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68249383888481029392408341 3199189869772548252769141)
                ·
                  refine ⟨299924050291176398697107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3199189869772548252769141 299924050291176398697107)
                  ·
                    rfl

theorem cell23_5256900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_5256900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256900 prefixEnd_5256900 := by exact prefixLift 5256900
  have htrace : WordTrace (prefixWord ++ tailWord_5256900) baseStart_5256900 baseEnd_5256900 := by
    simpa [prefixWord, tailWord_5256900, baseEnd_5256900] using wordTrace_append hprefix tailTrace_5256900
  have hstable : (prefixWord ++ tailWord_5256900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256900).length < 2 ^ (prefixWord ++ tailWord_5256900).sum := by decide
  have hdescent : baseEnd_5256900 < baseStart_5256900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256933 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 1, 3, 4]
def baseStart_5256933 : Nat := 118140960795 + 5256933 * 2 ^ 59
def prefixEnd_5256933 : Nat := 4983230072969 + 3 ^ 40 * 5256933 * 2
def baseEnd_5256933 : Nat := 2699333397482185959161311

theorem tailTrace_5256933 : CollatzResearch.WordTrace tailWord_5256933 prefixEnd_5256933 2699333397482185959161311 := by
  unfold tailWord_5256933
  simp only [CollatzResearch.WordTrace]
  refine ⟨191736098264037028522991453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127824065509358019015327635 191736098264037028522991453)
  ·
    refine ⟨71901036849013885696121795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191736098264037028522991453 71901036849013885696121795)
    ·
      refine ⟨107851555273520828544182693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71901036849013885696121795 107851555273520828544182693)
      ·
        refine ⟨20222166613785155352034255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107851555273520828544182693 20222166613785155352034255)
        ·
          refine ⟨30333249920677733028051383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20222166613785155352034255 30333249920677733028051383)
          ·
            refine ⟨45499874881016599542077075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30333249920677733028051383 45499874881016599542077075)
            ·
              refine ⟨68249812321524899313115613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45499874881016599542077075 68249812321524899313115613)
              ·
                refine ⟨25593679620571837242418355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68249812321524899313115613 25593679620571837242418355)
                ·
                  refine ⟨38390519430857755863627533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25593679620571837242418355 38390519430857755863627533)
                  ·
                    refine ⟨14396444786571658448860325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38390519430857755863627533 14396444786571658448860325)
                    ·
                      refine ⟨2699333397482185959161311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14396444786571658448860325 2699333397482185959161311)
                      ·
                        rfl

theorem cell23_5256933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_5256933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256933 prefixEnd_5256933 := by exact prefixLift 5256933
  have htrace : WordTrace (prefixWord ++ tailWord_5256933) baseStart_5256933 baseEnd_5256933 := by
    simpa [prefixWord, tailWord_5256933, baseEnd_5256933] using wordTrace_append hprefix tailTrace_5256933
  have hstable : (prefixWord ++ tailWord_5256933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256933).length < 2 ^ (prefixWord ++ tailWord_5256933).sum := by decide
  have hdescent : baseEnd_5256933 < baseStart_5256933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5256950 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_5256950 : Nat := 118140960795 + 5256950 * 2 ^ 59
def prefixEnd_5256950 : Nat := 4983230072969 + 3 ^ 40 * 5256950 * 2
def baseEnd_5256950 : Nat := 2699342126653312392648733

theorem tailTrace_5256950 : CollatzResearch.WordTrace tailWord_5256950 prefixEnd_5256950 2699342126653312392648733 := by
  unfold tailWord_5256950
  simp only [CollatzResearch.WordTrace]
  refine ⟨11983544894060965026647519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127824478869983626950906869 11983544894060965026647519)
  ·
    refine ⟨17975317341091447539971279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11983544894060965026647519 17975317341091447539971279)
    ·
      refine ⟨26962976011637171309956919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17975317341091447539971279 26962976011637171309956919)
      ·
        refine ⟨40444464017455756964935379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26962976011637171309956919 40444464017455756964935379)
        ·
          refine ⟨60666696026183635447403069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40444464017455756964935379 60666696026183635447403069)
          ·
            refine ⟨22750011009818863292776151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60666696026183635447403069 22750011009818863292776151)
            ·
              refine ⟨34125016514728294939164227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22750011009818863292776151 34125016514728294939164227)
              ·
                refine ⟨51187524772092442408746341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34125016514728294939164227 51187524772092442408746341)
                ·
                  refine ⟨9597660894767332951639939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51187524772092442408746341 9597660894767332951639939)
                  ·
                    refine ⟨14396491342150999427459909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9597660894767332951639939 14396491342150999427459909)
                    ·
                      refine ⟨2699342126653312392648733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14396491342150999427459909 2699342126653312392648733)
                      ·
                        rfl

theorem cell23_5256950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_5256950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5256950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5256950 prefixEnd_5256950 := by exact prefixLift 5256950
  have htrace : WordTrace (prefixWord ++ tailWord_5256950) baseStart_5256950 baseEnd_5256950 := by
    simpa [prefixWord, tailWord_5256950, baseEnd_5256950] using wordTrace_append hprefix tailTrace_5256950
  have hstable : (prefixWord ++ tailWord_5256950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5256950).length < 2 ^ (prefixWord ++ tailWord_5256950).sum := by decide
  have hdescent : baseEnd_5256950 < baseStart_5256950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5256950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257011 : List Nat := [1, 1, 1, 2, 7, 2, 2, 2, 1, 4]
def baseStart_5257011 : Nat := 118140960795 + 5257011 * 2 ^ 59
def prefixEnd_5257011 : Nat := 4983230072969 + 3 ^ 40 * 5257011 * 2
def baseEnd_5257011 : Nat := 899791149657745551328651

theorem tailTrace_5257011 : CollatzResearch.WordTrace tailWord_5257011 prefixEnd_5257011 899791149657745551328651 := by
  unfold tailWord_5257011
  simp only [CollatzResearch.WordTrace]
  refine ⟨191738943157754447844330887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127825962105169631896220591 191738943157754447844330887)
  ·
    refine ⟨287608414736631671766496331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191738943157754447844330887 287608414736631671766496331)
    ·
      refine ⟨431412622104947507649744497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287608414736631671766496331 431412622104947507649744497)
      ·
        refine ⟨323559466578710630737308373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 431412622104947507649744497 323559466578710630737308373)
        ·
          refine ⟨7583424997938530407905665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 323559466578710630737308373 7583424997938530407905665)
          ·
            refine ⟨5687568748453897805929249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7583424997938530407905665 5687568748453897805929249)
            ·
              refine ⟨4265676561340423354446937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5687568748453897805929249 4265676561340423354446937)
              ·
                refine ⟨3199257421005317515835203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4265676561340423354446937 3199257421005317515835203)
                ·
                  refine ⟨4798886131507976273752805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3199257421005317515835203 4798886131507976273752805)
                  ·
                    refine ⟨899791149657745551328651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4798886131507976273752805 899791149657745551328651)
                    ·
                      rfl

theorem cell23_5257011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 1, 4].length) (baseStart_5257011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257011 prefixEnd_5257011 := by exact prefixLift 5257011
  have htrace : WordTrace (prefixWord ++ tailWord_5257011) baseStart_5257011 baseEnd_5257011 := by
    simpa [prefixWord, tailWord_5257011, baseEnd_5257011] using wordTrace_append hprefix tailTrace_5257011
  have hstable : (prefixWord ++ tailWord_5257011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257011).length < 2 ^ (prefixWord ++ tailWord_5257011).sum := by decide
  have hdescent : baseEnd_5257011 < baseStart_5257011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257037 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_5257037 : Nat := 118140960795 + 5257037 * 2 ^ 59
def prefixEnd_5257037 : Nat := 4983230072969 + 3 ^ 40 * 5257037 * 2
def baseEnd_5257037 : Nat := 899795599823417850753611

theorem tailTrace_5257037 : CollatzResearch.WordTrace tailWord_5257037 prefixEnd_5257037 899795599823417850753611 := by
  unfold tailWord_5257037
  simp only [CollatzResearch.WordTrace]
  refine ⟨191739891455660254284777365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127826594303773502856518243 191739891455660254284777365)
  ·
    refine ⟨8987807411984074419598939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 191739891455660254284777365 8987807411984074419598939)
    ·
      refine ⟨13481711117976111629398409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8987807411984074419598939 13481711117976111629398409)
      ·
        refine ⟨10111283338482083722048807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13481711117976111629398409 10111283338482083722048807)
        ·
          refine ⟨15166925007723125583073211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10111283338482083722048807 15166925007723125583073211)
          ·
            refine ⟨22750387511584688374609817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15166925007723125583073211 22750387511584688374609817)
            ·
              refine ⟨17062790633688516280957363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22750387511584688374609817 17062790633688516280957363)
              ·
                refine ⟨25594185950532774421436045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17062790633688516280957363 25594185950532774421436045)
                ·
                  refine ⟨9597819731449790408038517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25594185950532774421436045 9597819731449790408038517)
                  ·
                    refine ⟨899795599823417850753611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9597819731449790408038517 899795599823417850753611)
                    ·
                      rfl

theorem cell23_5257037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_5257037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257037 prefixEnd_5257037 := by exact prefixLift 5257037
  have htrace : WordTrace (prefixWord ++ tailWord_5257037) baseStart_5257037 baseEnd_5257037 := by
    simpa [prefixWord, tailWord_5257037, baseEnd_5257037] using wordTrace_append hprefix tailTrace_5257037
  have hstable : (prefixWord ++ tailWord_5257037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257037).length < 2 ^ (prefixWord ++ tailWord_5257037).sum := by decide
  have hdescent : baseEnd_5257037 < baseStart_5257037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257040 : List Nat := [2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 4]
def baseStart_5257040 : Nat := 118140960795 + 5257040 * 2 ^ 59
def prefixEnd_5257040 : Nat := 4983230072969 + 3 ^ 40 * 5257040 * 2
def baseEnd_5257040 : Nat := 2699388339912217040523319

theorem tailTrace_5257040 : CollatzResearch.WordTrace tailWord_5257040 prefixEnd_5257040 2699388339912217040523319 := by
  unfold tailWord_5257040
  simp only [CollatzResearch.WordTrace]
  refine ⟨95870000437324692898568287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127826667249766257198091049 95870000437324692898568287)
  ·
    refine ⟨143805000655987039347852431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95870000437324692898568287 143805000655987039347852431)
    ·
      refine ⟨215707500983980559021778647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143805000655987039347852431 215707500983980559021778647)
      ·
        refine ⟨323561251475970838532667971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215707500983980559021778647 323561251475970838532667971)
        ·
          refine ⟨485341877213956257799001957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323561251475970838532667971 485341877213956257799001957)
          ·
            refine ⟨91001601977616798337312867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 485341877213956257799001957 91001601977616798337312867)
            ·
              refine ⟨136502402966425197505969301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91001601977616798337312867 136502402966425197505969301)
              ·
                refine ⟨6398550139051181133092311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 136502402966425197505969301 6398550139051181133092311)
                ·
                  refine ⟨9597825208576771699638467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6398550139051181133092311 9597825208576771699638467)
                  ·
                    refine ⟨14396737812865157549457701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9597825208576771699638467 14396737812865157549457701)
                    ·
                      refine ⟨2699388339912217040523319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14396737812865157549457701 2699388339912217040523319)
                      ·
                        rfl

theorem cell23_5257040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 4].length) (baseStart_5257040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257040 prefixEnd_5257040 := by exact prefixLift 5257040
  have htrace : WordTrace (prefixWord ++ tailWord_5257040) baseStart_5257040 baseEnd_5257040 := by
    simpa [prefixWord, tailWord_5257040, baseEnd_5257040] using wordTrace_append hprefix tailTrace_5257040
  have hstable : (prefixWord ++ tailWord_5257040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257040).length < 2 ^ (prefixWord ++ tailWord_5257040).sum := by decide
  have hdescent : baseEnd_5257040 < baseStart_5257040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257044 : List Nat := [2, 4, 1, 1, 3, 1, 3, 1, 2, 3, 2]
def baseStart_5257044 : Nat := 118140960795 + 5257044 * 2 ^ 59
def prefixEnd_5257044 : Nat := 4983230072969 + 3 ^ 40 * 5257044 * 2
def baseEnd_5257044 : Nat := 2699390393834835024873301

theorem tailTrace_5257044 : CollatzResearch.WordTrace tailWord_5257044 prefixEnd_5257044 2699390393834835024873301 := by
  unfold tailWord_5257044
  simp only [CollatzResearch.WordTrace]
  refine ⟨95870073383317447240141093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127826764511089929653521457 95870073383317447240141093)
  ·
    refine ⟨17975638759372021357526455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95870073383317447240141093 17975638759372021357526455)
    ·
      refine ⟨26963458139058032036289683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17975638759372021357526455 26963458139058032036289683)
      ·
        refine ⟨40445187208587048054434525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26963458139058032036289683 40445187208587048054434525)
        ·
          refine ⟨15166945203220143020412947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40445187208587048054434525 15166945203220143020412947)
          ·
            refine ⟨22750417804830214530619421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15166945203220143020412947 22750417804830214530619421)
            ·
              refine ⟨8531406676811330448982283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22750417804830214530619421 8531406676811330448982283)
              ·
                refine ⟨12797110015216995673473425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8531406676811330448982283 12797110015216995673473425)
                ·
                  refine ⟨9597832511412746755105069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12797110015216995673473425 9597832511412746755105069)
                  ·
                    refine ⟨3599187191779780033164401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9597832511412746755105069 3599187191779780033164401)
                    ·
                      refine ⟨2699390393834835024873301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3599187191779780033164401 2699390393834835024873301)
                      ·
                        rfl

theorem cell23_5257044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_5257044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257044 prefixEnd_5257044 := by exact prefixLift 5257044
  have htrace : WordTrace (prefixWord ++ tailWord_5257044) baseStart_5257044 baseEnd_5257044 := by
    simpa [prefixWord, tailWord_5257044, baseEnd_5257044] using wordTrace_append hprefix tailTrace_5257044
  have hstable : (prefixWord ++ tailWord_5257044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257044).length < 2 ^ (prefixWord ++ tailWord_5257044).sum := by decide
  have hdescent : baseEnd_5257044 < baseStart_5257044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257050 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 4, 4]
def baseStart_5257050 : Nat := 118140960795 + 5257050 * 2 ^ 59
def prefixEnd_5257050 : Nat := 4983230072969 + 3 ^ 40 * 5257050 * 2
def baseEnd_5257050 : Nat := 899797824906254000466091

theorem tailTrace_5257050 : CollatzResearch.WordTrace tailWord_5257050 prefixEnd_5257050 899797824906254000466091 := by
  unfold tailWord_5257050
  simp only [CollatzResearch.WordTrace]
  refine ⟨47935091401153289376250151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127826910403075438336667069 47935091401153289376250151)
  ·
    refine ⟨71902637101729934064375227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47935091401153289376250151 71902637101729934064375227)
    ·
      refine ⟨107853955652594901096562841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71902637101729934064375227 107853955652594901096562841)
      ·
        refine ⟨80890466739446175822422131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107853955652594901096562841 80890466739446175822422131)
        ·
          refine ⟨121335700109169263733633197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80890466739446175822422131 121335700109169263733633197)
          ·
            refine ⟨45500887540938473900112449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121335700109169263733633197 45500887540938473900112449)
            ·
              refine ⟨34125665655703855425084337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45500887540938473900112449 34125665655703855425084337)
              ·
                refine ⟨25594249241777891568813253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34125665655703855425084337 25594249241777891568813253)
                ·
                  refine ⟨4798921732833354669152485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25594249241777891568813253 4798921732833354669152485)
                  ·
                    refine ⟨899797824906254000466091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4798921732833354669152485 899797824906254000466091)
                    ·
                      rfl

theorem cell23_5257050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 4, 4].length) (baseStart_5257050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257050 prefixEnd_5257050 := by exact prefixLift 5257050
  have htrace : WordTrace (prefixWord ++ tailWord_5257050) baseStart_5257050 baseEnd_5257050 := by
    simpa [prefixWord, tailWord_5257050, baseEnd_5257050] using wordTrace_append hprefix tailTrace_5257050
  have hstable : (prefixWord ++ tailWord_5257050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257050).length < 2 ^ (prefixWord ++ tailWord_5257050).sum := by decide
  have hdescent : baseEnd_5257050 < baseStart_5257050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257057 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 5, 2, 2]
def baseStart_5257057 : Nat := 118140960795 + 5257057 * 2 ^ 59
def prefixEnd_5257057 : Nat := 4983230072969 + 3 ^ 40 * 5257057 * 2
def baseEnd_5257057 : Nat := 2699397069083343474010741

theorem tailTrace_5257057 : CollatzResearch.WordTrace tailWord_5257057 prefixEnd_5257057 2699397069083343474010741 := by
  unfold tailWord_5257057
  simp only [CollatzResearch.WordTrace]
  refine ⟨191740620915587797700505425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127827080610391865133670283 191740620915587797700505425)
  ·
    refine ⟨143805465686690848275379069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191740620915587797700505425 143805465686690848275379069)
    ·
      refine ⟨53927049632509068103267151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143805465686690848275379069 53927049632509068103267151)
      ·
        refine ⟨80890574448763602154900727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53927049632509068103267151 80890574448763602154900727)
        ·
          refine ⟨121335861673145403232351091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80890574448763602154900727 121335861673145403232351091)
          ·
            refine ⟨182003792509718104848526637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121335861673145403232351091 182003792509718104848526637)
            ·
              refine ⟨68251422191144289318197489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182003792509718104848526637 68251422191144289318197489)
              ·
                refine ⟨51188566643358216988648117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68251422191144289318197489 51188566643358216988648117)
                ·
                  refine ⟨4798928122814832842685761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51188566643358216988648117 4798928122814832842685761)
                  ·
                    refine ⟨3599196092111124632014321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4798928122814832842685761 3599196092111124632014321)
                    ·
                      refine ⟨2699397069083343474010741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3599196092111124632014321 2699397069083343474010741)
                      ·
                        rfl

theorem cell23_5257057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 2, 2].length) (baseStart_5257057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257057 prefixEnd_5257057 := by exact prefixLift 5257057
  have htrace : WordTrace (prefixWord ++ tailWord_5257057) baseStart_5257057 baseEnd_5257057 := by
    simpa [prefixWord, tailWord_5257057, baseEnd_5257057] using wordTrace_append hprefix tailTrace_5257057
  have hstable : (prefixWord ++ tailWord_5257057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257057).length < 2 ^ (prefixWord ++ tailWord_5257057).sum := by decide
  have hdescent : baseEnd_5257057 < baseStart_5257057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257063 : List Nat := [1, 1, 5, 1, 2, 1, 12]
def baseStart_5257063 : Nat := 118140960795 + 5257063 * 2 ^ 59
def prefixEnd_5257063 : Nat := 4983230072969 + 3 ^ 40 * 5257063 * 2
def baseEnd_5257063 : Nat := 33325927777373709265873

theorem tailTrace_5257063 : CollatzResearch.WordTrace tailWord_5257063 prefixEnd_5257063 33325927777373709265873 := by
  unfold tailWord_5257063
  simp only [CollatzResearch.WordTrace]
  refine ⟨191740839753566060725223843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127827226502377373816815895 191740839753566060725223843)
  ·
    refine ⟨287611259630349091087835765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191740839753566060725223843 287611259630349091087835765)
    ·
      refine ⟨26963555590345227289484603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 287611259630349091087835765 26963555590345227289484603)
      ·
        refine ⟨40445333385517840934226905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26963555590345227289484603 40445333385517840934226905)
        ·
          refine ⟨30334000039138380700670179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40445333385517840934226905 30334000039138380700670179)
          ·
            refine ⟨45501000058707571051005269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30334000039138380700670179 45501000058707571051005269)
            ·
              refine ⟨33325927777373709265873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 45501000058707571051005269 33325927777373709265873)
              ·
                rfl

theorem cell23_5257063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 12].length) (baseStart_5257063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257063 prefixEnd_5257063 := by exact prefixLift 5257063
  have htrace : WordTrace (prefixWord ++ tailWord_5257063) baseStart_5257063 baseEnd_5257063 := by
    simpa [prefixWord, tailWord_5257063, baseEnd_5257063] using wordTrace_append hprefix tailTrace_5257063
  have hstable : (prefixWord ++ tailWord_5257063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257063).length < 2 ^ (prefixWord ++ tailWord_5257063).sum := by decide
  have hdescent : baseEnd_5257063 < baseStart_5257063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257108 : List Nat := [2, 4, 2, 1, 1, 2, 3, 3, 1, 2, 2]
def baseStart_5257108 : Nat := 118140960795 + 5257108 * 2 ^ 59
def prefixEnd_5257108 : Nat := 4983230072969 + 3 ^ 40 * 5257108 * 2
def baseEnd_5257108 : Nat := 2699423256596722774473007

theorem tailTrace_5257108 : CollatzResearch.WordTrace tailWord_5257108 prefixEnd_5257108 2699423256596722774473007 := by
  unfold tailWord_5257108
  simp only [CollatzResearch.WordTrace]
  refine ⟨95871240519201516705305989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127828320692268688940407985 95871240519201516705305989)
  ·
    refine ⟨17975857597350284382244873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95871240519201516705305989 17975857597350284382244873)
    ·
      refine ⟨13481893198012713286683655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17975857597350284382244873 13481893198012713286683655)
      ·
        refine ⟨20222839797019069930025483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13481893198012713286683655 20222839797019069930025483)
        ·
          refine ⟨30334259695528604895038225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20222839797019069930025483 30334259695528604895038225)
          ·
            refine ⟨22750694771646453671278669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30334259695528604895038225 22750694771646453671278669)
            ·
              refine ⟨8531510539367420126729501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22750694771646453671278669 8531510539367420126729501)
              ·
                refine ⟨3199316452262782547523563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8531510539367420126729501 3199316452262782547523563)
                ·
                  refine ⟨4798974678394173821285345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3199316452262782547523563 4798974678394173821285345)
                  ·
                    refine ⟨3599231008795630365964009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4798974678394173821285345 3599231008795630365964009)
                    ·
                      refine ⟨2699423256596722774473007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3599231008795630365964009 2699423256596722774473007)
                      ·
                        rfl

theorem cell23_5257108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_5257108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257108 prefixEnd_5257108 := by exact prefixLift 5257108
  have htrace : WordTrace (prefixWord ++ tailWord_5257108) baseStart_5257108 baseEnd_5257108 := by
    simpa [prefixWord, tailWord_5257108, baseEnd_5257108] using wordTrace_append hprefix tailTrace_5257108
  have hstable : (prefixWord ++ tailWord_5257108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257108).length < 2 ^ (prefixWord ++ tailWord_5257108).sum := by decide
  have hdescent : baseEnd_5257108 < baseStart_5257108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257141 : List Nat := [1, 3, 3, 2, 1, 2, 4, 1, 2, 1, 3]
def baseStart_5257141 : Nat := 118140960795 + 5257141 * 2 ^ 59
def prefixEnd_5257141 : Nat := 4983230072969 + 3 ^ 40 * 5257141 * 2
def baseEnd_5257141 : Nat := 2699440201458321145360355

theorem tailTrace_5257141 : CollatzResearch.WordTrace tailWord_5257141 prefixEnd_5257141 2699440201458321145360355 := by
  unfold tailWord_5257141
  simp only [CollatzResearch.WordTrace]
  refine ⟨191743684647283480046563277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127829123098188986697708851 191743684647283480046563277)
  ·
    refine ⟨71903881742731305017461229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191743684647283480046563277 71903881742731305017461229)
    ·
      refine ⟨26963955653524239381547961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71903881742731305017461229 26963955653524239381547961)
      ·
        refine ⟨20222966740143179536160971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26963955653524239381547961 20222966740143179536160971)
        ·
          refine ⟨30334450110214769304241457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20222966740143179536160971 30334450110214769304241457)
          ·
            refine ⟨22750837582661076978181093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30334450110214769304241457 22750837582661076978181093)
            ·
              refine ⟨4265782046748951933408955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22750837582661076978181093 4265782046748951933408955)
              ·
                refine ⟨6398673070123427900113433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4265782046748951933408955 6398673070123427900113433)
                ·
                  refine ⟨4799004802592570925085075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6398673070123427900113433 4799004802592570925085075)
                  ·
                    refine ⟨7198507203888856387627613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4799004802592570925085075 7198507203888856387627613)
                    ·
                      refine ⟨2699440201458321145360355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7198507203888856387627613 2699440201458321145360355)
                      ·
                        rfl

theorem cell23_5257141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_5257141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257141 prefixEnd_5257141 := by exact prefixLift 5257141
  have htrace : WordTrace (prefixWord ++ tailWord_5257141) baseStart_5257141 baseEnd_5257141 := by
    simpa [prefixWord, tailWord_5257141, baseEnd_5257141] using wordTrace_append hprefix tailTrace_5257141
  have hstable : (prefixWord ++ tailWord_5257141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257141).length < 2 ^ (prefixWord ++ tailWord_5257141).sum := by decide
  have hdescent : baseEnd_5257141 < baseStart_5257141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257164 : List Nat := [2, 2, 1, 4, 1, 3, 1, 2, 1, 4, 2]
def baseStart_5257164 : Nat := 118140960795 + 5257164 * 2 ^ 59
def prefixEnd_5257164 : Nat := 4983230072969 + 3 ^ 40 * 5257164 * 2
def baseEnd_5257164 : Nat := 2699452011513374555372749

theorem tailTrace_5257164 : CollatzResearch.WordTrace tailWord_5257164 prefixEnd_5257164 2699452011513374555372749 := by
  unfold tailWord_5257164
  simp only [CollatzResearch.WordTrace]
  refine ⟨95872261763100077487325273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127829682350800103316433697 95872261763100077487325273)
  ·
    refine ⟨71904196322325058115493955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95872261763100077487325273 71904196322325058115493955)
    ·
      refine ⟨107856294483487587173240933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71904196322325058115493955 107856294483487587173240933)
      ·
        refine ⟨20223055215653922594982675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107856294483487587173240933 20223055215653922594982675)
        ·
          refine ⟨30334582823480883892474013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20223055215653922594982675 30334582823480883892474013)
          ·
            refine ⟨11375468558805331459677755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30334582823480883892474013 11375468558805331459677755)
            ·
              refine ⟨17063202838207997189516633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11375468558805331459677755 17063202838207997189516633)
              ·
                refine ⟨12797402128655997892137475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17063202838207997189516633 12797402128655997892137475)
                ·
                  refine ⟨19196103192983996838206213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12797402128655997892137475 19196103192983996838206213)
                  ·
                    refine ⟨3599269348684499407163665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19196103192983996838206213 3599269348684499407163665)
                    ·
                      refine ⟨2699452011513374555372749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3599269348684499407163665 2699452011513374555372749)
                      ·
                        rfl

theorem cell23_5257164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_5257164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257164 prefixEnd_5257164 := by exact prefixLift 5257164
  have htrace : WordTrace (prefixWord ++ tailWord_5257164) baseStart_5257164 baseEnd_5257164 := by
    simpa [prefixWord, tailWord_5257164, baseEnd_5257164] using wordTrace_append hprefix tailTrace_5257164
  have hstable : (prefixWord ++ tailWord_5257164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257164).length < 2 ^ (prefixWord ++ tailWord_5257164).sum := by decide
  have hdescent : baseEnd_5257164 < baseStart_5257164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257200 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 4, 5]
def baseStart_5257200 : Nat := 118140960795 + 5257200 * 2 ^ 59
def prefixEnd_5257200 : Nat := 4983230072969 + 3 ^ 40 * 5257200 * 2
def baseEnd_5257200 : Nat := 899823498938978804840861

theorem tailTrace_5257200 : CollatzResearch.WordTrace tailWord_5257200 prefixEnd_5257200 899823498938978804840861 := by
  unfold tailWord_5257200
  simp only [CollatzResearch.WordTrace]
  refine ⟨95872918277034866561480527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127830557702713155415307369 95872918277034866561480527)
  ·
    refine ⟨143809377415552299842220791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95872918277034866561480527 143809377415552299842220791)
    ·
      refine ⟨215714066123328449763331187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143809377415552299842220791 215714066123328449763331187)
      ·
        refine ⟨323571099184992674644996781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215714066123328449763331187 323571099184992674644996781)
        ·
          refine ⟨121339162194372252991873793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 323571099184992674644996781 121339162194372252991873793)
          ·
            refine ⟨91004371645779189743905345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121339162194372252991873793 91004371645779189743905345)
            ·
              refine ⟨68253278734334392307929009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91004371645779189743905345 68253278734334392307929009)
              ·
                refine ⟨51189959050750794230946757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68253278734334392307929009 51189959050750794230946757)
                ·
                  refine ⟨9598117322015773918302517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51189959050750794230946757 9598117322015773918302517)
                  ·
                    refine ⟨899823498938978804840861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9598117322015773918302517 899823498938978804840861)
                    ·
                      rfl

theorem cell23_5257200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 4, 5].length) (baseStart_5257200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257200 prefixEnd_5257200 := by exact prefixLift 5257200
  have htrace : WordTrace (prefixWord ++ tailWord_5257200) baseStart_5257200 baseEnd_5257200 := by
    simpa [prefixWord, tailWord_5257200, baseEnd_5257200] using wordTrace_append hprefix tailTrace_5257200
  have hstable : (prefixWord ++ tailWord_5257200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257200).length < 2 ^ (prefixWord ++ tailWord_5257200).sum := by decide
  have hdescent : baseEnd_5257200 < baseStart_5257200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257298 : List Nat := [3, 2, 2, 1, 5, 1, 1, 1, 3, 4]
def baseStart_5257298 : Nat := 118140960795 + 5257298 * 2 ^ 59
def prefixEnd_5257298 : Nat := 4983230072969 + 3 ^ 40 * 5257298 * 2
def baseEnd_5257298 : Nat := 899840272640359010365711

theorem tailTrace_5257298 : CollatzResearch.WordTrace tailWord_5257298 prefixEnd_5257298 899840272640359010365711 := by
  unfold tailWord_5257298
  simp only [CollatzResearch.WordTrace]
  refine ⟨47937352726928673965007137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127832940605143130573352365 47937352726928673965007137)
  ·
    refine ⟨35953014545196505473755353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47937352726928673965007137 35953014545196505473755353)
    ·
      refine ⟨26964760908897379105316515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35953014545196505473755353 26964760908897379105316515)
      ·
        refine ⟨40447141363346068657974773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26964760908897379105316515 40447141363346068657974773)
        ·
          refine ⟨3791919502813693936685135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40447141363346068657974773 3791919502813693936685135)
          ·
            refine ⟨5687879254220540905027703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3791919502813693936685135 5687879254220540905027703)
            ·
              refine ⟨8531818881330811357541555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5687879254220540905027703 8531818881330811357541555)
              ·
                refine ⟨12797728321996217036312333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8531818881330811357541555 12797728321996217036312333)
                ·
                  refine ⟨4799148120748581388617125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12797728321996217036312333 4799148120748581388617125)
                  ·
                    refine ⟨899840272640359010365711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4799148120748581388617125 899840272640359010365711)
                    ·
                      rfl

theorem cell23_5257298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_5257298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257298 prefixEnd_5257298 := by exact prefixLift 5257298
  have htrace : WordTrace (prefixWord ++ tailWord_5257298) baseStart_5257298 baseEnd_5257298 := by
    simpa [prefixWord, tailWord_5257298, baseEnd_5257298] using wordTrace_append hprefix tailTrace_5257298
  have hstable : (prefixWord ++ tailWord_5257298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257298).length < 2 ^ (prefixWord ++ tailWord_5257298).sum := by decide
  have hdescent : baseEnd_5257298 < baseStart_5257298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257324 : List Nat := [2, 2, 1, 1, 3, 3, 3, 2, 1, 5]
def baseStart_5257324 : Nat := 118140960795 + 5257324 * 2 ^ 59
def prefixEnd_5257324 : Nat := 4983230072969 + 3 ^ 40 * 5257324 * 2
def baseEnd_5257324 : Nat := 899844722806031309790671

theorem tailTrace_5257324 : CollatzResearch.WordTrace tailWord_5257324 prefixEnd_5257324 899844722806031309790671 := by
  unfold tailWord_5257324
  simp only [CollatzResearch.WordTrace]
  refine ⟨95875179602810251150237513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127833572803747001533650017 95875179602810251150237513)
  ·
    refine ⟨71906384702107688362678135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95875179602810251150237513 71906384702107688362678135)
    ·
      refine ⟨107859577053161532544017203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71906384702107688362678135 107859577053161532544017203)
      ·
        refine ⟨161789365579742298816025805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107859577053161532544017203 161789365579742298816025805)
        ·
          refine ⟨60671012092403362056009677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161789365579742298816025805 60671012092403362056009677)
          ·
            refine ⟨22751629534651260771003629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60671012092403362056009677 22751629534651260771003629)
            ·
              refine ⟨8531861075494222789126361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22751629534651260771003629 8531861075494222789126361)
              ·
                refine ⟨6398895806620667091844771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8531861075494222789126361 6398895806620667091844771)
                ·
                  refine ⟨9598343709931000637767157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6398895806620667091844771 9598343709931000637767157)
                  ·
                    refine ⟨899844722806031309790671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9598343709931000637767157 899844722806031309790671)
                    ·
                      rfl

theorem cell23_5257324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 5].length) (baseStart_5257324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257324 prefixEnd_5257324 := by exact prefixLift 5257324
  have htrace : WordTrace (prefixWord ++ tailWord_5257324) baseStart_5257324 baseEnd_5257324 := by
    simpa [prefixWord, tailWord_5257324, baseEnd_5257324] using wordTrace_append hprefix tailTrace_5257324
  have hstable : (prefixWord ++ tailWord_5257324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257324).length < 2 ^ (prefixWord ++ tailWord_5257324).sum := by decide
  have hdescent : baseEnd_5257324 < baseStart_5257324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257337 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 3, 6]
def baseStart_5257337 : Nat := 118140960795 + 5257337 * 2 ^ 59
def prefixEnd_5257337 : Nat := 4983230072969 + 3 ^ 40 * 5257337 * 2
def baseEnd_5257337 : Nat := 899846947888867459503151

theorem tailTrace_5257337 : CollatzResearch.WordTrace tailWord_5257337 prefixEnd_5257337 899846947888867459503151 := by
  unfold tailWord_5257337
  simp only [CollatzResearch.WordTrace]
  refine ⟨191750833354573405520698265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127833888903048937013798843 191750833354573405520698265)
  ·
    refine ⟨143813125015930054140523699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191750833354573405520698265 143813125015930054140523699)
    ·
      refine ⟨215719687523895081210785549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143813125015930054140523699 215719687523895081210785549)
      ·
        refine ⟨80894882821460655454044581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215719687523895081210785549 80894882821460655454044581)
        ·
          refine ⟨15167790529023872897633359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80894882821460655454044581 15167790529023872897633359)
          ·
            refine ⟨22751685793535809346450039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15167790529023872897633359 22751685793535809346450039)
            ·
              refine ⟨34127528690303714019675059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22751685793535809346450039 34127528690303714019675059)
              ·
                refine ⟨51191293035455571029512589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34127528690303714019675059 51191293035455571029512589)
                ·
                  refine ⟨19196734888295839136067221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51191293035455571029512589 19196734888295839136067221)
                  ·
                    refine ⟨899846947888867459503151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19196734888295839136067221 899846947888867459503151)
                    ·
                      rfl

theorem cell23_5257337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 6].length) (baseStart_5257337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257337 prefixEnd_5257337 := by exact prefixLift 5257337
  have htrace : WordTrace (prefixWord ++ tailWord_5257337) baseStart_5257337 baseEnd_5257337 := by
    simpa [prefixWord, tailWord_5257337, baseEnd_5257337] using wordTrace_append hprefix tailTrace_5257337
  have hstable : (prefixWord ++ tailWord_5257337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257337).length < 2 ^ (prefixWord ++ tailWord_5257337).sum := by decide
  have hdescent : baseEnd_5257337 < baseStart_5257337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257341 : List Nat := [1, 4, 1, 1, 3, 3, 3, 1, 1, 5]
def baseStart_5257341 : Nat := 118140960795 + 5257341 * 2 ^ 59
def prefixEnd_5257341 : Nat := 4983230072969 + 3 ^ 40 * 5257341 * 2
def baseEnd_5257341 : Nat := 899847632529740120953145

theorem tailTrace_5257341 : CollatzResearch.WordTrace tailWord_5257341 prefixEnd_5257341 899847632529740120953145 := by
  unfold tailWord_5257341
  simp only [CollatzResearch.WordTrace]
  refine ⟨191750979246558914203843877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127833986164372609469229251 191750979246558914203843877)
  ·
    refine ⟨35953308608729796413220727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191750979246558914203843877 35953308608729796413220727)
    ·
      refine ⟨53929962913094694619831091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35953308608729796413220727 53929962913094694619831091)
      ·
        refine ⟨80894944369642041929746637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53929962913094694619831091 80894944369642041929746637)
        ·
          refine ⟨30335604138615765723654989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80894944369642041929746637 30335604138615765723654989)
          ·
            refine ⟨11375851551980912146370621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30335604138615765723654989 11375851551980912146370621)
            ·
              refine ⟨4265944331992842054888983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11375851551980912146370621 4265944331992842054888983)
              ·
                refine ⟨6398916497989263082333475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4265944331992842054888983 6398916497989263082333475)
                ·
                  refine ⟨9598374746983894623500213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6398916497989263082333475 9598374746983894623500213)
                  ·
                    refine ⟨899847632529740120953145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9598374746983894623500213 899847632529740120953145)
                    ·
                      rfl

theorem cell23_5257341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_5257341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257341 prefixEnd_5257341 := by exact prefixLift 5257341
  have htrace : WordTrace (prefixWord ++ tailWord_5257341) baseStart_5257341 baseEnd_5257341 := by
    simpa [prefixWord, tailWord_5257341, baseEnd_5257341] using wordTrace_append hprefix tailTrace_5257341
  have hstable : (prefixWord ++ tailWord_5257341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257341).length < 2 ^ (prefixWord ++ tailWord_5257341).sum := by decide
  have hdescent : baseEnd_5257341 < baseStart_5257341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257378 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 5, 2, 2]
def baseStart_5257378 : Nat := 118140960795 + 5257378 * 2 ^ 59
def prefixEnd_5257378 : Nat := 4983230072969 + 3 ^ 40 * 5257378 * 2
def baseEnd_5257378 : Nat := 2699561896373436718096765

theorem tailTrace_5257378 : CollatzResearch.WordTrace tailWord_5257378 prefixEnd_5257378 2699561896373436718096765 := by
  unfold tailWord_5257378
  simp only [CollatzResearch.WordTrace]
  refine ⟨47938082186856217380735197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127834885831616579681960525 47938082186856217380735197)
  ·
    refine ⟨17976780820071081517775699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47938082186856217380735197 17976780820071081517775699)
    ·
      refine ⟨26965171230106622276663549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17976780820071081517775699 26965171230106622276663549)
      ·
        refine ⟨10111939211289983353748831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26965171230106622276663549 10111939211289983353748831)
        ·
          refine ⟨15167908816934975030623247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10111939211289983353748831 15167908816934975030623247)
          ·
            refine ⟨22751863225402462545934871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15167908816934975030623247 22751863225402462545934871)
            ·
              refine ⟨34127794838103693818902307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22751863225402462545934871 34127794838103693818902307)
              ·
                refine ⟨51191692257155540728353461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34127794838103693818902307 51191692257155540728353461)
                ·
                  refine ⟨4799221149108331943283137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51191692257155540728353461 4799221149108331943283137)
                  ·
                    refine ⟨3599415861831248957462353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4799221149108331943283137 3599415861831248957462353)
                    ·
                      refine ⟨2699561896373436718096765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3599415861831248957462353 2699561896373436718096765)
                      ·
                        rfl

theorem cell23_5257378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_5257378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257378 prefixEnd_5257378 := by exact prefixLift 5257378
  have htrace : WordTrace (prefixWord ++ tailWord_5257378) baseStart_5257378 baseEnd_5257378 := by
    simpa [prefixWord, tailWord_5257378, baseEnd_5257378] using wordTrace_append hprefix tailTrace_5257378
  have hstable : (prefixWord ++ tailWord_5257378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257378).length < 2 ^ (prefixWord ++ tailWord_5257378).sum := by decide
  have hdescent : baseEnd_5257378 < baseStart_5257378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257394 : List Nat := [3, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3]
def baseStart_5257394 : Nat := 118140960795 + 5257394 * 2 ^ 59
def prefixEnd_5257394 : Nat := 4983230072969 + 3 ^ 40 * 5257394 * 2
def baseEnd_5257394 : Nat := 2699570112063908655496691

theorem tailTrace_5257394 : CollatzResearch.WordTrace tailWord_5257394 prefixEnd_5257394 2699570112063908655496691 := by
  unfold tailWord_5257394
  simp only [CollatzResearch.WordTrace]
  refine ⟨47938228078841726063880809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127835274876911269503682157 47938228078841726063880809)
  ·
    refine ⟨35953671059131294547910607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47938228078841726063880809 35953671059131294547910607)
    ·
      refine ⟨53930506588696941821865911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35953671059131294547910607 53930506588696941821865911)
      ·
        refine ⟨80895759883045412732798867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53930506588696941821865911 80895759883045412732798867)
        ·
          refine ⟨121343639824568119099198301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80895759883045412732798867 121343639824568119099198301)
          ·
            refine ⟨45503864934213044662199363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121343639824568119099198301 45503864934213044662199363)
            ·
              refine ⟨68255797401319566993299045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45503864934213044662199363 68255797401319566993299045)
              ·
                refine ⟨12797962012747418811243571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68255797401319566993299045 12797962012747418811243571)
                ·
                  refine ⟨19196943019121128216865357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12797962012747418811243571 19196943019121128216865357)
                  ·
                    refine ⟨7198853632170423081324509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19196943019121128216865357 7198853632170423081324509)
                    ·
                      refine ⟨2699570112063908655496691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7198853632170423081324509 2699570112063908655496691)
                      ·
                        rfl

theorem cell23_5257394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_5257394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257394 prefixEnd_5257394 := by exact prefixLift 5257394
  have htrace : WordTrace (prefixWord ++ tailWord_5257394) baseStart_5257394 baseEnd_5257394 := by
    simpa [prefixWord, tailWord_5257394, baseEnd_5257394] using wordTrace_append hprefix tailTrace_5257394
  have hstable : (prefixWord ++ tailWord_5257394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257394).length < 2 ^ (prefixWord ++ tailWord_5257394).sum := by decide
  have hdescent : baseEnd_5257394 < baseStart_5257394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257417 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 2, 3, 4]
def baseStart_5257417 : Nat := 118140960795 + 5257417 * 2 ^ 59
def prefixEnd_5257417 : Nat := 4983230072969 + 3 ^ 40 * 5257417 * 2
def baseEnd_5257417 : Nat := 2699581922118962065509085

theorem tailTrace_5257417 : CollatzResearch.WordTrace tailWord_5257417 prefixEnd_5257417 2699581922118962065509085 := by
  unfold tailWord_5257417
  simp only [CollatzResearch.WordTrace]
  refine ⟨191753751194283579183610505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127835834129522386122407003 191753751194283579183610505)
  ·
    refine ⟨143815313395712684387707879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191753751194283579183610505 143815313395712684387707879)
    ·
      refine ⟨215722970093569026581561819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143815313395712684387707879 215722970093569026581561819)
      ·
        refine ⟨323584455140353539872342729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215722970093569026581561819 323584455140353539872342729)
        ·
          refine ⟨242688341355265154904257047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323584455140353539872342729 242688341355265154904257047)
          ·
            refine ⟨364032512032897732356385571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242688341355265154904257047 364032512032897732356385571)
            ·
              refine ⟨546048768049346598534578357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364032512032897732356385571 546048768049346598534578357)
              ·
                refine ⟨51192072004626243612616721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 546048768049346598534578357 51192072004626243612616721)
                ·
                  refine ⟨38394054003469682709462541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51192072004626243612616721 38394054003469682709462541)
                  ·
                    refine ⟨14397770251301131016048453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38394054003469682709462541 14397770251301131016048453)
                    ·
                      refine ⟨2699581922118962065509085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14397770251301131016048453 2699581922118962065509085)
                      ·
                        rfl

theorem cell23_5257417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 3, 4].length) (baseStart_5257417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257417 prefixEnd_5257417 := by exact prefixLift 5257417
  have htrace : WordTrace (prefixWord ++ tailWord_5257417) baseStart_5257417 baseEnd_5257417 := by
    simpa [prefixWord, tailWord_5257417, baseEnd_5257417] using wordTrace_append hprefix tailTrace_5257417
  have hstable : (prefixWord ++ tailWord_5257417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257417).length < 2 ^ (prefixWord ++ tailWord_5257417).sum := by decide
  have hdescent : baseEnd_5257417 < baseStart_5257417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257451 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 6, 2, 2]
def baseStart_5257451 : Nat := 118140960795 + 5257451 * 2 ^ 59
def prefixEnd_5257451 : Nat := 4983230072969 + 3 ^ 40 * 5257451 * 2
def baseEnd_5257451 : Nat := 2699599380461214932483929

theorem tailTrace_5257451 : CollatzResearch.WordTrace tailWord_5257451 prefixEnd_5257451 2699599380461214932483929 := by
  unfold tailWord_5257451
  simp only [CollatzResearch.WordTrace]
  refine ⟨191754991276160402990348207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127836660850773601993565471 191754991276160402990348207)
  ·
    refine ⟨287632486914240604485522311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191754991276160402990348207 287632486914240604485522311)
    ·
      refine ⟨431448730371360906728283467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287632486914240604485522311 431448730371360906728283467)
      ·
        refine ⟨647173095557041360092425201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431448730371360906728283467 647173095557041360092425201)
        ·
          refine ⟨485379821667781020069318901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 647173095557041360092425201 485379821667781020069318901)
          ·
            refine ⟨45504358281354470631498647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 485379821667781020069318901 45504358281354470631498647)
            ·
              refine ⟨68256537422031705947247971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45504358281354470631498647 68256537422031705947247971)
              ·
                refine ⟨102384806133047558920871957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68256537422031705947247971 102384806133047558920871957)
                ·
                  refine ⟨4799287787486604324415873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 102384806133047558920871957 4799287787486604324415873)
                  ·
                    refine ⟨3599465840614953243311905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4799287787486604324415873 3599465840614953243311905)
                    ·
                      refine ⟨2699599380461214932483929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3599465840614953243311905 2699599380461214932483929)
                      ·
                        rfl

theorem cell23_5257451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 2, 2].length) (baseStart_5257451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257451 prefixEnd_5257451 := by exact prefixLift 5257451
  have htrace : WordTrace (prefixWord ++ tailWord_5257451) baseStart_5257451 baseEnd_5257451 := by
    simpa [prefixWord, tailWord_5257451, baseEnd_5257451] using wordTrace_append hprefix tailTrace_5257451
  have hstable : (prefixWord ++ tailWord_5257451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257451).length < 2 ^ (prefixWord ++ tailWord_5257451).sum := by decide
  have hdescent : baseEnd_5257451 < baseStart_5257451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257454 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 1, 6, 3]
def baseStart_5257454 : Nat := 118140960795 + 5257454 * 2 ^ 59
def prefixEnd_5257454 : Nat := 4983230072969 + 3 ^ 40 * 5257454 * 2
def baseEnd_5257454 : Nat := 2699600920903178420746415

theorem tailTrace_5257454 : CollatzResearch.WordTrace tailWord_5257454 prefixEnd_5257454 2699600920903178420746415 := by
  unfold tailWord_5257454
  simp only [CollatzResearch.WordTrace]
  refine ⟨23969387586893691812838427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127836733796766356335138277 23969387586893691812838427)
  ·
    refine ⟨35954081380340537719257641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23969387586893691812838427 35954081380340537719257641)
    ·
      refine ⟨26965561035255403289443231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35954081380340537719257641 26965561035255403289443231)
      ·
        refine ⟨40448341552883104934164847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26965561035255403289443231 40448341552883104934164847)
        ·
          refine ⟨60672512329324657401247271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40448341552883104934164847 60672512329324657401247271)
          ·
            refine ⟨91008768493986986101870907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60672512329324657401247271 91008768493986986101870907)
            ·
              refine ⟨136513152740980479152806361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91008768493986986101870907 136513152740980479152806361)
              ·
                refine ⟨102384864555735359364604771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136513152740980479152806361 102384864555735359364604771)
                ·
                  refine ⟨153577296833603039046907157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102384864555735359364604771 153577296833603039046907157)
                  ·
                    refine ⟨7198935789075142455323773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 153577296833603039046907157 7198935789075142455323773)
                    ·
                      refine ⟨2699600920903178420746415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7198935789075142455323773 2699600920903178420746415)
                      ·
                        rfl

theorem cell23_5257454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_5257454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257454 prefixEnd_5257454 := by exact prefixLift 5257454
  have htrace : WordTrace (prefixWord ++ tailWord_5257454) baseStart_5257454 baseEnd_5257454 := by
    simpa [prefixWord, tailWord_5257454, baseEnd_5257454] using wordTrace_append hprefix tailTrace_5257454
  have hstable : (prefixWord ++ tailWord_5257454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257454).length < 2 ^ (prefixWord ++ tailWord_5257454).sum := by decide
  have hdescent : baseEnd_5257454 < baseStart_5257454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257457 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 9]
def baseStart_5257457 : Nat := 118140960795 + 5257457 * 2 ^ 59
def prefixEnd_5257457 : Nat := 4983230072969 + 3 ^ 40 * 5257457 * 2
def baseEnd_5257457 : Nat := 299955829038349101000989

theorem tailTrace_5257457 : CollatzResearch.WordTrace tailWord_5257457 prefixEnd_5257457 299955829038349101000989 := by
  unfold tailWord_5257457
  simp only [CollatzResearch.WordTrace]
  refine ⟨191755210114138666015066625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127836806742759110676711083 191755210114138666015066625)
  ·
    refine ⟨143816407585603999511299969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191755210114138666015066625 143816407585603999511299969)
    ·
      refine ⟨107862305689202999633474977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143816407585603999511299969 107862305689202999633474977)
      ·
        refine ⟨80896729266902249725106233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107862305689202999633474977 80896729266902249725106233)
        ·
          refine ⟨60672546950176687293829675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80896729266902249725106233 60672546950176687293829675)
          ·
            refine ⟨91008820425265030940744513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60672546950176687293829675 91008820425265030940744513)
            ·
              refine ⟨68256615318948773205558385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91008820425265030940744513 68256615318948773205558385)
              ·
                refine ⟨51192461489211579904168789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68256615318948773205558385 51192461489211579904168789)
                ·
                  refine ⟨299955829038349101000989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51192461489211579904168789 299955829038349101000989)
                  ·
                    rfl

theorem cell23_5257457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 9].length) (baseStart_5257457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257457 prefixEnd_5257457 := by exact prefixLift 5257457
  have htrace : WordTrace (prefixWord ++ tailWord_5257457) baseStart_5257457 baseEnd_5257457 := by
    simpa [prefixWord, tailWord_5257457, baseEnd_5257457] using wordTrace_append hprefix tailTrace_5257457
  have hstable : (prefixWord ++ tailWord_5257457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257457).length < 2 ^ (prefixWord ++ tailWord_5257457).sum := by decide
  have hdescent : baseEnd_5257457 < baseStart_5257457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257468 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 4, 2, 2]
def baseStart_5257468 : Nat := 118140960795 + 5257468 * 2 ^ 59
def prefixEnd_5257468 : Nat := 4983230072969 + 3 ^ 40 * 5257468 * 2
def baseEnd_5257468 : Nat := 2699608109632341365971351

theorem tailTrace_5257468 : CollatzResearch.WordTrace tailWord_5257468 prefixEnd_5257468 2699608109632341365971351 := by
  unfold tailWord_5257468
  simp only [CollatzResearch.WordTrace]
  refine ⟨95877805658549407446858529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127837074211399209929144705 95877805658549407446858529)
  ·
    refine ⟨71908354243912055585143897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95877805658549407446858529 71908354243912055585143897)
    ·
      refine ⟨53931265682934041688857923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71908354243912055585143897 53931265682934041688857923)
      ·
        refine ⟨80896898524401062533286885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53931265682934041688857923 80896898524401062533286885)
        ·
          refine ⟨15168168473325199224991291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80896898524401062533286885 15168168473325199224991291)
          ·
            refine ⟨22752252709987798837486937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15168168473325199224991291 22752252709987798837486937)
            ·
              refine ⟨17064189532490849128115203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22752252709987798837486937 17064189532490849128115203)
              ·
                refine ⟨25596284298736273692172805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17064189532490849128115203 25596284298736273692172805)
                ·
                  refine ⟨4799303306013051317282401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25596284298736273692172805 4799303306013051317282401)
                  ·
                    refine ⟨3599477479509788487961801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4799303306013051317282401 3599477479509788487961801)
                    ·
                      refine ⟨2699608109632341365971351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3599477479509788487961801 2699608109632341365971351)
                      ·
                        rfl

theorem cell23_5257468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 4, 2, 2].length) (baseStart_5257468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257468 prefixEnd_5257468 := by exact prefixLift 5257468
  have htrace : WordTrace (prefixWord ++ tailWord_5257468) baseStart_5257468 baseEnd_5257468 := by
    simpa [prefixWord, tailWord_5257468, baseEnd_5257468] using wordTrace_append hprefix tailTrace_5257468
  have hstable : (prefixWord ++ tailWord_5257468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257468).length < 2 ^ (prefixWord ++ tailWord_5257468).sum := by decide
  have hdescent : baseEnd_5257468 < baseStart_5257468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257477 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 2, 1, 8]
def baseStart_5257477 : Nat := 118140960795 + 5257477 * 2 ^ 59
def prefixEnd_5257477 : Nat := 4983230072969 + 3 ^ 40 * 5257477 * 2
def baseEnd_5257477 : Nat := 2699612730958231830758809

theorem tailTrace_5257477 : CollatzResearch.WordTrace tailWord_5257477 prefixEnd_5257477 2699612730958231830758809 := by
  unfold tailWord_5257477
  simp only [CollatzResearch.WordTrace]
  refine ⟨191755939574066209430794685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127837293049377472953863123 191755939574066209430794685)
  ·
    refine ⟨71908477340274828536548007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191755939574066209430794685 71908477340274828536548007)
    ·
      refine ⟨107862716010412242804822011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71908477340274828536548007 107862716010412242804822011)
      ·
        refine ⟨161794074015618364207233017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107862716010412242804822011 161794074015618364207233017)
        ·
          refine ⟨121345555511713773155424763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161794074015618364207233017 121345555511713773155424763)
          ·
            refine ⟨182018333267570659733137145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121345555511713773155424763 182018333267570659733137145)
            ·
              refine ⟨136513749950677994799852859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182018333267570659733137145 136513749950677994799852859)
              ·
                refine ⟨204770624926016992199779289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136513749950677994799852859 204770624926016992199779289)
                ·
                  refine ⟨153577968694512744149834467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204770624926016992199779289 153577968694512744149834467)
                  ·
                    refine ⟨230366953041769116224751701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 153577968694512744149834467 230366953041769116224751701)
                    ·
                      refine ⟨2699612730958231830758809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 230366953041769116224751701 2699612730958231830758809)
                      ·
                        rfl

theorem cell23_5257477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_5257477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257477 prefixEnd_5257477 := by exact prefixLift 5257477
  have htrace : WordTrace (prefixWord ++ tailWord_5257477) baseStart_5257477 baseEnd_5257477 := by
    simpa [prefixWord, tailWord_5257477, baseEnd_5257477] using wordTrace_append hprefix tailTrace_5257477
  have hstable : (prefixWord ++ tailWord_5257477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257477).length < 2 ^ (prefixWord ++ tailWord_5257477).sum := by decide
  have hdescent : baseEnd_5257477 < baseStart_5257477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257479 : List Nat := [1, 1, 4, 5, 2, 1, 2, 1, 2, 1, 3]
def baseStart_5257479 : Nat := 118140960795 + 5257479 * 2 ^ 59
def prefixEnd_5257479 : Nat := 4983230072969 + 3 ^ 40 * 5257479 * 2
def baseEnd_5257479 : Nat := 2699613757919540822933801

theorem tailTrace_5257479 : CollatzResearch.WordTrace tailWord_5257479 prefixEnd_5257479 2699613757919540822933801 := by
  unfold tailWord_5257479
  simp only [CollatzResearch.WordTrace]
  refine ⟨191756012520058963772367491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127837341680039309181578327 191756012520058963772367491)
  ·
    refine ⟨287634018780088445658551237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191756012520058963772367491 287634018780088445658551237)
    ·
      refine ⟨53931378521266583560978357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 287634018780088445658551237 53931378521266583560978357)
      ·
        refine ⟨5056066736368742208841721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53931378521266583560978357 5056066736368742208841721)
        ·
          refine ⟨3792050052276556656631291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5056066736368742208841721 3792050052276556656631291)
          ·
            refine ⟨5688075078414834984946937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3792050052276556656631291 5688075078414834984946937)
            ·
              refine ⟨4266056308811126238710203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5688075078414834984946937 4266056308811126238710203)
              ·
                refine ⟨6399084463216689358065305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4266056308811126238710203 6399084463216689358065305)
                ·
                  refine ⟨4799313347412517018548979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6399084463216689358065305 4799313347412517018548979)
                  ·
                    refine ⟨7198970021118775527823469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4799313347412517018548979 7198970021118775527823469)
                    ·
                      refine ⟨2699613757919540822933801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7198970021118775527823469 2699613757919540822933801)
                      ·
                        rfl

theorem cell23_5257479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_5257479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257479 prefixEnd_5257479 := by exact prefixLift 5257479
  have htrace : WordTrace (prefixWord ++ tailWord_5257479) baseStart_5257479 baseEnd_5257479 := by
    simpa [prefixWord, tailWord_5257479, baseEnd_5257479] using wordTrace_append hprefix tailTrace_5257479
  have hstable : (prefixWord ++ tailWord_5257479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257479).length < 2 ^ (prefixWord ++ tailWord_5257479).sum := by decide
  have hdescent : baseEnd_5257479 < baseStart_5257479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257484 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 1, 5, 3]
def baseStart_5257484 : Nat := 118140960795 + 5257484 * 2 ^ 59
def prefixEnd_5257484 : Nat := 4983230072969 + 3 ^ 40 * 5257484 * 2
def baseEnd_5257484 : Nat := 2699616325322813303371277

theorem tailTrace_5257484 : CollatzResearch.WordTrace tailWord_5257484 prefixEnd_5257484 2699616325322813303371277 := by
  unfold tailWord_5257484
  simp only [CollatzResearch.WordTrace]
  refine ⟨95878097442520424813149753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127837463256693899750866337 95878097442520424813149753)
  ·
    refine ⟨71908573081890318609862315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95878097442520424813149753 71908573081890318609862315)
    ·
      refine ⟨107862859622835477914793473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71908573081890318609862315 107862859622835477914793473)
      ·
        refine ⟨80897144717126608436095105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107862859622835477914793473 80897144717126608436095105)
        ·
          refine ⟨60672858537844956327071329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80897144717126608436095105 60672858537844956327071329)
          ·
            refine ⟨45504643903383717245303497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60672858537844956327071329 45504643903383717245303497)
            ·
              refine ⟨34128482927537787933977623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45504643903383717245303497 34128482927537787933977623)
              ·
                refine ⟨51192724391306681900966435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34128482927537787933977623 51192724391306681900966435)
                ·
                  refine ⟨76789086586960022851449653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51192724391306681900966435 76789086586960022851449653)
                  ·
                    refine ⟨7198976867527502142323405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76789086586960022851449653 7198976867527502142323405)
                    ·
                      refine ⟨2699616325322813303371277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7198976867527502142323405 2699616325322813303371277)
                      ·
                        rfl

theorem cell23_5257484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_5257484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257484 prefixEnd_5257484 := by exact prefixLift 5257484
  have htrace : WordTrace (prefixWord ++ tailWord_5257484) baseStart_5257484 baseEnd_5257484 := by
    simpa [prefixWord, tailWord_5257484, baseEnd_5257484] using wordTrace_append hprefix tailTrace_5257484
  have hstable : (prefixWord ++ tailWord_5257484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257484).length < 2 ^ (prefixWord ++ tailWord_5257484).sum := by decide
  have hdescent : baseEnd_5257484 < baseStart_5257484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257487 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 3, 7]
def baseStart_5257487 : Nat := 118140960795 + 5257487 * 2 ^ 59
def prefixEnd_5257487 : Nat := 4983230072969 + 3 ^ 40 * 5257487 * 2
def baseEnd_5257487 : Nat := 899872621921592263877921

theorem tailTrace_5257487 : CollatzResearch.WordTrace tailWord_5257487 prefixEnd_5257487 899872621921592263877921 := by
  unfold tailWord_5257487
  simp only [CollatzResearch.WordTrace]
  refine ⟨191756304304029981138658715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127837536202686654092439143 191756304304029981138658715)
  ·
    refine ⟨287634456456044971707988073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191756304304029981138658715 287634456456044971707988073)
    ·
      refine ⟨215725842342033728780991055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287634456456044971707988073 215725842342033728780991055)
      ·
        refine ⟨323588763513050593171486583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215725842342033728780991055 323588763513050593171486583)
        ·
          refine ⟨485383145269575889757229875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323588763513050593171486583 485383145269575889757229875)
          ·
            refine ⟨728074717904363834635844813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485383145269575889757229875 728074717904363834635844813)
            ·
              refine ⟨273028019214136437988441805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 728074717904363834635844813 273028019214136437988441805)
              ·
                refine ⟨102385507205301164245665677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 273028019214136437988441805 102385507205301164245665677)
                ·
                  refine ⟨38394565201987936592124629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102385507205301164245665677 38394565201987936592124629)
                  ·
                    refine ⟨899872621921592263877921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38394565201987936592124629 899872621921592263877921)
                    ·
                      rfl

theorem cell23_5257487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 7].length) (baseStart_5257487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257487 prefixEnd_5257487 := by exact prefixLift 5257487
  have htrace : WordTrace (prefixWord ++ tailWord_5257487) baseStart_5257487 baseEnd_5257487 := by
    simpa [prefixWord, tailWord_5257487, baseEnd_5257487] using wordTrace_append hprefix tailTrace_5257487
  have hstable : (prefixWord ++ tailWord_5257487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257487).length < 2 ^ (prefixWord ++ tailWord_5257487).sum := by decide
  have hdescent : baseEnd_5257487 < baseStart_5257487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257584 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 6]
def baseStart_5257584 : Nat := 118140960795 + 5257584 * 2 ^ 59
def prefixEnd_5257584 : Nat := 4983230072969 + 3 ^ 40 * 5257584 * 2
def baseEnd_5257584 : Nat := 2699667673388262912120817

theorem tailTrace_5257584 : CollatzResearch.WordTrace tailWord_5257584 prefixEnd_5257584 2699667673388262912120817 := by
  unfold tailWord_5257584
  simp only [CollatzResearch.WordTrace]
  refine ⟨95879921092339283352469903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127839894789785711136626537 95879921092339283352469903)
  ·
    refine ⟨143819881638508925028704855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95879921092339283352469903 143819881638508925028704855)
    ·
      refine ⟨215729822457763387543057283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143819881638508925028704855 215729822457763387543057283)
      ·
        refine ⟨323594733686645081314585925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215729822457763387543057283 323594733686645081314585925)
        ·
          refine ⟨60674012566245952746484861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 323594733686645081314585925 60674012566245952746484861)
          ·
            refine ⟨22752754712342232279931823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60674012566245952746484861 22752754712342232279931823)
            ·
              refine ⟨34129132068513348419897735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22752754712342232279931823 34129132068513348419897735)
              ·
                refine ⟨51193698102770022629846603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34129132068513348419897735 51193698102770022629846603)
                ·
                  refine ⟨76790547154155033944769905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51193698102770022629846603 76790547154155033944769905)
                  ·
                    refine ⟨57592910365616275458577429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76790547154155033944769905 57592910365616275458577429)
                    ·
                      refine ⟨2699667673388262912120817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57592910365616275458577429 2699667673388262912120817)
                      ·
                        rfl

theorem cell23_5257584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 6].length) (baseStart_5257584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257584 prefixEnd_5257584 := by exact prefixLift 5257584
  have htrace : WordTrace (prefixWord ++ tailWord_5257584) baseStart_5257584 baseEnd_5257584 := by
    simpa [prefixWord, tailWord_5257584, baseEnd_5257584] using wordTrace_append hprefix tailTrace_5257584
  have hstable : (prefixWord ++ tailWord_5257584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257584).length < 2 ^ (prefixWord ++ tailWord_5257584).sum := by decide
  have hdescent : baseEnd_5257584 < baseStart_5257584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257608 : List Nat := [2, 1, 3, 3, 1, 1, 1, 4, 3, 1, 3]
def baseStart_5257608 : Nat := 118140960795 + 5257608 * 2 ^ 59
def prefixEnd_5257608 : Nat := 4983230072969 + 3 ^ 40 * 5257608 * 2
def baseEnd_5257608 : Nat := 2699679996923970818220707

theorem tailTrace_5257608 : CollatzResearch.WordTrace tailWord_5257608 prefixEnd_5257608 2699679996923970818220707 := by
  unfold tailWord_5257608
  simp only [CollatzResearch.WordTrace]
  refine ⟨95880358768295809401906739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127840478357727745869208985 95880358768295809401906739)
  ·
    refine ⟨143820538152443714102860109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95880358768295809401906739 143820538152443714102860109)
    ·
      refine ⟨53932701807166392788572541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143820538152443714102860109 53932701807166392788572541)
      ·
        refine ⟨20224763177687397295714703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53932701807166392788572541 20224763177687397295714703)
        ·
          refine ⟨30337144766531095943572055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20224763177687397295714703 30337144766531095943572055)
          ·
            refine ⟨45505717149796643915358083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30337144766531095943572055 45505717149796643915358083)
            ·
              refine ⟨68258575724694965873037125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45505717149796643915358083 68258575724694965873037125)
              ·
                refine ⟨12798482948380306101194461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68258575724694965873037125 12798482948380306101194461)
                ·
                  refine ⟨4799431105642614787947923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12798482948380306101194461 4799431105642614787947923)
                  ·
                    refine ⟨7199146658463922181921885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4799431105642614787947923 7199146658463922181921885)
                    ·
                      refine ⟨2699679996923970818220707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7199146658463922181921885 2699679996923970818220707)
                      ·
                        rfl

theorem cell23_5257608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_5257608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257608 prefixEnd_5257608 := by exact prefixLift 5257608
  have htrace : WordTrace (prefixWord ++ tailWord_5257608) baseStart_5257608 baseEnd_5257608 := by
    simpa [prefixWord, tailWord_5257608, baseEnd_5257608] using wordTrace_append hprefix tailTrace_5257608
  have hstable : (prefixWord ++ tailWord_5257608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257608).length < 2 ^ (prefixWord ++ tailWord_5257608).sum := by decide
  have hdescent : baseEnd_5257608 < baseStart_5257608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257611 : List Nat := [1, 1, 1, 1, 4, 4, 1, 4, 1, 5]
def baseStart_5257611 : Nat := 118140960795 + 5257611 * 2 ^ 59
def prefixEnd_5257611 : Nat := 4983230072969 + 3 ^ 40 * 5257611 * 2
def baseEnd_5257611 : Nat := 899893845788644768827731

theorem tailTrace_5257611 : CollatzResearch.WordTrace tailWord_5257611 prefixEnd_5257611 899893845788644768827731 := by
  unfold tailWord_5257611
  simp only [CollatzResearch.WordTrace]
  refine ⟨191760826955580750316172687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127840551303720500210781791 191760826955580750316172687)
  ·
    refine ⟨287641240433371125474259031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191760826955580750316172687 287641240433371125474259031)
    ·
      refine ⟨431461860650056688211388547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287641240433371125474259031 431461860650056688211388547)
      ·
        refine ⟨647192790975085032317082821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431461860650056688211388547 647192790975085032317082821)
        ·
          refine ⟨121348648307828443559453029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 647192790975085032317082821 121348648307828443559453029)
          ·
            refine ⟨22752871557717833167397443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121348648307828443559453029 22752871557717833167397443)
            ·
              refine ⟨34129307336576749751096165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22752871557717833167397443 34129307336576749751096165)
              ·
                refine ⟨6399245125608140578330531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34129307336576749751096165 6399245125608140578330531)
                ·
                  refine ⟨9598867688412210867495797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6399245125608140578330531 9598867688412210867495797)
                  ·
                    refine ⟨899893845788644768827731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9598867688412210867495797 899893845788644768827731)
                    ·
                      rfl

theorem cell23_5257611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 5].length) (baseStart_5257611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257611 prefixEnd_5257611 := by exact prefixLift 5257611
  have htrace : WordTrace (prefixWord ++ tailWord_5257611) baseStart_5257611 baseEnd_5257611 := by
    simpa [prefixWord, tailWord_5257611, baseEnd_5257611] using wordTrace_append hprefix tailTrace_5257611
  have hstable : (prefixWord ++ tailWord_5257611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257611).length < 2 ^ (prefixWord ++ tailWord_5257611).sum := by decide
  have hdescent : baseEnd_5257611 < baseStart_5257611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257661 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 1, 1, 6]
def baseStart_5257661 : Nat := 118140960795 + 5257661 * 2 ^ 59
def prefixEnd_5257661 : Nat := 4983230072969 + 3 ^ 40 * 5257661 * 2
def baseEnd_5257661 : Nat := 2699707211398659110857963

theorem tailTrace_5257661 : CollatzResearch.WordTrace tailWord_5257661 prefixEnd_5257661 2699707211398659110857963 := by
  unfold tailWord_5257661
  simp only [CollatzResearch.WordTrace]
  refine ⟨191762650605399608855492837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127841767070266405903661891 191762650605399608855492837)
  ·
    refine ⟨35955496988512426660404907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191762650605399608855492837 35955496988512426660404907)
    ·
      refine ⟨53933245482768639990607361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35955496988512426660404907 53933245482768639990607361)
      ·
        refine ⟨40449934112076479992955521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53933245482768639990607361 40449934112076479992955521)
        ·
          refine ⟨30337450584057359994716641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40449934112076479992955521 30337450584057359994716641)
          ·
            refine ⟨22753087938043019996037481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30337450584057359994716641 22753087938043019996037481)
            ·
              refine ⟨17064815953532264997028111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22753087938043019996037481 17064815953532264997028111)
              ·
                refine ⟨25597223930298397495542167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17064815953532264997028111 25597223930298397495542167)
                ·
                  refine ⟨38395835895447596243313251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25597223930298397495542167 38395835895447596243313251)
                  ·
                    refine ⟨57593753843171394364969877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38395835895447596243313251 57593753843171394364969877)
                    ·
                      refine ⟨2699707211398659110857963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57593753843171394364969877 2699707211398659110857963)
                      ·
                        rfl

theorem cell23_5257661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_5257661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257661 prefixEnd_5257661 := by exact prefixLift 5257661
  have htrace : WordTrace (prefixWord ++ tailWord_5257661) baseStart_5257661 baseEnd_5257661 := by
    simpa [prefixWord, tailWord_5257661, baseEnd_5257661] using wordTrace_append hprefix tailTrace_5257661
  have hstable : (prefixWord ++ tailWord_5257661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257661).length < 2 ^ (prefixWord ++ tailWord_5257661).sum := by decide
  have hdescent : baseEnd_5257661 < baseStart_5257661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257699 : List Nat := [1, 1, 1, 6, 3, 1, 1, 4, 1, 2, 2]
def baseStart_5257699 : Nat := 118140960795 + 5257699 * 2 ^ 59
def prefixEnd_5257699 : Nat := 4983230072969 + 3 ^ 40 * 5257699 * 2
def baseEnd_5257699 : Nat := 2699726723663529962182789

theorem tailTrace_5257699 : CollatzResearch.WordTrace tailWord_5257699 prefixEnd_5257699 2699726723663529962182789 := by
  unfold tailWord_5257699
  simp only [CollatzResearch.WordTrace]
  refine ⟨191764036579261941345376151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127842691052841294230250767 191764036579261941345376151)
  ·
    refine ⟨287646054868892912018064227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191764036579261941345376151 287646054868892912018064227)
    ·
      refine ⟨431469082303339368027096341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287646054868892912018064227 431469082303339368027096341)
      ·
        refine ⟨20225113232969032876270141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 431469082303339368027096341 20225113232969032876270141)
        ·
          refine ⟨7584417462363387328601303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20225113232969032876270141 7584417462363387328601303)
          ·
            refine ⟨11376626193545080992901955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7584417462363387328601303 11376626193545080992901955)
            ·
              refine ⟨17064939290317621489352933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11376626193545080992901955 17064939290317621489352933)
              ·
                refine ⟨3199676116934554029253675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17064939290317621489352933 3199676116934554029253675)
                ·
                  refine ⟨4799514175401831043880513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3199676116934554029253675 4799514175401831043880513)
                  ·
                    refine ⟨3599635631551373282910385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4799514175401831043880513 3599635631551373282910385)
                    ·
                      refine ⟨2699726723663529962182789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3599635631551373282910385 2699726723663529962182789)
                      ·
                        rfl

theorem cell23_5257699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_5257699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257699 prefixEnd_5257699 := by exact prefixLift 5257699
  have htrace : WordTrace (prefixWord ++ tailWord_5257699) baseStart_5257699 baseEnd_5257699 := by
    simpa [prefixWord, tailWord_5257699, baseEnd_5257699] using wordTrace_append hprefix tailTrace_5257699
  have hstable : (prefixWord ++ tailWord_5257699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257699).length < 2 ^ (prefixWord ++ tailWord_5257699).sum := by decide
  have hdescent : baseEnd_5257699 < baseStart_5257699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257708 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 5, 3, 2]
def baseStart_5257708 : Nat := 118140960795 + 5257708 * 2 ^ 59
def prefixEnd_5257708 : Nat := 4983230072969 + 3 ^ 40 * 5257708 * 2
def baseEnd_5257708 : Nat := 2699731344989420426970247

theorem tailTrace_5257708 : CollatzResearch.WordTrace tailWord_5257708 prefixEnd_5257708 2699731344989420426970247 := by
  unfold tailWord_5257708
  simp only [CollatzResearch.WordTrace]
  refine ⟨95882182418114667941226889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127842909890819557254969185 95882182418114667941226889)
  ·
    refine ⟨71911636813586000955920167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95882182418114667941226889 71911636813586000955920167)
    ·
      refine ⟨107867455220379001433880251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71911636813586000955920167 107867455220379001433880251)
      ·
        refine ⟨161801182830568502150820377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107867455220379001433880251 161801182830568502150820377)
        ·
          refine ⟨121350887122926376613115283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161801182830568502150820377 121350887122926376613115283)
          ·
            refine ⟨182026330684389564919672925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121350887122926376613115283 182026330684389564919672925)
            ·
              refine ⟨68259874006646086844877347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182026330684389564919672925 68259874006646086844877347)
              ·
                refine ⟨102389811009969130267316021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68259874006646086844877347 102389811009969130267316021)
                ·
                  refine ⟨9599044782184605962560877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102389811009969130267316021 9599044782184605962560877)
                  ·
                    refine ⟨3599641793319227235960329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9599044782184605962560877 3599641793319227235960329)
                    ·
                      refine ⟨2699731344989420426970247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3599641793319227235960329 2699731344989420426970247)
                      ·
                        rfl

theorem cell23_5257708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 3, 2].length) (baseStart_5257708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257708 prefixEnd_5257708 := by exact prefixLift 5257708
  have htrace : WordTrace (prefixWord ++ tailWord_5257708) baseStart_5257708 baseEnd_5257708 := by
    simpa [prefixWord, tailWord_5257708, baseEnd_5257708] using wordTrace_append hprefix tailTrace_5257708
  have hstable : (prefixWord ++ tailWord_5257708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257708).length < 2 ^ (prefixWord ++ tailWord_5257708).sum := by decide
  have hdescent : baseEnd_5257708 < baseStart_5257708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257725 : List Nat := [1, 4, 1, 1, 1, 3, 2, 4, 1, 3, 2]
def baseStart_5257725 : Nat := 118140960795 + 5257725 * 2 ^ 59
def prefixEnd_5257725 : Nat := 4983230072969 + 3 ^ 40 * 5257725 * 2
def baseEnd_5257725 : Nat := 2699740074160546860457669

theorem tailTrace_5257725 : CollatzResearch.WordTrace tailWord_5257725 prefixEnd_5257725 2699740074160546860457669 := by
  unfold tailWord_5257725
  simp only [CollatzResearch.WordTrace]
  refine ⟨191764984877167747785822629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127843323251445165190548419 191764984877167747785822629)
  ·
    refine ⟨35955934664468952709841743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191764984877167747785822629 35955934664468952709841743)
    ·
      refine ⟨53933901996703429064762615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35955934664468952709841743 53933901996703429064762615)
      ·
        refine ⟨80900852995055143597143923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53933901996703429064762615 80900852995055143597143923)
        ·
          refine ⟨121351279492582715395715885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80900852995055143597143923 121351279492582715395715885)
          ·
            refine ⟨45506729809718518273393457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121351279492582715395715885 45506729809718518273393457)
            ·
              refine ⟨34130047357288888705045093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45506729809718518273393457 34130047357288888705045093)
              ·
                refine ⟨6399383879491666632195955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34130047357288888705045093 6399383879491666632195955)
                ·
                  refine ⟨9599075819237499948293933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6399383879491666632195955 9599075819237499948293933)
                  ·
                    refine ⟨3599653432214062480610225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9599075819237499948293933 3599653432214062480610225)
                    ·
                      refine ⟨2699740074160546860457669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3599653432214062480610225 2699740074160546860457669)
                      ·
                        rfl

theorem cell23_5257725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 3, 2].length) (baseStart_5257725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257725 prefixEnd_5257725 := by exact prefixLift 5257725
  have htrace : WordTrace (prefixWord ++ tailWord_5257725) baseStart_5257725 baseEnd_5257725 := by
    simpa [prefixWord, tailWord_5257725, baseEnd_5257725] using wordTrace_append hprefix tailTrace_5257725
  have hstable : (prefixWord ++ tailWord_5257725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257725).length < 2 ^ (prefixWord ++ tailWord_5257725).sum := by decide
  have hdescent : baseEnd_5257725 < baseStart_5257725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257742 : List Nat := [4, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2]
def baseStart_5257742 : Nat := 118140960795 + 5257742 * 2 ^ 59
def prefixEnd_5257742 : Nat := 4983230072969 + 3 ^ 40 * 5257742 * 2
def baseEnd_5257742 : Nat := 2699748803331673293945091

theorem tailTrace_5257742 : CollatzResearch.WordTrace tailWord_5257742 prefixEnd_5257742 2699748803331673293945091 := by
  unfold tailWord_5257742
  simp only [CollatzResearch.WordTrace]
  refine ⟨23970700614763269961148935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127843736612070773126127653 23970700614763269961148935)
  ·
    refine ⟨35956050922144904941723403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23970700614763269961148935 35956050922144904941723403)
    ·
      refine ⟨53934076383217357412585105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35956050922144904941723403 53934076383217357412585105)
      ·
        refine ⟨40450557287413018059438829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53934076383217357412585105 40450557287413018059438829)
        ·
          refine ⟨15168958982779881772289561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40450557287413018059438829 15168958982779881772289561)
          ·
            refine ⟨11376719237084911329217171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15168958982779881772289561 11376719237084911329217171)
            ·
              refine ⟨17065078855627366993825757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11376719237084911329217171 17065078855627366993825757)
              ·
                refine ⟨6399404570860262622684659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17065078855627366993825757 6399404570860262622684659)
                ·
                  refine ⟨9599106856290393934026989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6399404570860262622684659 9599106856290393934026989)
                  ·
                    refine ⟨3599665071108897725260121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9599106856290393934026989 3599665071108897725260121)
                    ·
                      refine ⟨2699748803331673293945091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3599665071108897725260121 2699748803331673293945091)
                      ·
                        rfl

theorem cell23_5257742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_5257742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257742 prefixEnd_5257742 := by exact prefixLift 5257742
  have htrace : WordTrace (prefixWord ++ tailWord_5257742) baseStart_5257742 baseEnd_5257742 := by
    simpa [prefixWord, tailWord_5257742, baseEnd_5257742] using wordTrace_append hprefix tailTrace_5257742
  have hstable : (prefixWord ++ tailWord_5257742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257742).length < 2 ^ (prefixWord ++ tailWord_5257742).sum := by decide
  have hdescent : baseEnd_5257742 < baseStart_5257742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257791 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 1, 7]
def baseStart_5257791 : Nat := 118140960795 + 5257791 * 2 ^ 59
def prefixEnd_5257791 : Nat := 4983230072969 + 3 ^ 40 * 5257791 * 2
def baseEnd_5257791 : Nat := 899924654627914534077455

theorem tailTrace_5257791 : CollatzResearch.WordTrace tailWord_5257791 prefixEnd_5257791 899924654627914534077455 := by
  unfold tailWord_5257791
  simp only [CollatzResearch.WordTrace]
  refine ⟨191767392094928641057725227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127844928063285760705150151 191767392094928641057725227)
  ·
    refine ⟨287651088142392961586587841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191767392094928641057725227 287651088142392961586587841)
    ·
      refine ⟨215738316106794721189940881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287651088142392961586587841 215738316106794721189940881)
      ·
        refine ⟨161803737080096040892455661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215738316106794721189940881 161803737080096040892455661)
        ·
          refine ⟨60676401405036015334670873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161803737080096040892455661 60676401405036015334670873)
          ·
            refine ⟨45507301053777011501003155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60676401405036015334670873 45507301053777011501003155)
            ·
              refine ⟨68260951580665517251504733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45507301053777011501003155 68260951580665517251504733)
              ·
                refine ⟨25597856842749568969314275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68260951580665517251504733 25597856842749568969314275)
                ·
                  refine ⟨38396785264124353453971413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25597856842749568969314275 38396785264124353453971413)
                  ·
                    refine ⟨899924654627914534077455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38396785264124353453971413 899924654627914534077455)
                    ·
                      rfl

theorem cell23_5257791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 7].length) (baseStart_5257791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257791 prefixEnd_5257791 := by exact prefixLift 5257791
  have htrace : WordTrace (prefixWord ++ tailWord_5257791) baseStart_5257791 baseEnd_5257791 := by
    simpa [prefixWord, tailWord_5257791, baseEnd_5257791] using wordTrace_append hprefix tailTrace_5257791
  have hstable : (prefixWord ++ tailWord_5257791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257791).length < 2 ^ (prefixWord ++ tailWord_5257791).sum := by decide
  have hdescent : baseEnd_5257791 < baseStart_5257791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257812 : List Nat := [2, 4, 1, 1, 1, 4, 3, 2, 5]
def baseStart_5257812 : Nat := 118140960795 + 5257812 * 2 ^ 59
def prefixEnd_5257812 : Nat := 4983230072969 + 3 ^ 40 * 5257812 * 2
def baseEnd_5257812 : Nat := 299976082997498668896641

theorem tailTrace_5257812 : CollatzResearch.WordTrace tailWord_5257812 prefixEnd_5257812 299976082997498668896641 := by
  unfold tailWord_5257812
  simp only [CollatzResearch.WordTrace]
  refine ⟨95884079013926280822119845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127845438685235041096159793 95884079013926280822119845)
  ·
    refine ⟨17978264815111177654147471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95884079013926280822119845 17978264815111177654147471)
    ·
      refine ⟨26967397222666766481221207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17978264815111177654147471 26967397222666766481221207)
      ·
        refine ⟨40451095834000149721831811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26967397222666766481221207 40451095834000149721831811)
        ·
          refine ⟨60676643751000224582747717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40451095834000149721831811 60676643751000224582747717)
          ·
            refine ⟨11376870703312542109265197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60676643751000224582747717 11376870703312542109265197)
            ·
              refine ⟨4266326513742203290974449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11376870703312542109265197 4266326513742203290974449)
              ·
                refine ⟨3199744885306652468230837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4266326513742203290974449 3199744885306652468230837)
                ·
                  refine ⟨299976082997498668896641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3199744885306652468230837 299976082997498668896641)
                  ·
                    rfl

theorem cell23_5257812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_5257812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257812 prefixEnd_5257812 := by exact prefixLift 5257812
  have htrace : WordTrace (prefixWord ++ tailWord_5257812) baseStart_5257812 baseEnd_5257812 := by
    simpa [prefixWord, tailWord_5257812, baseEnd_5257812] using wordTrace_append hprefix tailTrace_5257812
  have hstable : (prefixWord ++ tailWord_5257812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257812).length < 2 ^ (prefixWord ++ tailWord_5257812).sum := by decide
  have hdescent : baseEnd_5257812 < baseStart_5257812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257828 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 4, 1, 4]
def baseStart_5257828 : Nat := 118140960795 + 5257828 * 2 ^ 59
def prefixEnd_5257828 : Nat := 4983230072969 + 3 ^ 40 * 5257828 * 2
def baseEnd_5257828 : Nat := 2699792962667959957469695

theorem tailTrace_5257828 : CollatzResearch.WordTrace tailWord_5257828 prefixEnd_5257828 2699792962667959957469695 := by
  unfold tailWord_5257828
  simp only [CollatzResearch.WordTrace]
  refine ⟨95884370797897298188411069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127845827730529730917881425 95884370797897298188411069)
  ·
    refine ⟨35956639049211486820654151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95884370797897298188411069 35956639049211486820654151)
    ·
      refine ⟨53934958573817230230981227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35956639049211486820654151 53934958573817230230981227)
      ·
        refine ⟨80902437860725845346471841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53934958573817230230981227 80902437860725845346471841)
        ·
          refine ⟨60676828395544384009853881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80902437860725845346471841 60676828395544384009853881)
          ·
            refine ⟨45507621296658288007390411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60676828395544384009853881 45507621296658288007390411)
            ·
              refine ⟨68261431944987432011085617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45507621296658288007390411 68261431944987432011085617)
              ·
                refine ⟨51196073958740574008314213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68261431944987432011085617 51196073958740574008314213)
                ·
                  refine ⟨9599263867263857626558915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51196073958740574008314213 9599263867263857626558915)
                  ·
                    refine ⟨14398895800895786439838373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9599263867263857626558915 14398895800895786439838373)
                    ·
                      refine ⟨2699792962667959957469695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14398895800895786439838373 2699792962667959957469695)
                      ·
                        rfl

theorem cell23_5257828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_5257828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257828 prefixEnd_5257828 := by exact prefixLift 5257828
  have htrace : WordTrace (prefixWord ++ tailWord_5257828) baseStart_5257828 baseEnd_5257828 := by
    simpa [prefixWord, tailWord_5257828, baseEnd_5257828] using wordTrace_append hprefix tailTrace_5257828
  have hstable : (prefixWord ++ tailWord_5257828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257828).length < 2 ^ (prefixWord ++ tailWord_5257828).sum := by decide
  have hdescent : baseEnd_5257828 < baseStart_5257828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257841 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 3, 3, 6]
def baseStart_5257841 : Nat := 118140960795 + 5257841 * 2 ^ 59
def prefixEnd_5257841 : Nat := 4983230072969 + 3 ^ 40 * 5257841 * 2
def baseEnd_5257841 : Nat := 2699799637916468406607135

theorem tailTrace_5257841 : CollatzResearch.WordTrace tailWord_5257841 prefixEnd_5257841 2699799637916468406607135 := by
  unfold tailWord_5257841
  simp only [CollatzResearch.WordTrace]
  refine ⟨191769215744747499597045377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127846143829831666398030251 191769215744747499597045377)
  ·
    refine ⟨143826911808560624697784033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191769215744747499597045377 143826911808560624697784033)
    ·
      refine ⟨107870183856420468523338025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143826911808560624697784033 107870183856420468523338025)
      ·
        refine ⟨80902637892315351392503519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107870183856420468523338025 80902637892315351392503519)
        ·
          refine ⟨121353956838473027088755279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80902637892315351392503519 121353956838473027088755279)
          ·
            refine ⟨182030935257709540633132919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121353956838473027088755279 182030935257709540633132919)
            ·
              refine ⟨273046402886564310949699379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182030935257709540633132919 273046402886564310949699379)
              ·
                refine ⟨409569604329846466424549069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273046402886564310949699379 409569604329846466424549069)
                ·
                  refine ⟨153588601623692424909205901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 409569604329846466424549069 153588601623692424909205901)
                  ·
                    refine ⟨57595725608884659340952213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 153588601623692424909205901 57595725608884659340952213)
                    ·
                      refine ⟨2699799637916468406607135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57595725608884659340952213 2699799637916468406607135)
                      ·
                        rfl

theorem cell23_5257841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_5257841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257841 prefixEnd_5257841 := by exact prefixLift 5257841
  have htrace : WordTrace (prefixWord ++ tailWord_5257841) baseStart_5257841 baseEnd_5257841 := by
    simpa [prefixWord, tailWord_5257841, baseEnd_5257841] using wordTrace_append hprefix tailTrace_5257841
  have hstable : (prefixWord ++ tailWord_5257841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257841).length < 2 ^ (prefixWord ++ tailWord_5257841).sum := by decide
  have hdescent : baseEnd_5257841 < baseStart_5257841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257848 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 6, 2, 3]
def baseStart_5257848 : Nat := 118140960795 + 5257848 * 2 ^ 59
def prefixEnd_5257848 : Nat := 4983230072969 + 3 ^ 40 * 5257848 * 2
def baseEnd_5257848 : Nat := 2699803232281049879219603

theorem tailTrace_5257848 : CollatzResearch.WordTrace tailWord_5257848 prefixEnd_5257848 2699803232281049879219603 := by
  unfold tailWord_5257848
  simp only [CollatzResearch.WordTrace]
  refine ⟨95884735527861069896275099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127846314037148093195033465 95884735527861069896275099)
  ·
    refine ⟨143827103291791604844412649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95884735527861069896275099 143827103291791604844412649)
    ·
      refine ⟨107870327468843703633309487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143827103291791604844412649 107870327468843703633309487)
      ·
        refine ⟨161805491203265555449964231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107870327468843703633309487 161805491203265555449964231)
        ·
          refine ⟨242708236804898333174946347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161805491203265555449964231 242708236804898333174946347)
          ·
            refine ⟨364062355207347499762419521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242708236804898333174946347 364062355207347499762419521)
            ·
              refine ⟨273046766405510624821814641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 364062355207347499762419521 273046766405510624821814641)
              ·
                refine ⟨204785074804132968616360981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273046766405510624821814641 204785074804132968616360981)
                ·
                  refine ⟨9599300381443732903891921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 204785074804132968616360981 9599300381443732903891921)
                  ·
                    refine ⟨7199475286082799677918941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9599300381443732903891921 7199475286082799677918941)
                    ·
                      refine ⟨2699803232281049879219603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7199475286082799677918941 2699803232281049879219603)
                      ·
                        rfl

theorem cell23_5257848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 6, 2, 3].length) (baseStart_5257848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257848 prefixEnd_5257848 := by exact prefixLift 5257848
  have htrace : WordTrace (prefixWord ++ tailWord_5257848) baseStart_5257848 baseEnd_5257848 := by
    simpa [prefixWord, tailWord_5257848, baseEnd_5257848] using wordTrace_append hprefix tailTrace_5257848
  have hstable : (prefixWord ++ tailWord_5257848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257848).length < 2 ^ (prefixWord ++ tailWord_5257848).sum := by decide
  have hdescent : baseEnd_5257848 < baseStart_5257848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257851 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 8]
def baseStart_5257851 : Nat := 118140960795 + 5257851 * 2 ^ 59
def prefixEnd_5257851 : Nat := 4983230072969 + 3 ^ 40 * 5257851 * 2
def baseEnd_5257851 : Nat := 299978308080334818609121

theorem tailTrace_5257851 : CollatzResearch.WordTrace tailWord_5257851 prefixEnd_5257851 299978308080334818609121 := by
  unfold tailWord_5257851
  simp only [CollatzResearch.WordTrace]
  refine ⟨191769580474711271304909407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127846386983140847536606271 191769580474711271304909407)
  ·
    refine ⟨287654370712066906957364111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191769580474711271304909407 287654370712066906957364111)
    ·
      refine ⟨431481556068100360436046167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287654370712066906957364111 431481556068100360436046167)
      ·
        refine ⟨647222334102150540654069251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431481556068100360436046167 647222334102150540654069251)
        ·
          refine ⟨970833501153225810981103877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647222334102150540654069251 970833501153225810981103877)
          ·
            refine ⟨182031281466229839558956977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 970833501153225810981103877 182031281466229839558956977)
            ·
              refine ⟨136523461099672379669217733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182031281466229839558956977 136523461099672379669217733)
              ·
                refine ⟨25598148956188571187978325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136523461099672379669217733 25598148956188571187978325)
                ·
                  refine ⟨299978308080334818609121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25598148956188571187978325 299978308080334818609121)
                  ·
                    rfl

theorem cell23_5257851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 8].length) (baseStart_5257851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257851 prefixEnd_5257851 := by exact prefixLift 5257851
  have htrace : WordTrace (prefixWord ++ tailWord_5257851) baseStart_5257851 baseEnd_5257851 := by
    simpa [prefixWord, tailWord_5257851, baseEnd_5257851] using wordTrace_append hprefix tailTrace_5257851
  have hstable : (prefixWord ++ tailWord_5257851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257851).length < 2 ^ (prefixWord ++ tailWord_5257851).sum := by decide
  have hdescent : baseEnd_5257851 < baseStart_5257851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257871 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 8]
def baseStart_5257871 : Nat := 118140960795 + 5257871 * 2 ^ 59
def prefixEnd_5257871 : Nat := 4983230072969 + 3 ^ 40 * 5257871 * 2
def baseEnd_5257871 : Nat := 2699815042336103289231997

theorem tailTrace_5257871 : CollatzResearch.WordTrace tailWord_5257871 prefixEnd_5257871 2699815042336103289231997 := by
  unfold tailWord_5257871
  simp only [CollatzResearch.WordTrace]
  refine ⟨191770309934638814720637467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127846873289759209813758311 191770309934638814720637467)
  ·
    refine ⟨287655464901958222080956201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191770309934638814720637467 287655464901958222080956201)
    ·
      refine ⟨215741598676468666560717151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287655464901958222080956201 215741598676468666560717151)
      ·
        refine ⟨323612398014702999841075727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215741598676468666560717151 323612398014702999841075727)
        ·
          refine ⟨485418597022054499761613591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323612398014702999841075727 485418597022054499761613591)
          ·
            refine ⟨728127895533081749642420387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485418597022054499761613591 728127895533081749642420387)
            ·
              refine ⟨1092191843299622624463630581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 728127895533081749642420387 1092191843299622624463630581)
              ·
                refine ⟨102392985309339621043465367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1092191843299622624463630581 102392985309339621043465367)
                ·
                  refine ⟨153589477964009431565198051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102392985309339621043465367 153589477964009431565198051)
                  ·
                    refine ⟨230384216946014147347797077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 153589477964009431565198051 230384216946014147347797077)
                    ·
                      refine ⟨2699815042336103289231997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 230384216946014147347797077 2699815042336103289231997)
                      ·
                        rfl

theorem cell23_5257871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_5257871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257871 prefixEnd_5257871 := by exact prefixLift 5257871
  have htrace : WordTrace (prefixWord ++ tailWord_5257871) baseStart_5257871 baseEnd_5257871 := by
    simpa [prefixWord, tailWord_5257871, baseEnd_5257871] using wordTrace_append hprefix tailTrace_5257871
  have hstable : (prefixWord ++ tailWord_5257871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257871).length < 2 ^ (prefixWord ++ tailWord_5257871).sum := by decide
  have hdescent : baseEnd_5257871 < baseStart_5257871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257965 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_5257965 : Nat := 118140960795 + 5257965 * 2 ^ 59
def prefixEnd_5257965 : Nat := 4983230072969 + 3 ^ 40 * 5257965 * 2
def baseEnd_5257965 : Nat := 2699863309517625921456565

theorem tailTrace_5257965 : CollatzResearch.WordTrace tailWord_5257965 prefixEnd_5257965 2699863309517625921456565 := by
  unfold tailWord_5257965
  simp only [CollatzResearch.WordTrace]
  refine ⟨191773738396298268774559349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127849158930865512516372899 191773738396298268774559349)
  ·
    refine ⟨17978787974652962697614939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191773738396298268774559349 17978787974652962697614939)
    ·
      refine ⟨26968181961979444046422409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17978787974652962697614939 26968181961979444046422409)
      ·
        refine ⟨20226136471484583034816807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26968181961979444046422409 20226136471484583034816807)
        ·
          refine ⟨30339204707226874552225211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20226136471484583034816807 30339204707226874552225211)
          ·
            refine ⟨45508807060840311828337817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30339204707226874552225211 45508807060840311828337817)
            ·
              refine ⟨34131605295630233871253363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45508807060840311828337817 34131605295630233871253363)
              ·
                refine ⟨51197407943445350806880045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34131605295630233871253363 51197407943445350806880045)
                ·
                  refine ⟨19199027978792006552580017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51197407943445350806880045 19199027978792006552580017)
                  ·
                    refine ⟨14399270984094004914435013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19199027978792006552580017 14399270984094004914435013)
                    ·
                      refine ⟨2699863309517625921456565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14399270984094004914435013 2699863309517625921456565)
                      ·
                        rfl

theorem cell23_5257965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_5257965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257965 prefixEnd_5257965 := by exact prefixLift 5257965
  have htrace : WordTrace (prefixWord ++ tailWord_5257965) baseStart_5257965 baseEnd_5257965 := by
    simpa [prefixWord, tailWord_5257965, baseEnd_5257965] using wordTrace_append hprefix tailTrace_5257965
  have hstable : (prefixWord ++ tailWord_5257965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257965).length < 2 ^ (prefixWord ++ tailWord_5257965).sum := by decide
  have hdescent : baseEnd_5257965 < baseStart_5257965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257973 : List Nat := [1, 3, 6, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_5257973 : Nat := 118140960795 + 5257973 * 2 ^ 59
def prefixEnd_5257973 : Nat := 4983230072969 + 3 ^ 40 * 5257973 * 2
def baseEnd_5257973 : Nat := 2699867417362861890156529

theorem tailTrace_5257973 : CollatzResearch.WordTrace tailWord_5257973 prefixEnd_5257973 2699867417362861890156529 := by
  unfold tailWord_5257973
  simp only [CollatzResearch.WordTrace]
  refine ⟨191774030180269286140850573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127849353453512857427233715 191774030180269286140850573)
  ·
    refine ⟨71915261317600982302818965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191774030180269286140850573 71915261317600982302818965)
    ·
      refine ⟨3371027874262546045444639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 71915261317600982302818965 3371027874262546045444639)
      ·
        refine ⟨5056541811393819068166959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3371027874262546045444639 5056541811393819068166959)
        ·
          refine ⟨7584812717090728602250439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5056541811393819068166959 7584812717090728602250439)
          ·
            refine ⟨11377219075636092903375659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7584812717090728602250439 11377219075636092903375659)
            ·
              refine ⟨17065828613454139355063489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11377219075636092903375659 17065828613454139355063489)
              ·
                refine ⟨12799371460090604516297617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17065828613454139355063489 12799371460090604516297617)
                ·
                  refine ⟨9599528595067953387223213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12799371460090604516297617 9599528595067953387223213)
                  ·
                    refine ⟨3599823223150482520208705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9599528595067953387223213 3599823223150482520208705)
                    ·
                      refine ⟨2699867417362861890156529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3599823223150482520208705 2699867417362861890156529)
                      ·
                        rfl

theorem cell23_5257973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_5257973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257973 prefixEnd_5257973 := by exact prefixLift 5257973
  have htrace : WordTrace (prefixWord ++ tailWord_5257973) baseStart_5257973 baseEnd_5257973 := by
    simpa [prefixWord, tailWord_5257973, baseEnd_5257973] using wordTrace_append hprefix tailTrace_5257973
  have hstable : (prefixWord ++ tailWord_5257973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257973).length < 2 ^ (prefixWord ++ tailWord_5257973).sum := by decide
  have hdescent : baseEnd_5257973 < baseStart_5257973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257986 : List Nat := [3, 4, 1, 1, 1, 2, 3, 1, 3, 2, 2]
def baseStart_5257986 : Nat := 118140960795 + 5257986 * 2 ^ 59
def prefixEnd_5257986 : Nat := 4983230072969 + 3 ^ 40 * 5257986 * 2
def baseEnd_5257986 : Nat := 2699874092611370339293969

theorem tailTrace_5257986 : CollatzResearch.WordTrace tailWord_5257986 prefixEnd_5257986 2699874092611370339293969 := by
  unfold tailWord_5257986
  simp only [CollatzResearch.WordTrace]
  refine ⟨47943626082305547340268453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127849669552814792907382541 47943626082305547340268453)
  ·
    refine ⟨8989429890432290126300335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47943626082305547340268453 8989429890432290126300335)
    ·
      refine ⟨13484144835648435189450503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8989429890432290126300335 13484144835648435189450503)
      ·
        refine ⟨20226217253472652784175755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13484144835648435189450503 20226217253472652784175755)
        ·
          refine ⟨30339325880208979176263633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20226217253472652784175755 30339325880208979176263633)
          ·
            refine ⟨22754494410156734382197725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30339325880208979176263633 22754494410156734382197725)
            ·
              refine ⟨8532935403808775393324147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22754494410156734382197725 8532935403808775393324147)
              ·
                refine ⟨12799403105713163089986221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8532935403808775393324147 12799403105713163089986221)
                ·
                  refine ⟨4799776164642436158744833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12799403105713163089986221 4799776164642436158744833)
                  ·
                    refine ⟨3599832123481827119058625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4799776164642436158744833 3599832123481827119058625)
                    ·
                      refine ⟨2699874092611370339293969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3599832123481827119058625 2699874092611370339293969)
                      ·
                        rfl

theorem cell23_5257986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_5257986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257986 prefixEnd_5257986 := by exact prefixLift 5257986
  have htrace : WordTrace (prefixWord ++ tailWord_5257986) baseStart_5257986 baseEnd_5257986 := by
    simpa [prefixWord, tailWord_5257986, baseEnd_5257986] using wordTrace_append hprefix tailTrace_5257986
  have hstable : (prefixWord ++ tailWord_5257986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257986).length < 2 ^ (prefixWord ++ tailWord_5257986).sum := by decide
  have hdescent : baseEnd_5257986 < baseStart_5257986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5257995 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 2, 7, 2]
def baseStart_5257995 : Nat := 118140960795 + 5257995 * 2 ^ 59
def prefixEnd_5257995 : Nat := 4983230072969 + 3 ^ 40 * 5257995 * 2
def baseEnd_5257995 : Nat := 2699878713937260804081427

theorem tailTrace_5257995 : CollatzResearch.WordTrace tailWord_5257995 prefixEnd_5257995 2699878713937260804081427 := by
  unfold tailWord_5257995
  simp only [CollatzResearch.WordTrace]
  refine ⟨191774832586189583898151439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127849888390793055932100959 191774832586189583898151439)
  ·
    refine ⟨287662248879284375847227159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191774832586189583898151439 287662248879284375847227159)
    ·
      refine ⟨431493373318926563770840739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287662248879284375847227159 431493373318926563770840739)
      ·
        refine ⟨647240059978389845656261109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431493373318926563770840739 647240059978389845656261109)
        ·
          refine ⟨60678755622974048030274479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 647240059978389845656261109 60678755622974048030274479)
          ·
            refine ⟨91018133434461072045411719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60678755622974048030274479 91018133434461072045411719)
            ·
              refine ⟨136527200151691608068117579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91018133434461072045411719 136527200151691608068117579)
              ·
                refine ⟨204790800227537412102176369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136527200151691608068117579 204790800227537412102176369)
                ·
                  refine ⟨153593100170653059076632277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204790800227537412102176369 153593100170653059076632277)
                  ·
                    refine ⟨3599838285249681072108569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 153593100170653059076632277 3599838285249681072108569)
                    ·
                      refine ⟨2699878713937260804081427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3599838285249681072108569 2699878713937260804081427)
                      ·
                        rfl

theorem cell23_5257995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 7, 2].length) (baseStart_5257995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5257995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5257995 prefixEnd_5257995 := by exact prefixLift 5257995
  have htrace : WordTrace (prefixWord ++ tailWord_5257995) baseStart_5257995 baseEnd_5257995 := by
    simpa [prefixWord, tailWord_5257995, baseEnd_5257995] using wordTrace_append hprefix tailTrace_5257995
  have hstable : (prefixWord ++ tailWord_5257995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5257995).length < 2 ^ (prefixWord ++ tailWord_5257995).sum := by decide
  have hdescent : baseEnd_5257995 < baseStart_5257995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5257995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258008 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 1, 2, 8]
def baseStart_5258008 : Nat := 118140960795 + 5258008 * 2 ^ 59
def prefixEnd_5258008 : Nat := 4983230072969 + 3 ^ 40 * 5258008 * 2
def baseEnd_5258008 : Nat := 2699885389185769253218867

theorem tailTrace_5258008 : CollatzResearch.WordTrace tailWord_5258008 prefixEnd_5258008 2699885389185769253218867 := by
  unfold tailWord_5258008
  simp only [CollatzResearch.WordTrace]
  refine ⟨95887653367571243559187339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127850204490094991412249785 95887653367571243559187339)
  ·
    refine ⟨143831480051356865338781009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95887653367571243559187339 143831480051356865338781009)
    ·
      refine ⟨107873610038517649004085757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143831480051356865338781009 107873610038517649004085757)
      ·
        refine ⟨40452603764444118376532159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107873610038517649004085757 40452603764444118376532159)
        ·
          refine ⟨60678905646666177564798239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40452603764444118376532159 60678905646666177564798239)
          ·
            refine ⟨91018358469999266347197359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60678905646666177564798239 91018358469999266347197359)
            ·
              refine ⟨136527537704998899520796039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91018358469999266347197359 136527537704998899520796039)
              ·
                refine ⟨204791306557498349281194059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136527537704998899520796039 204791306557498349281194059)
                ·
                  refine ⟨307186959836247523921791089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204791306557498349281194059 307186959836247523921791089)
                  ·
                    refine ⟨230390219877185642941343317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 307186959836247523921791089 230390219877185642941343317)
                    ·
                      refine ⟨2699885389185769253218867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 230390219877185642941343317 2699885389185769253218867)
                      ·
                        rfl

theorem cell23_5258008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_5258008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258008 prefixEnd_5258008 := by exact prefixLift 5258008
  have htrace : WordTrace (prefixWord ++ tailWord_5258008) baseStart_5258008 baseEnd_5258008 := by
    simpa [prefixWord, tailWord_5258008, baseEnd_5258008] using wordTrace_append hprefix tailTrace_5258008
  have hstable : (prefixWord ++ tailWord_5258008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258008).length < 2 ^ (prefixWord ++ tailWord_5258008).sum := by decide
  have hdescent : baseEnd_5258008 < baseStart_5258008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258048 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 11]
def baseStart_5258048 : Nat := 118140960795 + 5258048 * 2 ^ 59
def prefixEnd_5258048 : Nat := 4983230072969 + 3 ^ 40 * 5258048 * 2
def baseEnd_5258048 : Nat := 299989547601327677413187

theorem tailTrace_5258048 : CollatzResearch.WordTrace tailWord_5258048 prefixEnd_5258048 299989547601327677413187 := by
  unfold tailWord_5258048
  simp only [CollatzResearch.WordTrace]
  refine ⟨95888382827498786974915399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127851177103331715966553865 95888382827498786974915399)
  ·
    refine ⟨143832574241248180462373099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95888382827498786974915399 143832574241248180462373099)
    ·
      refine ⟨215748861361872270693559649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143832574241248180462373099 215748861361872270693559649)
      ·
        refine ⟨161811646021404203020169737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215748861361872270693559649 161811646021404203020169737)
        ·
          refine ⟨121358734516053152265127303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161811646021404203020169737 121358734516053152265127303)
          ·
            refine ⟨182038101774079728397690955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121358734516053152265127303 182038101774079728397690955)
            ·
              refine ⟨273057152661119592596536433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182038101774079728397690955 273057152661119592596536433)
              ·
                refine ⟨204792864495839694447402325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273057152661119592596536433 204792864495839694447402325)
                ·
                  refine ⟨299989547601327677413187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 204792864495839694447402325 299989547601327677413187)
                  ·
                    rfl

theorem cell23_5258048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 11].length) (baseStart_5258048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258048 prefixEnd_5258048 := by exact prefixLift 5258048
  have htrace : WordTrace (prefixWord ++ tailWord_5258048) baseStart_5258048 baseEnd_5258048 := by
    simpa [prefixWord, tailWord_5258048, baseEnd_5258048] using wordTrace_append hprefix tailTrace_5258048
  have hstable : (prefixWord ++ tailWord_5258048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258048).length < 2 ^ (prefixWord ++ tailWord_5258048).sum := by decide
  have hdescent : baseEnd_5258048 < baseStart_5258048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258095 : List Nat := [1, 1, 2, 1, 3, 1, 1, 6, 2, 5]
def baseStart_5258095 : Nat := 118140960795 + 5258095 * 2 ^ 59
def prefixEnd_5258095 : Nat := 4983230072969 + 3 ^ 40 * 5258095 * 2
def baseEnd_5258095 : Nat := 899976687334236804276989

theorem tailTrace_5258095 : CollatzResearch.WordTrace tailWord_5258095 prefixEnd_5258095 899976687334236804276989 := by
  unfold tailWord_5258095
  simp only [CollatzResearch.WordTrace]
  refine ⟨191778479885827300976791739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127852319923884867317861159 191778479885827300976791739)
  ·
    refine ⟨287667719828740951465187609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191778479885827300976791739 287667719828740951465187609)
    ·
      refine ⟨215750789871555713598890707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287667719828740951465187609 215750789871555713598890707)
      ·
        refine ⟨323626184807333570398336061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215750789871555713598890707 323626184807333570398336061)
        ·
          refine ⟨121359819302750088899376023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 323626184807333570398336061 121359819302750088899376023)
          ·
            refine ⟨182039728954125133349064035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121359819302750088899376023 182039728954125133349064035)
            ·
              refine ⟨273059593431187700023596053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182039728954125133349064035 273059593431187700023596053)
              ·
                refine ⟨12799668442086923438606065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 273059593431187700023596053 12799668442086923438606065)
                ·
                  refine ⟨9599751331565192578954549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12799668442086923438606065 9599751331565192578954549)
                  ·
                    refine ⟨899976687334236804276989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9599751331565192578954549 899976687334236804276989)
                    ·
                      rfl

theorem cell23_5258095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 5].length) (baseStart_5258095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258095 prefixEnd_5258095 := by exact prefixLift 5258095
  have htrace : WordTrace (prefixWord ++ tailWord_5258095) baseStart_5258095 baseEnd_5258095 := by
    simpa [prefixWord, tailWord_5258095, baseEnd_5258095] using wordTrace_append hprefix tailTrace_5258095
  have hstable : (prefixWord ++ tailWord_5258095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258095).length < 2 ^ (prefixWord ++ tailWord_5258095).sum := by decide
  have hdescent : baseEnd_5258095 < baseStart_5258095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258110 : List Nat := [4, 2, 3, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_5258110 : Nat := 118140960795 + 5258110 * 2 ^ 59
def prefixEnd_5258110 : Nat := 4983230072969 + 3 ^ 40 * 5258110 * 2
def baseEnd_5258110 : Nat := 2699937764212527854143399

theorem tailTrace_5258110 : CollatzResearch.WordTrace tailWord_5258110 prefixEnd_5258110 2699937764212527854143399 := by
  unfold tailWord_5258110
  simp only [CollatzResearch.WordTrace]
  refine ⟨23972378372596619817323473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127852684653848639025725189 23972378372596619817323473)
  ·
    refine ⟨17979283779447464862992605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23972378372596619817323473 17979283779447464862992605)
    ·
      refine ⟨6742231417292799323622227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17979283779447464862992605 6742231417292799323622227)
      ·
        refine ⟨10113347125939198985433341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6742231417292799323622227 10113347125939198985433341)
        ·
          refine ⟨3792505172227199619537503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10113347125939198985433341 3792505172227199619537503)
          ·
            refine ⟨5688757758340799429306255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3792505172227199619537503 5688757758340799429306255)
            ·
              refine ⟨8533136637511199143959383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5688757758340799429306255 8533136637511199143959383)
              ·
                refine ⟨12799704956266798715939075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8533136637511199143959383 12799704956266798715939075)
                ·
                  refine ⟨19199557434400198073908613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12799704956266798715939075 19199557434400198073908613)
                  ·
                    refine ⟨3599917018950037138857865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19199557434400198073908613 3599917018950037138857865)
                    ·
                      refine ⟨2699937764212527854143399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3599917018950037138857865 2699937764212527854143399)
                      ·
                        rfl

theorem cell23_5258110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_5258110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258110 prefixEnd_5258110 := by exact prefixLift 5258110
  have htrace : WordTrace (prefixWord ++ tailWord_5258110) baseStart_5258110 baseEnd_5258110 := by
    simpa [prefixWord, tailWord_5258110, baseEnd_5258110] using wordTrace_append hprefix tailTrace_5258110
  have hstable : (prefixWord ++ tailWord_5258110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258110).length < 2 ^ (prefixWord ++ tailWord_5258110).sum := by decide
  have hdescent : baseEnd_5258110 < baseStart_5258110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258115 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 4]
def baseStart_5258115 : Nat := 118140960795 + 5258115 * 2 ^ 59
def prefixEnd_5258115 : Nat := 4983230072969 + 3 ^ 40 * 5258115 * 2
def baseEnd_5258115 : Nat := 2699940331615800334580875

theorem tailTrace_5258115 : CollatzResearch.WordTrace tailWord_5258115 prefixEnd_5258115 2699940331615800334580875 := by
  unfold tailWord_5258115
  simp only [CollatzResearch.WordTrace]
  refine ⟨191779209345754844392519799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127852806230503229595013199 191779209345754844392519799)
  ·
    refine ⟨287668814018632266588779699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191779209345754844392519799 287668814018632266588779699)
    ·
      refine ⟨431503221027948399883169549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287668814018632266588779699 431503221027948399883169549)
      ·
        refine ⟨161813707885480649956188581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 431503221027948399883169549 161813707885480649956188581)
        ·
          refine ⟨30340070228527621866785359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161813707885480649956188581 30340070228527621866785359)
          ·
            refine ⟨45510105342791432800178039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30340070228527621866785359 45510105342791432800178039)
            ·
              refine ⟨68265158014187149200267059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45510105342791432800178039 68265158014187149200267059)
              ·
                refine ⟨102397737021280723800400589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68265158014187149200267059 102397737021280723800400589)
                ·
                  refine ⟨38399151382980271425150221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102397737021280723800400589 38399151382980271425150221)
                  ·
                    refine ⟨14399681768617601784431333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38399151382980271425150221 14399681768617601784431333)
                    ·
                      refine ⟨2699940331615800334580875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14399681768617601784431333 2699940331615800334580875)
                      ·
                        rfl

theorem cell23_5258115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_5258115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258115 prefixEnd_5258115 := by exact prefixLift 5258115
  have htrace : WordTrace (prefixWord ++ tailWord_5258115) baseStart_5258115 baseEnd_5258115 := by
    simpa [prefixWord, tailWord_5258115, baseEnd_5258115] using wordTrace_append hprefix tailTrace_5258115
  have hstable : (prefixWord ++ tailWord_5258115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258115).length < 2 ^ (prefixWord ++ tailWord_5258115).sum := by decide
  have hdescent : baseEnd_5258115 < baseStart_5258115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258132 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_5258132 : Nat := 118140960795 + 5258132 * 2 ^ 59
def prefixEnd_5258132 : Nat := 4983230072969 + 3 ^ 40 * 5258132 * 2
def baseEnd_5258132 : Nat := 2699949060786926768068297

theorem tailTrace_5258132 : CollatzResearch.WordTrace tailWord_5258132 prefixEnd_5258132 2699949060786926768068297 := by
  unfold tailWord_5258132
  simp only [CollatzResearch.WordTrace]
  refine ⟨95889914693346628147944325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127853219591128837530592433 95889914693346628147944325)
  ·
    refine ⟨17979359005002492777739561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95889914693346628147944325 17979359005002492777739561)
    ·
      refine ⟨13484519253751869583304671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17979359005002492777739561 13484519253751869583304671)
      ·
        refine ⟨20226778880627804374957007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13484519253751869583304671 20226778880627804374957007)
        ·
          refine ⟨30340168320941706562435511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20226778880627804374957007 30340168320941706562435511)
          ·
            refine ⟨45510252481412559843653267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30340168320941706562435511 45510252481412559843653267)
            ·
              refine ⟨68265378722118839765479901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45510252481412559843653267 68265378722118839765479901)
              ·
                refine ⟨25599517020794564912054963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68265378722118839765479901 25599517020794564912054963)
                ·
                  refine ⟨38399275531191847368082445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25599517020794564912054963 38399275531191847368082445)
                  ·
                    refine ⟨14399728324196942763030917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38399275531191847368082445 14399728324196942763030917)
                    ·
                      refine ⟨2699949060786926768068297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14399728324196942763030917 2699949060786926768068297)
                      ·
                        rfl

theorem cell23_5258132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_5258132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258132 prefixEnd_5258132 := by exact prefixLift 5258132
  have htrace : WordTrace (prefixWord ++ tailWord_5258132) baseStart_5258132 baseEnd_5258132 := by
    simpa [prefixWord, tailWord_5258132, baseEnd_5258132] using wordTrace_append hprefix tailTrace_5258132
  have hstable : (prefixWord ++ tailWord_5258132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258132).length < 2 ^ (prefixWord ++ tailWord_5258132).sum := by decide
  have hdescent : baseEnd_5258132 < baseStart_5258132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258210 : List Nat := [3, 3, 3, 1, 1, 1, 4, 2, 1, 4]
def baseStart_5258210 : Nat := 118140960795 + 5258210 * 2 ^ 59
def prefixEnd_5258210 : Nat := 4983230072969 + 3 ^ 40 * 5258210 * 2
def baseEnd_5258210 : Nat := 899996370759325820964313

theorem tailTrace_5258210 : CollatzResearch.WordTrace tailWord_5258210 prefixEnd_5258210 899996370759325820964313 := by
  unfold tailWord_5258210
  simp only [CollatzResearch.WordTrace]
  refine ⟨47945668570102668904307021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127855116186940450411485389 47945668570102668904307021)
  ·
    refine ⟨17979625713788500839115133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47945668570102668904307021 17979625713788500839115133)
    ·
      refine ⟨6742359642670687814668175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17979625713788500839115133 6742359642670687814668175)
      ·
        refine ⟨10113539464006031722002263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6742359642670687814668175 10113539464006031722002263)
        ·
          refine ⟨15170309196009047583003395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10113539464006031722002263 15170309196009047583003395)
          ·
            refine ⟨22755463794013571374505093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15170309196009047583003395 22755463794013571374505093)
            ·
              refine ⟨4266649461377544632719705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22755463794013571374505093 4266649461377544632719705)
              ·
                refine ⟨3199987096033158474539779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4266649461377544632719705 3199987096033158474539779)
                ·
                  refine ⟨4799980644049737711809669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3199987096033158474539779 4799980644049737711809669)
                  ·
                    refine ⟨899996370759325820964313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4799980644049737711809669 899996370759325820964313)
                    ·
                      rfl

theorem cell23_5258210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_5258210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258210 prefixEnd_5258210 := by exact prefixLift 5258210
  have htrace : WordTrace (prefixWord ++ tailWord_5258210) baseStart_5258210 baseEnd_5258210 := by
    simpa [prefixWord, tailWord_5258210, baseEnd_5258210] using wordTrace_append hprefix tailTrace_5258210
  have hstable : (prefixWord ++ tailWord_5258210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258210).length < 2 ^ (prefixWord ++ tailWord_5258210).sum := by decide
  have hdescent : baseEnd_5258210 < baseStart_5258210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258232 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 6, 4]
def baseStart_5258232 : Nat := 118140960795 + 5258232 * 2 ^ 59
def prefixEnd_5258232 : Nat := 4983230072969 + 3 ^ 40 * 5258232 * 2
def baseEnd_5258232 : Nat := 900000136284125458939279

theorem tailTrace_5258232 : CollatzResearch.WordTrace tailWord_5258232 prefixEnd_5258232 900000136284125458939279 := by
  unfold tailWord_5258232
  simp only [CollatzResearch.WordTrace]
  refine ⟨95891738343165486687264475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127855651124220648916352633 95891738343165486687264475)
  ·
    refine ⟨143837607514748230030896713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95891738343165486687264475 143837607514748230030896713)
    ·
      refine ⟨107878205636061172523172535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143837607514748230030896713 107878205636061172523172535)
      ·
        refine ⟨161817308454091758784758803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107878205636061172523172535 161817308454091758784758803)
        ·
          refine ⟨242725962681137638177138205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161817308454091758784758803 242725962681137638177138205)
          ·
            refine ⟨91022236005426614316426827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242725962681137638177138205 91022236005426614316426827)
            ·
              refine ⟨136533354008139921474640241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91022236005426614316426827 136533354008139921474640241)
              ·
                refine ⟨102400015506104941105980181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136533354008139921474640241 102400015506104941105980181)
                ·
                  refine ⟨4800000726848669114342821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 102400015506104941105980181 4800000726848669114342821)
                  ·
                    refine ⟨900000136284125458939279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4800000726848669114342821 900000136284125458939279)
                    ·
                      rfl

theorem cell23_5258232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 6, 4].length) (baseStart_5258232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258232 prefixEnd_5258232 := by exact prefixLift 5258232
  have htrace : WordTrace (prefixWord ++ tailWord_5258232) baseStart_5258232 baseEnd_5258232 := by
    simpa [prefixWord, tailWord_5258232, baseEnd_5258232] using wordTrace_append hprefix tailTrace_5258232
  have hstable : (prefixWord ++ tailWord_5258232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258232).length < 2 ^ (prefixWord ++ tailWord_5258232).sum := by decide
  have hdescent : baseEnd_5258232 < baseStart_5258232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258273 : List Nat := [1, 2, 3, 2, 3, 2, 2, 1, 3, 2, 2]
def baseStart_5258273 : Nat := 118140960795 + 5258273 * 2 ^ 59
def prefixEnd_5258273 : Nat := 4983230072969 + 3 ^ 40 * 5258273 * 2
def baseEnd_5258273 : Nat := 2700021461559210716405149

theorem tailTrace_5258273 : CollatzResearch.WordTrace tailWord_5258273 prefixEnd_5258273 2700021461559210716405149 := by
  unfold tailWord_5258273
  simp only [CollatzResearch.WordTrace]
  refine ⟨191784972079182437376771473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127856648052788291584514315 191784972079182437376771473)
  ·
    refine ⟨143838729059386828032578605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191784972079182437376771473 143838729059386828032578605)
    ·
      refine ⟨53939523397270060512216977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143838729059386828032578605 53939523397270060512216977)
      ·
        refine ⟨40454642547952545384162733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53939523397270060512216977 40454642547952545384162733)
        ·
          refine ⟨15170490955482204519061025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40454642547952545384162733 15170490955482204519061025)
          ·
            refine ⟨11377868216611653389295769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15170490955482204519061025 11377868216611653389295769)
            ·
              refine ⟨8533401162458740041971827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11377868216611653389295769 8533401162458740041971827)
              ·
                refine ⟨12800101743688110062957741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8533401162458740041971827 12800101743688110062957741)
                ·
                  refine ⟨4800038153883041273609153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12800101743688110062957741 4800038153883041273609153)
                  ·
                    refine ⟨3600028615412280955206865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4800038153883041273609153 3600028615412280955206865)
                    ·
                      refine ⟨2700021461559210716405149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3600028615412280955206865 2700021461559210716405149)
                      ·
                        rfl

theorem cell23_5258273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_5258273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258273 prefixEnd_5258273 := by exact prefixLift 5258273
  have htrace : WordTrace (prefixWord ++ tailWord_5258273) baseStart_5258273 baseEnd_5258273 := by
    simpa [prefixWord, tailWord_5258273, baseEnd_5258273] using wordTrace_append hprefix tailTrace_5258273
  have hstable : (prefixWord ++ tailWord_5258273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258273).length < 2 ^ (prefixWord ++ tailWord_5258273).sum := by decide
  have hdescent : baseEnd_5258273 < baseStart_5258273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258329 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 5, 4, 2]
def baseStart_5258329 : Nat := 118140960795 + 5258329 * 2 ^ 59
def prefixEnd_5258329 : Nat := 4983230072969 + 3 ^ 40 * 5258329 * 2
def baseEnd_5258329 : Nat := 2700050216475862497304891

theorem tailTrace_5258329 : CollatzResearch.WordTrace tailWord_5258329 prefixEnd_5258329 2700050216475862497304891 := by
  unfold tailWord_5258329
  simp only [CollatzResearch.WordTrace]
  refine ⟨191787014566979558940810041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127858009711319705960540027 191787014566979558940810041)
  ·
    refine ⟨143840260925234669205607531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191787014566979558940810041 143840260925234669205607531)
    ·
      refine ⟨215760391387852003808411297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143840260925234669205607531 215760391387852003808411297)
      ·
        refine ⟨161820293540889002856308473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215760391387852003808411297 161820293540889002856308473)
        ·
          refine ⟨121365220155666752142231355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161820293540889002856308473 121365220155666752142231355)
          ·
            refine ⟨182047830233500128213347033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121365220155666752142231355 182047830233500128213347033)
            ·
              refine ⟨136535872675125096160010275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182047830233500128213347033 136535872675125096160010275)
              ·
                refine ⟨204803809012687644240015413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136535872675125096160010275 204803809012687644240015413)
                ·
                  refine ⟨19200357094939466647501445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 204803809012687644240015413 19200357094939466647501445)
                  ·
                    refine ⟨3600066955301149996406521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19200357094939466647501445 3600066955301149996406521)
                    ·
                      refine ⟨2700050216475862497304891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3600066955301149996406521 2700050216475862497304891)
                      ·
                        rfl

theorem cell23_5258329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 4, 2].length) (baseStart_5258329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258329 prefixEnd_5258329 := by exact prefixLift 5258329
  have htrace : WordTrace (prefixWord ++ tailWord_5258329) baseStart_5258329 baseEnd_5258329 := by
    simpa [prefixWord, tailWord_5258329, baseEnd_5258329] using wordTrace_append hprefix tailTrace_5258329
  have hstable : (prefixWord ++ tailWord_5258329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258329).length < 2 ^ (prefixWord ++ tailWord_5258329).sum := by decide
  have hdescent : baseEnd_5258329 < baseStart_5258329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258349 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_5258349 : Nat := 118140960795 + 5258349 * 2 ^ 59
def prefixEnd_5258349 : Nat := 4983230072969 + 3 ^ 40 * 5258349 * 2
def baseEnd_5258349 : Nat := 2700060486088952419054799

theorem tailTrace_5258349 : CollatzResearch.WordTrace tailWord_5258349 prefixEnd_5258349 2700060486088952419054799 := by
  unfold tailWord_5258349
  simp only [CollatzResearch.WordTrace]
  refine ⟨191787744026907102356538101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127858496017938068237692067 191787744026907102356538101)
  ·
    refine ⟨17980101002522540845925447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191787744026907102356538101 17980101002522540845925447)
    ·
      refine ⟨26970151503783811268888171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17980101002522540845925447 26970151503783811268888171)
      ·
        refine ⟨40455227255675716903332257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26970151503783811268888171 40455227255675716903332257)
        ·
          refine ⟨30341420441756787677499193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40455227255675716903332257 30341420441756787677499193)
          ·
            refine ⟨22756065331317590758124395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30341420441756787677499193 22756065331317590758124395)
            ·
              refine ⟨34134097996976386137186593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22756065331317590758124395 34134097996976386137186593)
              ·
                refine ⟨25600573497732289602889945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34134097996976386137186593 25600573497732289602889945)
                ·
                  refine ⟨19200430123299217202167459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25600573497732289602889945 19200430123299217202167459)
                  ·
                    refine ⟨28800645184948825803251189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19200430123299217202167459 28800645184948825803251189)
                    ·
                      refine ⟨2700060486088952419054799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28800645184948825803251189 2700060486088952419054799)
                      ·
                        rfl

theorem cell23_5258349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_5258349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258349 prefixEnd_5258349 := by exact prefixLift 5258349
  have htrace : WordTrace (prefixWord ++ tailWord_5258349) baseStart_5258349 baseEnd_5258349 := by
    simpa [prefixWord, tailWord_5258349, baseEnd_5258349] using wordTrace_append hprefix tailTrace_5258349
  have hstable : (prefixWord ++ tailWord_5258349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258349).length < 2 ^ (prefixWord ++ tailWord_5258349).sum := by decide
  have hdescent : baseEnd_5258349 < baseStart_5258349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258350 : List Nat := [4, 1, 2, 2, 1, 4, 1, 2, 1, 3, 2]
def baseStart_5258350 : Nat := 118140960795 + 5258350 * 2 ^ 59
def prefixEnd_5258350 : Nat := 4983230072969 + 3 ^ 40 * 5258350 * 2
def baseEnd_5258350 : Nat := 2700060999569606915142295

theorem tailTrace_5258350 : CollatzResearch.WordTrace tailWord_5258350 prefixEnd_5258350 2700060999569606915142295 := by
  unfold tailWord_5258350
  simp only [CollatzResearch.WordTrace]
  refine ⟨23973472562487934940915563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127858520333268986351549669 23973472562487934940915563)
  ·
    refine ⟨35960208843731902411373345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23973472562487934940915563 35960208843731902411373345)
    ·
      refine ⟨26970156632798926808530009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35960208843731902411373345 26970156632798926808530009)
      ·
        refine ⟨20227617474599195106397507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26970156632798926808530009 20227617474599195106397507)
        ·
          refine ⟨30341426211898792659596261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20227617474599195106397507 30341426211898792659596261)
          ·
            refine ⟨5689017414731023623674299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30341426211898792659596261 5689017414731023623674299)
            ·
              refine ⟨8533526122096535435511449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5689017414731023623674299 8533526122096535435511449)
              ·
                refine ⟨6400144591572401576633587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8533526122096535435511449 6400144591572401576633587)
                ·
                  refine ⟨9600216887358602364950381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6400144591572401576633587 9600216887358602364950381)
                  ·
                    refine ⟨3600081332759475886856393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9600216887358602364950381 3600081332759475886856393)
                    ·
                      refine ⟨2700060999569606915142295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3600081332759475886856393 2700060999569606915142295)
                      ·
                        rfl

theorem cell23_5258350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_5258350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258350 prefixEnd_5258350 := by exact prefixLift 5258350
  have htrace : WordTrace (prefixWord ++ tailWord_5258350) baseStart_5258350 baseEnd_5258350 := by
    simpa [prefixWord, tailWord_5258350, baseEnd_5258350] using wordTrace_append hprefix tailTrace_5258350
  have hstable : (prefixWord ++ tailWord_5258350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258350).length < 2 ^ (prefixWord ++ tailWord_5258350).sum := by decide
  have hdescent : baseEnd_5258350 < baseStart_5258350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258352 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 9]
def baseStart_5258352 : Nat := 118140960795 + 5258352 * 2 ^ 59
def prefixEnd_5258352 : Nat := 4983230072969 + 3 ^ 40 * 5258352 * 2
def baseEnd_5258352 : Nat := 300006891836768434146365

theorem tailTrace_5258352 : CollatzResearch.WordTrace tailWord_5258352 prefixEnd_5258352 300006891836768434146365 := by
  unfold tailWord_5258352
  simp only [CollatzResearch.WordTrace]
  refine ⟨95893926722948116934448655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127858568963930822579264873 95893926722948116934448655)
  ·
    refine ⟨143840890084422175401672983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95893926722948116934448655 143840890084422175401672983)
    ·
      refine ⟨215761335126633263102509475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143840890084422175401672983 215761335126633263102509475)
      ·
        refine ⟨323642002689949894653764213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215761335126633263102509475 323642002689949894653764213)
        ·
          refine ⟨30341437752182802623790395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 323642002689949894653764213 30341437752182802623790395)
          ·
            refine ⟨45512156628274203935685593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30341437752182802623790395 45512156628274203935685593)
            ·
              refine ⟨34134117471205652951764195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45512156628274203935685593 34134117471205652951764195)
              ·
                refine ⟨51201176206808479427646293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34134117471205652951764195 51201176206808479427646293)
                ·
                  refine ⟨300006891836768434146365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51201176206808479427646293 300006891836768434146365)
                  ·
                    rfl

theorem cell23_5258352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 9].length) (baseStart_5258352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258352 prefixEnd_5258352 := by exact prefixLift 5258352
  have htrace : WordTrace (prefixWord ++ tailWord_5258352) baseStart_5258352 baseEnd_5258352 := by
    simpa [prefixWord, tailWord_5258352, baseEnd_5258352] using wordTrace_append hprefix tailTrace_5258352
  have hstable : (prefixWord ++ tailWord_5258352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258352).length < 2 ^ (prefixWord ++ tailWord_5258352).sum := by decide
  have hdescent : baseEnd_5258352 < baseStart_5258352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258396 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 2, 3, 3]
def baseStart_5258396 : Nat := 118140960795 + 5258396 * 2 ^ 59
def prefixEnd_5258396 : Nat := 4983230072969 + 3 ^ 40 * 5258396 * 2
def baseEnd_5258396 : Nat := 2700084619679713735167083

theorem tailTrace_5258396 : CollatzResearch.WordTrace tailWord_5258396 prefixEnd_5258396 2700084619679713735167083 := by
  unfold tailWord_5258396
  simp only [CollatzResearch.WordTrace]
  refine ⟨95894729128868414691749521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127859638838491219588999361 95894729128868414691749521)
  ·
    refine ⟨71921046846651311018812141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95894729128868414691749521 71921046846651311018812141)
    ·
      refine ⟨26970392567494241632054553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71921046846651311018812141 26970392567494241632054553)
      ·
        refine ⟨20227794425620681224040915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26970392567494241632054553 20227794425620681224040915)
        ·
          refine ⟨30341691638431021836061373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20227794425620681224040915 30341691638431021836061373)
          ·
            refine ⟨11378134364411633188523015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30341691638431021836061373 11378134364411633188523015)
            ·
              refine ⟨17067201546617449782784523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11378134364411633188523015 17067201546617449782784523)
              ·
                refine ⟨25600802319926174674176785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17067201546617449782784523 25600802319926174674176785)
                ·
                  refine ⟨19200601739944631005632589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25600802319926174674176785 19200601739944631005632589)
                  ·
                    refine ⟨7200225652479236627112221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19200601739944631005632589 7200225652479236627112221)
                    ·
                      refine ⟨2700084619679713735167083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7200225652479236627112221 2700084619679713735167083)
                      ·
                        rfl

theorem cell23_5258396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_5258396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258396 prefixEnd_5258396 := by exact prefixLift 5258396
  have htrace : WordTrace (prefixWord ++ tailWord_5258396) baseStart_5258396 baseEnd_5258396 := by
    simpa [prefixWord, tailWord_5258396, baseEnd_5258396] using wordTrace_append hprefix tailTrace_5258396
  have hstable : (prefixWord ++ tailWord_5258396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258396).length < 2 ^ (prefixWord ++ tailWord_5258396).sum := by decide
  have hdescent : baseEnd_5258396 < baseStart_5258396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258412 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 1, 10]
def baseStart_5258412 : Nat := 118140960795 + 5258412 * 2 ^ 59
def prefixEnd_5258412 : Nat := 4983230072969 + 3 ^ 40 * 5258412 * 2
def baseEnd_5258412 : Nat := 900030945123395224189003

theorem tailTrace_5258412 : CollatzResearch.WordTrace tailWord_5258412 prefixEnd_5258412 900030945123395224189003 := by
  unfold tailWord_5258412
  simp only [CollatzResearch.WordTrace]
  refine ⟨95895020912839432058040745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127860027883785909410720993 95895020912839432058040745)
  ·
    refine ⟨71921265684629574043530559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95895020912839432058040745 71921265684629574043530559)
    ·
      refine ⟨107881898526944361065295839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71921265684629574043530559 107881898526944361065295839)
      ·
        refine ⟨161822847790416541597943759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107881898526944361065295839 161822847790416541597943759)
        ·
          refine ⟨242734271685624812396915639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161822847790416541597943759 242734271685624812396915639)
          ·
            refine ⟨364101407528437218595373459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242734271685624812396915639 364101407528437218595373459)
            ·
              refine ⟨546152111292655827893060189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364101407528437218595373459 546152111292655827893060189)
              ·
                refine ⟨204807041734745935459897571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 546152111292655827893060189 204807041734745935459897571)
                ·
                  refine ⟨307210562602118903189846357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204807041734745935459897571 307210562602118903189846357)
                  ·
                    refine ⟨900030945123395224189003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 307210562602118903189846357 900030945123395224189003)
                    ·
                      rfl

theorem cell23_5258412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_5258412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258412 prefixEnd_5258412 := by exact prefixLift 5258412
  have htrace : WordTrace (prefixWord ++ tailWord_5258412) baseStart_5258412 baseEnd_5258412 := by
    simpa [prefixWord, tailWord_5258412, baseEnd_5258412] using wordTrace_append hprefix tailTrace_5258412
  have hstable : (prefixWord ++ tailWord_5258412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258412).length < 2 ^ (prefixWord ++ tailWord_5258412).sum := by decide
  have hdescent : baseEnd_5258412 < baseStart_5258412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258453 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 2, 4, 2]
def baseStart_5258453 : Nat := 118140960795 + 5258453 * 2 ^ 59
def prefixEnd_5258453 : Nat := 4983230072969 + 3 ^ 40 * 5258453 * 2
def baseEnd_5258453 : Nat := 2700113888077020012154321

theorem tailTrace_5258453 : CollatzResearch.WordTrace tailWord_5258453 prefixEnd_5258453 2700113888077020012154321 := by
  unfold tailWord_5258453
  simp only [CollatzResearch.WordTrace]
  refine ⟨191791537218530328118324013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127861024812353552078882675 191791537218530328118324013)
  ·
    refine ⟨71921826456948873044371505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191791537218530328118324013 71921826456948873044371505)
    ·
      refine ⟨53941369842711654783278629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71921826456948873044371505 53941369842711654783278629)
      ·
        refine ⟨10114006845508435271864743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53941369842711654783278629 10114006845508435271864743)
        ·
          refine ⟨15171010268262652907797115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10114006845508435271864743 15171010268262652907797115)
          ·
            refine ⟨22756515402393979361695673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15171010268262652907797115 22756515402393979361695673)
            ·
              refine ⟨17067386551795484521271755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22756515402393979361695673 17067386551795484521271755)
              ·
                refine ⟨25601079827693226781907633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17067386551795484521271755 25601079827693226781907633)
                ·
                  refine ⟨19200809870769920086430725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25601079827693226781907633 19200809870769920086430725)
                  ·
                    refine ⟨3600151850769360016205761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19200809870769920086430725 3600151850769360016205761)
                    ·
                      refine ⟨2700113888077020012154321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3600151850769360016205761 2700113888077020012154321)
                      ·
                        rfl

theorem cell23_5258453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_5258453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258453 prefixEnd_5258453 := by exact prefixLift 5258453
  have htrace : WordTrace (prefixWord ++ tailWord_5258453) baseStart_5258453 baseEnd_5258453 := by
    simpa [prefixWord, tailWord_5258453, baseEnd_5258453] using wordTrace_append hprefix tailTrace_5258453
  have hstable : (prefixWord ++ tailWord_5258453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258453).length < 2 ^ (prefixWord ++ tailWord_5258453).sum := by decide
  have hdescent : baseEnd_5258453 < baseStart_5258453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258536 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 3, 6]
def baseStart_5258536 : Nat := 118140960795 + 5258536 * 2 ^ 59
def prefixEnd_5258536 : Nat := 4983230072969 + 3 ^ 40 * 5258536 * 2
def baseEnd_5258536 : Nat := 900052168990447729138813

theorem tailTrace_5258536 : CollatzResearch.WordTrace tailWord_5258536 prefixEnd_5258536 900052168990447729138813 := by
  unfold tailWord_5258536
  simp only [CollatzResearch.WordTrace]
  refine ⟨95897282238614816646797731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127863042984819755529063641 95897282238614816646797731)
  ·
    refine ⟨143845923357922224970196597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95897282238614816646797731 143845923357922224970196597)
    ·
      refine ⟨13485555314805208590955931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143845923357922224970196597 13485555314805208590955931)
      ·
        refine ⟨20228332972207812886433897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13485555314805208590955931 20228332972207812886433897)
        ·
          refine ⟨15171249729155859664825423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20228332972207812886433897 15171249729155859664825423)
          ·
            refine ⟨22756874593733789497238135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15171249729155859664825423 22756874593733789497238135)
            ·
              refine ⟨34135311890600684245857203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22756874593733789497238135 34135311890600684245857203)
              ·
                refine ⟨51202967835901026368785805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34135311890600684245857203 51202967835901026368785805)
                ·
                  refine ⟨19201112938462884888294677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51202967835901026368785805 19201112938462884888294677)
                  ·
                    refine ⟨900052168990447729138813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19201112938462884888294677 900052168990447729138813)
                    ·
                      rfl

theorem cell23_5258536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_5258536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258536 prefixEnd_5258536 := by exact prefixLift 5258536
  have htrace : WordTrace (prefixWord ++ tailWord_5258536) baseStart_5258536 baseEnd_5258536 := by
    simpa [prefixWord, tailWord_5258536, baseEnd_5258536] using wordTrace_append hprefix tailTrace_5258536
  have hstable : (prefixWord ++ tailWord_5258536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258536).length < 2 ^ (prefixWord ++ tailWord_5258536).sum := by decide
  have hdescent : baseEnd_5258536 < baseStart_5258536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258549 : List Nat := [1, 3, 3, 1, 2, 13]
def baseStart_5258549 : Nat := 118140960795 + 5258549 * 2 ^ 59
def prefixEnd_5258549 : Nat := 4983230072969 + 3 ^ 40 * 5258549 * 2
def baseEnd_5258549 : Nat := 11111782642880047887053

theorem tailTrace_5258549 : CollatzResearch.WordTrace tailWord_5258549 prefixEnd_5258549 11111782642880047887053 := by
  unfold tailWord_5258549
  simp only [CollatzResearch.WordTrace]
  refine ⟨191795038626182536513818701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127863359084121691009212467 191795038626182536513818701)
  ·
    refine ⟨71923139484818451192682013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191795038626182536513818701 71923139484818451192682013)
    ·
      refine ⟨26971177306806919197255755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71923139484818451192682013 26971177306806919197255755)
      ·
        refine ⟨40456765960210378795883633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26971177306806919197255755 40456765960210378795883633)
        ·
          refine ⟨30342574470157784096912725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40456765960210378795883633 30342574470157784096912725)
          ·
            refine ⟨11111782642880047887053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 30342574470157784096912725 11111782642880047887053)
            ·
              rfl

theorem cell23_5258549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 13].length) (baseStart_5258549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258549 prefixEnd_5258549 := by exact prefixLift 5258549
  have htrace : WordTrace (prefixWord ++ tailWord_5258549) baseStart_5258549 baseEnd_5258549 := by
    simpa [prefixWord, tailWord_5258549, baseEnd_5258549] using wordTrace_append hprefix tailTrace_5258549
  have hstable : (prefixWord ++ tailWord_5258549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258549).length < 2 ^ (prefixWord ++ tailWord_5258549).sum := by decide
  have hdescent : baseEnd_5258549 < baseStart_5258549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258569 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 2, 2, 6]
def baseStart_5258569 : Nat := 118140960795 + 5258569 * 2 ^ 59
def prefixEnd_5258569 : Nat := 4983230072969 + 3 ^ 40 * 5258569 * 2
def baseEnd_5258569 : Nat := 2700173451832941558303787

theorem tailTrace_5258569 : CollatzResearch.WordTrace tailWord_5258569 prefixEnd_5258569 2700173451832941558303787 := by
  unfold tailWord_5258569
  simp only [CollatzResearch.WordTrace]
  refine ⟨191795768086110079929546761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127863845390740053286364507 191795768086110079929546761)
  ·
    refine ⟨143846826064582559947160071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191795768086110079929546761 143846826064582559947160071)
    ·
      refine ⟨215770239096873839920740107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143846826064582559947160071 215770239096873839920740107)
      ·
        refine ⟨323655358645310759881110161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215770239096873839920740107 323655358645310759881110161)
        ·
          refine ⟨242741518983983069910832621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323655358645310759881110161 242741518983983069910832621)
          ·
            refine ⟨91028069618993651216562233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242741518983983069910832621 91028069618993651216562233)
            ·
              refine ⟨68271052214245238412421675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91028069618993651216562233 68271052214245238412421675)
              ·
                refine ⟨102406578321367857618632513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68271052214245238412421675 102406578321367857618632513)
                ·
                  refine ⟨76804933741025893213974385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102406578321367857618632513 76804933741025893213974385)
                  ·
                    refine ⟨57603700305769419910480789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76804933741025893213974385 57603700305769419910480789)
                    ·
                      refine ⟨2700173451832941558303787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57603700305769419910480789 2700173451832941558303787)
                      ·
                        rfl

theorem cell23_5258569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_5258569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258569 prefixEnd_5258569 := by exact prefixLift 5258569
  have htrace : WordTrace (prefixWord ++ tailWord_5258569) baseStart_5258569 baseEnd_5258569 := by
    simpa [prefixWord, tailWord_5258569, baseEnd_5258569] using wordTrace_append hprefix tailTrace_5258569
  have hstable : (prefixWord ++ tailWord_5258569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258569).length < 2 ^ (prefixWord ++ tailWord_5258569).sum := by decide
  have hdescent : baseEnd_5258569 < baseStart_5258569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258579 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 2, 7]
def baseStart_5258579 : Nat := 118140960795 + 5258579 * 2 ^ 59
def prefixEnd_5258579 : Nat := 4983230072969 + 3 ^ 40 * 5258579 * 2
def baseEnd_5258579 : Nat := 900059528879828839726247

theorem tailTrace_5258579 : CollatzResearch.WordTrace tailWord_5258579 prefixEnd_5258579 900059528879828839726247 := by
  unfold tailWord_5258579
  simp only [CollatzResearch.WordTrace]
  refine ⟨191796132816073851637410791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127864088544049234424940527 191796132816073851637410791)
  ·
    refine ⟨287694199224110777456116187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191796132816073851637410791 287694199224110777456116187)
    ·
      refine ⟨431541298836166166184174281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287694199224110777456116187 431541298836166166184174281)
      ·
        refine ⟨323655974127124624638130711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 431541298836166166184174281 323655974127124624638130711)
        ·
          refine ⟨485483961190686936957196067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323655974127124624638130711 485483961190686936957196067)
          ·
            refine ⟨728225941786030405435794101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485483961190686936957196067 728225941786030405435794101)
            ·
              refine ⟨68271182042440350509605697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 728225941786030405435794101 68271182042440350509605697)
              ·
                refine ⟨51203386531830262882204273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68271182042440350509605697 51203386531830262882204273)
                ·
                  refine ⟨38402539898872697161653205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51203386531830262882204273 38402539898872697161653205)
                  ·
                    refine ⟨900059528879828839726247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38402539898872697161653205 900059528879828839726247)
                    ·
                      rfl

theorem cell23_5258579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 7].length) (baseStart_5258579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258579 prefixEnd_5258579 := by exact prefixLift 5258579
  have htrace : WordTrace (prefixWord ++ tailWord_5258579) baseStart_5258579 baseEnd_5258579 := by
    simpa [prefixWord, tailWord_5258579, baseEnd_5258579] using wordTrace_append hprefix tailTrace_5258579
  have hstable : (prefixWord ++ tailWord_5258579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258579).length < 2 ^ (prefixWord ++ tailWord_5258579).sum := by decide
  have hdescent : baseEnd_5258579 < baseStart_5258579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258594 : List Nat := [3, 3, 2, 1, 1, 1, 4, 3, 1, 2, 2]
def baseStart_5258594 : Nat := 118140960795 + 5258594 * 2 ^ 59
def prefixEnd_5258594 : Nat := 4983230072969 + 3 ^ 40 * 5258594 * 2
def baseEnd_5258594 : Nat := 2700186288849303960491173

theorem tailTrace_5258594 : CollatzResearch.WordTrace tailWord_5258594 prefixEnd_5258594 2700186288849303960491173 := by
  unfold tailWord_5258594
  simp only [CollatzResearch.WordTrace]
  refine ⟨47949169977754877299801709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127864453274013006132804557 47949169977754877299801709)
  ·
    refine ⟨17980938741658078987425641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47949169977754877299801709 17980938741658078987425641)
    ·
      refine ⟨13485704056243559240569231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17980938741658078987425641 13485704056243559240569231)
      ·
        refine ⟨20228556084365338860853847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13485704056243559240569231 20228556084365338860853847)
        ·
          refine ⟨30342834126548008291280771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20228556084365338860853847 30342834126548008291280771)
          ·
            refine ⟨45514251189822012436921157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30342834126548008291280771 45514251189822012436921157)
            ·
              refine ⟨8533922098091627331922717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45514251189822012436921157 8533922098091627331922717)
              ·
                refine ⟨3200220786784360249471019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8533922098091627331922717 3200220786784360249471019)
                ·
                  refine ⟨4800331180176540374206529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3200220786784360249471019 4800331180176540374206529)
                  ·
                    refine ⟨3600248385132405280654897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4800331180176540374206529 3600248385132405280654897)
                    ·
                      refine ⟨2700186288849303960491173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3600248385132405280654897 2700186288849303960491173)
                      ·
                        rfl

theorem cell23_5258594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_5258594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258594 prefixEnd_5258594 := by exact prefixLift 5258594
  have htrace : WordTrace (prefixWord ++ tailWord_5258594) baseStart_5258594 baseEnd_5258594 := by
    simpa [prefixWord, tailWord_5258594, baseEnd_5258594] using wordTrace_append hprefix tailTrace_5258594
  have hstable : (prefixWord ++ tailWord_5258594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258594).length < 2 ^ (prefixWord ++ tailWord_5258594).sum := by decide
  have hdescent : baseEnd_5258594 < baseStart_5258594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258627 : List Nat := [1, 1, 1, 3, 5, 2, 3, 1, 2, 1, 3]
def baseStart_5258627 : Nat := 118140960795 + 5258627 * 2 ^ 59
def prefixEnd_5258627 : Nat := 4983230072969 + 3 ^ 40 * 5258627 * 2
def baseEnd_5258627 : Nat := 2700203233710902331378521

theorem tailTrace_5258627 : CollatzResearch.WordTrace tailWord_5258627 prefixEnd_5258627 2700203233710902331378521 := by
  unfold tailWord_5258627
  simp only [CollatzResearch.WordTrace]
  refine ⟨191797883519899955835158135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127865255679933303890105423 191797883519899955835158135)
  ·
    refine ⟨287696825279849933752737203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191797883519899955835158135 287696825279849933752737203)
    ·
      refine ⟨431545237919774900629105805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287696825279849933752737203 431545237919774900629105805)
      ·
        refine ⟨161829464219915587735914677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 431545237919774900629105805 161829464219915587735914677)
        ·
          refine ⟨15171512270617086350242001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 161829464219915587735914677 15171512270617086350242001)
          ·
            refine ⟨11378634202962814762681501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15171512270617086350242001 11378634202962814762681501)
            ·
              refine ⟨4266987826111055536005563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11378634202962814762681501 4266987826111055536005563)
              ·
                refine ⟨6400481739166583304008345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4266987826111055536005563 6400481739166583304008345)
                ·
                  refine ⟨4800361304374937478006259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6400481739166583304008345 4800361304374937478006259)
                  ·
                    refine ⟨7200541956562406217009389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4800361304374937478006259 7200541956562406217009389)
                    ·
                      refine ⟨2700203233710902331378521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7200541956562406217009389 2700203233710902331378521)
                      ·
                        rfl

theorem cell23_5258627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 2, 1, 3].length) (baseStart_5258627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258627 prefixEnd_5258627 := by exact prefixLift 5258627
  have htrace : WordTrace (prefixWord ++ tailWord_5258627) baseStart_5258627 baseEnd_5258627 := by
    simpa [prefixWord, tailWord_5258627, baseEnd_5258627] using wordTrace_append hprefix tailTrace_5258627
  have hstable : (prefixWord ++ tailWord_5258627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258627).length < 2 ^ (prefixWord ++ tailWord_5258627).sum := by decide
  have hdescent : baseEnd_5258627 < baseStart_5258627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258636 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 2, 1, 5]
def baseStart_5258636 : Nat := 118140960795 + 5258636 * 2 ^ 59
def prefixEnd_5258636 : Nat := 4983230072969 + 3 ^ 40 * 5258636 * 2
def baseEnd_5258636 : Nat := 2700207855036792796165979

theorem tailTrace_5258636 : CollatzResearch.WordTrace tailWord_5258636 prefixEnd_5258636 2700207855036792796165979 := by
  unfold tailWord_5258636
  simp only [CollatzResearch.WordTrace]
  refine ⟨95899105888433675186117881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127865474517911566914823841 95899105888433675186117881)
  ·
    refine ⟨71924329416325256389588411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95899105888433675186117881 71924329416325256389588411)
    ·
      refine ⟨107886494124487884584382617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71924329416325256389588411 107886494124487884584382617)
      ·
        refine ⟨80914870593365913438286963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107886494124487884584382617 80914870593365913438286963)
        ·
          refine ⟨121372305890048870157430445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80914870593365913438286963 121372305890048870157430445)
          ·
            refine ⟨45514614708768326309036417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121372305890048870157430445 45514614708768326309036417)
            ·
              refine ⟨34135961031576244731777313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45514614708768326309036417 34135961031576244731777313)
              ·
                refine ⟨25601970773682183548832985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34135961031576244731777313 25601970773682183548832985)
                ·
                  refine ⟨19201478080261637661624739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25601970773682183548832985 19201478080261637661624739)
                  ·
                    refine ⟨28802217120392456492437109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19201478080261637661624739 28802217120392456492437109)
                    ·
                      refine ⟨2700207855036792796165979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28802217120392456492437109 2700207855036792796165979)
                      ·
                        rfl

theorem cell23_5258636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_5258636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258636 prefixEnd_5258636 := by exact prefixLift 5258636
  have htrace : WordTrace (prefixWord ++ tailWord_5258636) baseStart_5258636 baseEnd_5258636 := by
    simpa [prefixWord, tailWord_5258636, baseEnd_5258636] using wordTrace_append hprefix tailTrace_5258636
  have hstable : (prefixWord ++ tailWord_5258636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258636).length < 2 ^ (prefixWord ++ tailWord_5258636).sum := by decide
  have hdescent : baseEnd_5258636 < baseStart_5258636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258650 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2]
def baseStart_5258650 : Nat := 118140960795 + 5258650 * 2 ^ 59
def prefixEnd_5258650 : Nat := 4983230072969 + 3 ^ 40 * 5258650 * 2
def baseEnd_5258650 : Nat := 2700215043765955741390915

theorem tailTrace_5258650 : CollatzResearch.WordTrace tailWord_5258650 prefixEnd_5258650 2700215043765955741390915 := by
  unfold tailWord_5258650
  simp only [CollatzResearch.WordTrace]
  refine ⟨47949680599704157690811351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127865814932544420508830269 47949680599704157690811351)
  ·
    refine ⟨71924520899556236536217027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47949680599704157690811351 71924520899556236536217027)
    ·
      refine ⟨107886781349334354804325541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71924520899556236536217027 107886781349334354804325541)
      ·
        refine ⟨20228771503000191525811039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107886781349334354804325541 20228771503000191525811039)
        ·
          refine ⟨30343157254500287288716559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20228771503000191525811039 30343157254500287288716559)
          ·
            refine ⟨45514735881750430933074839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30343157254500287288716559 45514735881750430933074839)
            ·
              refine ⟨68272103822625646399612259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45514735881750430933074839 68272103822625646399612259)
              ·
                refine ⟨102408155733938469599418389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68272103822625646399612259 102408155733938469599418389)
                ·
                  refine ⟨4800382300028365762472737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 102408155733938469599418389 4800382300028365762472737)
                  ·
                    refine ⟨3600286725021274321854553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4800382300028365762472737 3600286725021274321854553)
                    ·
                      refine ⟨2700215043765955741390915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3600286725021274321854553 2700215043765955741390915)
                      ·
                        rfl

theorem cell23_5258650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_5258650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258650 prefixEnd_5258650 := by exact prefixLift 5258650
  have htrace : WordTrace (prefixWord ++ tailWord_5258650) baseStart_5258650 baseEnd_5258650 := by
    simpa [prefixWord, tailWord_5258650, baseEnd_5258650] using wordTrace_append hprefix tailTrace_5258650
  have hstable : (prefixWord ++ tailWord_5258650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258650).length < 2 ^ (prefixWord ++ tailWord_5258650).sum := by decide
  have hdescent : baseEnd_5258650 < baseStart_5258650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258653 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_5258653 : Nat := 118140960795 + 5258653 * 2 ^ 59
def prefixEnd_5258653 : Nat := 4983230072969 + 3 ^ 40 * 5258653 * 2
def baseEnd_5258653 : Nat := 2700216584207919229653401

theorem tailTrace_5258653 : CollatzResearch.WordTrace tailWord_5258653 prefixEnd_5258653 2700216584207919229653401 := by
  unfold tailWord_5258653
  simp only [CollatzResearch.WordTrace]
  refine ⟨191798831817805762275604613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127865887878537174850403075 191798831817805762275604613)
  ·
    refine ⟨35962280965838580426675865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191798831817805762275604613 35962280965838580426675865)
    ·
      refine ⟨26971710724378935320006899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35962280965838580426675865 26971710724378935320006899)
      ·
        refine ⟨40457566086568402980010349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26971710724378935320006899 40457566086568402980010349)
        ·
          refine ⟨15171587282463151117503881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40457566086568402980010349 15171587282463151117503881)
          ·
            refine ⟨11378690461847363338127911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15171587282463151117503881 11378690461847363338127911)
            ·
              refine ⟨17068035692771045007191867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11378690461847363338127911 17068035692771045007191867)
              ·
                refine ⟨25602053539156567510787801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17068035692771045007191867 25602053539156567510787801)
                ·
                  refine ⟨19201540154367425633090851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25602053539156567510787801 19201540154367425633090851)
                  ·
                    refine ⟨28802310231551138449636277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19201540154367425633090851 28802310231551138449636277)
                    ·
                      refine ⟨2700216584207919229653401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28802310231551138449636277 2700216584207919229653401)
                      ·
                        rfl

theorem cell23_5258653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_5258653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258653 prefixEnd_5258653 := by exact prefixLift 5258653
  have htrace : WordTrace (prefixWord ++ tailWord_5258653) baseStart_5258653 baseEnd_5258653 := by
    simpa [prefixWord, tailWord_5258653, baseEnd_5258653] using wordTrace_append hprefix tailTrace_5258653
  have hstable : (prefixWord ++ tailWord_5258653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258653).length < 2 ^ (prefixWord ++ tailWord_5258653).sum := by decide
  have hdescent : baseEnd_5258653 < baseStart_5258653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258684 : List Nat := [2, 2, 2, 4, 2, 1, 1, 3, 2, 2, 2]
def baseStart_5258684 : Nat := 118140960795 + 5258684 * 2 ^ 59
def prefixEnd_5258684 : Nat := 4983230072969 + 3 ^ 40 * 5258684 * 2
def baseEnd_5258684 : Nat := 2700232502108208608365759

theorem tailTrace_5258684 : CollatzResearch.WordTrace tailWord_5258684 prefixEnd_5258684 2700232502108208608365759 := by
  unfold tailWord_5258684
  simp only [CollatzResearch.WordTrace]
  refine ⟨95899981240346727284991553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127866641653795636379988737 95899981240346727284991553)
  ·
    refine ⟨71924985930260045463743665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95899981240346727284991553 71924985930260045463743665)
    ·
      refine ⟨53943739447695034097807749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71924985930260045463743665 53943739447695034097807749)
      ·
        refine ⟨10114451146442818893338953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53943739447695034097807749 10114451146442818893338953)
        ·
          refine ⟨7585838359832114170004215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10114451146442818893338953 7585838359832114170004215)
          ·
            refine ⟨11378757539748171255006323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7585838359832114170004215 11378757539748171255006323)
            ·
              refine ⟨17068136309622256882509485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11378757539748171255006323 17068136309622256882509485)
              ·
                refine ⟨6400551116108346330941057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17068136309622256882509485 6400551116108346330941057)
                ·
                  refine ⟨4800413337081259748205793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6400551116108346330941057 4800413337081259748205793)
                  ·
                    refine ⟨3600310002810944811154345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4800413337081259748205793 3600310002810944811154345)
                    ·
                      refine ⟨2700232502108208608365759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3600310002810944811154345 2700232502108208608365759)
                      ·
                        rfl

theorem cell23_5258684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_5258684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258684 prefixEnd_5258684 := by exact prefixLift 5258684
  have htrace : WordTrace (prefixWord ++ tailWord_5258684) baseStart_5258684 baseEnd_5258684 := by
    simpa [prefixWord, tailWord_5258684, baseEnd_5258684] using wordTrace_append hprefix tailTrace_5258684
  have hstable : (prefixWord ++ tailWord_5258684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258684).length < 2 ^ (prefixWord ++ tailWord_5258684).sum := by decide
  have hdescent : baseEnd_5258684 < baseStart_5258684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258696 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 1, 1, 7]
def baseStart_5258696 : Nat := 118140960795 + 5258696 * 2 ^ 59
def prefixEnd_5258696 : Nat := 4983230072969 + 3 ^ 40 * 5258696 * 2
def baseEnd_5258696 : Nat := 2700238663876062561415703

theorem tailTrace_5258696 : CollatzResearch.WordTrace tailWord_5258696 prefixEnd_5258696 2700238663876062561415703 := by
  unfold tailWord_5258696
  simp only [CollatzResearch.WordTrace]
  refine ⟨95900200078324990309709971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127866933437766653746279961 95900200078324990309709971)
  ·
    refine ⟨143850300117487485464564957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95900200078324990309709971 143850300117487485464564957)
    ·
      refine ⟨53943862544057807049211859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143850300117487485464564957 53943862544057807049211859)
      ·
        refine ⟨80915793816086710573817789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53943862544057807049211859 80915793816086710573817789)
        ·
          refine ⟨30343422681032516465181671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80915793816086710573817789 30343422681032516465181671)
          ·
            refine ⟨45515134021548774697772507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30343422681032516465181671 45515134021548774697772507)
            ·
              refine ⟨68272701032323162046658761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45515134021548774697772507 68272701032323162046658761)
              ·
                refine ⟨51204525774242371534994071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68272701032323162046658761 51204525774242371534994071)
                ·
                  refine ⟨76806788661363557302491107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51204525774242371534994071 76806788661363557302491107)
                  ·
                    refine ⟨115210182992045335953736661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76806788661363557302491107 115210182992045335953736661)
                    ·
                      refine ⟨2700238663876062561415703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115210182992045335953736661 2700238663876062561415703)
                      ·
                        rfl

theorem cell23_5258696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_5258696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258696 prefixEnd_5258696 := by exact prefixLift 5258696
  have htrace : WordTrace (prefixWord ++ tailWord_5258696) baseStart_5258696 baseEnd_5258696 := by
    simpa [prefixWord, tailWord_5258696, baseEnd_5258696] using wordTrace_append hprefix tailTrace_5258696
  have hstable : (prefixWord ++ tailWord_5258696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258696).length < 2 ^ (prefixWord ++ tailWord_5258696).sum := by decide
  have hdescent : baseEnd_5258696 < baseStart_5258696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258760 : List Nat := [2, 1, 3, 2, 1, 1, 5, 1, 2, 2, 3]
def baseStart_5258760 : Nat := 118140960795 + 5258760 * 2 ^ 59
def prefixEnd_5258760 : Nat := 4983230072969 + 3 ^ 40 * 5258760 * 2
def baseEnd_5258760 : Nat := 2700271526637950311015409

theorem tailTrace_5258760 : CollatzResearch.WordTrace tailWord_5258760 prefixEnd_5258760 2700271526637950311015409 := by
  unfold tailWord_5258760
  simp only [CollatzResearch.WordTrace]
  refine ⟨95901367214209059774874867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127868489618945413033166489 95901367214209059774874867)
  ·
    refine ⟨143852050821313589662312301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95901367214209059774874867 143852050821313589662312301)
    ·
      refine ⟨53944519057992596123367113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143852050821313589662312301 53944519057992596123367113)
      ·
        refine ⟨40458389293494447092525335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53944519057992596123367113 40458389293494447092525335)
        ·
          refine ⟨60687583940241670638788003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40458389293494447092525335 60687583940241670638788003)
          ·
            refine ⟨91031375910362505958182005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60687583940241670638788003 91031375910362505958182005)
            ·
              refine ⟨8534191491596484933579563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91031375910362505958182005 8534191491596484933579563)
              ·
                refine ⟨12801287237394727400369345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8534191491596484933579563 12801287237394727400369345)
                ·
                  refine ⟨9600965428046045550277009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12801287237394727400369345 9600965428046045550277009)
                  ·
                    refine ⟨7200724071034534162707757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9600965428046045550277009 7200724071034534162707757)
                    ·
                      refine ⟨2700271526637950311015409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7200724071034534162707757 2700271526637950311015409)
                      ·
                        rfl

theorem cell23_5258760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_5258760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258760 prefixEnd_5258760 := by exact prefixLift 5258760
  have htrace : WordTrace (prefixWord ++ tailWord_5258760) baseStart_5258760 baseEnd_5258760 := by
    simpa [prefixWord, tailWord_5258760, baseEnd_5258760] using wordTrace_append hprefix tailTrace_5258760
  have hstable : (prefixWord ++ tailWord_5258760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258760).length < 2 ^ (prefixWord ++ tailWord_5258760).sum := by decide
  have hdescent : baseEnd_5258760 < baseStart_5258760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258810 : List Nat := [3, 1, 1, 1, 3, 2, 4, 2, 1, 5]
def baseStart_5258810 : Nat := 118140960795 + 5258810 * 2 ^ 59
def prefixEnd_5258810 : Nat := 4983230072969 + 3 ^ 40 * 5258810 * 2
def baseEnd_5258810 : Nat := 900099066890225038463393

theorem tailTrace_5258810 : CollatzResearch.WordTrace tailWord_5258810 prefixEnd_5258810 900099066890225038463393 := by
  unfold tailWord_5258810
  simp only [CollatzResearch.WordTrace]
  refine ⟨47951139519559244522267471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127869705385491318726046589 47951139519559244522267471)
  ·
    refine ⟨71926709279338866783401207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47951139519559244522267471 71926709279338866783401207)
    ·
      refine ⟨107890063919008300175101811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71926709279338866783401207 107890063919008300175101811)
      ·
        refine ⟨161835095878512450262652717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107890063919008300175101811 161835095878512450262652717)
        ·
          refine ⟨60688160954442168848494769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161835095878512450262652717 60688160954442168848494769)
          ·
            refine ⟨45516120715831626636371077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60688160954442168848494769 45516120715831626636371077)
            ·
              refine ⟨8534272634218429994319577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45516120715831626636371077 8534272634218429994319577)
              ·
                refine ⟨6400704475663822495739683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8534272634218429994319577 6400704475663822495739683)
                ·
                  refine ⟨9601056713495733743609525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6400704475663822495739683 9601056713495733743609525)
                  ·
                    refine ⟨900099066890225038463393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9601056713495733743609525 900099066890225038463393)
                    ·
                      rfl

theorem cell23_5258810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 1, 5].length) (baseStart_5258810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258810 prefixEnd_5258810 := by exact prefixLift 5258810
  have htrace : WordTrace (prefixWord ++ tailWord_5258810) baseStart_5258810 baseEnd_5258810 := by
    simpa [prefixWord, tailWord_5258810, baseEnd_5258810] using wordTrace_append hprefix tailTrace_5258810
  have hstable : (prefixWord ++ tailWord_5258810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258810).length < 2 ^ (prefixWord ++ tailWord_5258810).sum := by decide
  have hdescent : baseEnd_5258810 < baseStart_5258810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258817 : List Nat := [1, 2, 5, 1, 1, 1, 2, 3, 2, 3, 2]
def baseStart_5258817 : Nat := 118140960795 + 5258817 * 2 ^ 59
def prefixEnd_5258817 : Nat := 4983230072969 + 3 ^ 40 * 5258817 * 2
def baseEnd_5258817 : Nat := 2700300795035256588002647

theorem tailTrace_5258817 : CollatzResearch.WordTrace tailWord_5258817 prefixEnd_5258817 2700300795035256588002647 := by
  unfold tailWord_5258817
  simp only [CollatzResearch.WordTrace]
  refine ⟨191804813389211618284574705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127869875592807745523049803 191804813389211618284574705)
  ·
    refine ⟨143853610041908713713431029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191804813389211618284574705 143853610041908713713431029)
    ·
      refine ⟨13486275941428941910634159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143853610041908713713431029 13486275941428941910634159)
      ·
        refine ⟨20229413912143412865951239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13486275941428941910634159 20229413912143412865951239)
        ·
          refine ⟨30344120868215119298926859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20229413912143412865951239 30344120868215119298926859)
          ·
            refine ⟨45516181302322678948390289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30344120868215119298926859 45516181302322678948390289)
            ·
              refine ⟨34137135976742009211292717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45516181302322678948390289 34137135976742009211292717)
              ·
                refine ⟨12801425991278253454234769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34137135976742009211292717 12801425991278253454234769)
                ·
                  refine ⟨9601069493458690090676077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12801425991278253454234769 9601069493458690090676077)
                  ·
                    refine ⟨3600401060047008784003529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9601069493458690090676077 3600401060047008784003529)
                    ·
                      refine ⟨2700300795035256588002647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3600401060047008784003529 2700300795035256588002647)
                      ·
                        rfl

theorem cell23_5258817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_5258817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258817 prefixEnd_5258817 := by exact prefixLift 5258817
  have htrace : WordTrace (prefixWord ++ tailWord_5258817) baseStart_5258817 baseEnd_5258817 := by
    simpa [prefixWord, tailWord_5258817, baseEnd_5258817] using wordTrace_append hprefix tailTrace_5258817
  have hstable : (prefixWord ++ tailWord_5258817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258817).length < 2 ^ (prefixWord ++ tailWord_5258817).sum := by decide
  have hdescent : baseEnd_5258817 < baseStart_5258817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258840 : List Nat := [2, 1, 2, 2, 1, 2, 1, 6, 2, 4]
def baseStart_5258840 : Nat := 118140960795 + 5258840 * 2 ^ 59
def prefixEnd_5258840 : Nat := 4983230072969 + 3 ^ 40 * 5258840 * 2
def baseEnd_5258840 : Nat := 900104201696769999338347

theorem tailTrace_5258840 : CollatzResearch.WordTrace tailWord_5258840 prefixEnd_5258840 900104201696769999338347 := by
  unfold tailWord_5258840
  simp only [CollatzResearch.WordTrace]
  refine ⟨95902826134064146606330987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127870434845418862141774649 95902826134064146606330987)
  ·
    refine ⟨143854239201096219909496481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95902826134064146606330987 143854239201096219909496481)
    ·
      refine ⟨107890679400822164932122361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143854239201096219909496481 107890679400822164932122361)
      ·
        refine ⟨80918009550616623699091771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107890679400822164932122361 80918009550616623699091771)
        ·
          refine ⟨121377014325924935548637657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80918009550616623699091771 121377014325924935548637657)
          ·
            refine ⟨91032760744443701661478243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121377014325924935548637657 91032760744443701661478243)
            ·
              refine ⟨136549141116665552492217365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91032760744443701661478243 136549141116665552492217365)
              ·
                refine ⟨6400740989843697773072689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 136549141116665552492217365 6400740989843697773072689)
                ·
                  refine ⟨4800555742382773329804517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6400740989843697773072689 4800555742382773329804517)
                  ·
                    refine ⟨900104201696769999338347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4800555742382773329804517 900104201696769999338347)
                    ·
                      rfl

theorem cell23_5258840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 2, 4].length) (baseStart_5258840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258840 prefixEnd_5258840 := by exact prefixLift 5258840
  have htrace : WordTrace (prefixWord ++ tailWord_5258840) baseStart_5258840 baseEnd_5258840 := by
    simpa [prefixWord, tailWord_5258840, baseEnd_5258840] using wordTrace_append hprefix tailTrace_5258840
  have hstable : (prefixWord ++ tailWord_5258840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258840).length < 2 ^ (prefixWord ++ tailWord_5258840).sum := by decide
  have hdescent : baseEnd_5258840 < baseStart_5258840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258853 : List Nat := [1, 3, 1, 3, 3, 1, 1, 10]
def baseStart_5258853 : Nat := 118140960795 + 5258853 * 2 ^ 59
def prefixEnd_5258853 : Nat := 4983230072969 + 3 ^ 40 * 5258853 * 2
def baseEnd_5258853 : Nat := 100011825197734016561203

theorem tailTrace_5258853 : CollatzResearch.WordTrace tailWord_5258853 prefixEnd_5258853 100011825197734016561203 := by
  unfold tailWord_5258853
  simp only [CollatzResearch.WordTrace]
  refine ⟨191806126417081196432885213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127870750944720797621923475 191806126417081196432885213)
  ·
    refine ⟨71927297406405448662331955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191806126417081196432885213 71927297406405448662331955)
    ·
      refine ⟨107890946109608172993497933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71927297406405448662331955 107890946109608172993497933)
      ·
        refine ⟨40459104791103064872561725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107890946109608172993497933 40459104791103064872561725)
        ·
          refine ⟨15172164296663649327210647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40459104791103064872561725 15172164296663649327210647)
          ·
            refine ⟨22758246444995473990815971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15172164296663649327210647 22758246444995473990815971)
            ·
              refine ⟨34137369667493210986223957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22758246444995473990815971 34137369667493210986223957)
              ·
                refine ⟨100011825197734016561203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34137369667493210986223957 100011825197734016561203)
                ·
                  rfl

theorem cell23_5258853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 10].length) (baseStart_5258853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258853 prefixEnd_5258853 := by exact prefixLift 5258853
  have htrace : WordTrace (prefixWord ++ tailWord_5258853) baseStart_5258853 baseEnd_5258853 := by
    simpa [prefixWord, tailWord_5258853, baseEnd_5258853] using wordTrace_append hprefix tailTrace_5258853
  have hstable : (prefixWord ++ tailWord_5258853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258853).length < 2 ^ (prefixWord ++ tailWord_5258853).sum := by decide
  have hdescent : baseEnd_5258853 < baseStart_5258853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258857 : List Nat := [1, 2, 1, 1, 1, 4, 6, 1, 2, 4]
def baseStart_5258857 : Nat := 118140960795 + 5258857 * 2 ^ 59
def prefixEnd_5258857 : Nat := 4983230072969 + 3 ^ 40 * 5258857 * 2
def baseEnd_5258857 : Nat := 900107111420478810500821

theorem tailTrace_5258857 : CollatzResearch.WordTrace tailWord_5258857 prefixEnd_5258857 900107111420478810500821 := by
  unfold tailWord_5258857
  simp only [CollatzResearch.WordTrace]
  refine ⟨191806272309066705116030825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127870848206044470077353883 191806272309066705116030825)
  ·
    refine ⟨143854704231800028837023119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191806272309066705116030825 143854704231800028837023119)
    ·
      refine ⟨215782056347700043255534679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143854704231800028837023119 215782056347700043255534679)
      ·
        refine ⟨323673084521550064883302019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215782056347700043255534679 323673084521550064883302019)
        ·
          refine ⟨485509626782325097324953029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323673084521550064883302019 485509626782325097324953029)
          ·
            refine ⟨91033055021685955748428693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 485509626782325097324953029 91033055021685955748428693)
            ·
              refine ⟨4267174454141529175707595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91033055021685955748428693 4267174454141529175707595)
              ·
                refine ⟨6400761681212293763561393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4267174454141529175707595 6400761681212293763561393)
                ·
                  refine ⟨4800571260909220322671045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6400761681212293763561393 4800571260909220322671045)
                  ·
                    refine ⟨900107111420478810500821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4800571260909220322671045 900107111420478810500821)
                    ·
                      rfl

theorem cell23_5258857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 2, 4].length) (baseStart_5258857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258857 prefixEnd_5258857 := by exact prefixLift 5258857
  have htrace : WordTrace (prefixWord ++ tailWord_5258857) baseStart_5258857 baseEnd_5258857 := by
    simpa [prefixWord, tailWord_5258857, baseEnd_5258857] using wordTrace_append hprefix tailTrace_5258857
  have hstable : (prefixWord ++ tailWord_5258857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258857).length < 2 ^ (prefixWord ++ tailWord_5258857).sum := by decide
  have hdescent : baseEnd_5258857 < baseStart_5258857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258870 : List Nat := [5, 1, 1, 2, 2, 1, 2, 9]
def baseStart_5258870 : Nat := 118140960795 + 5258870 * 2 ^ 59
def prefixEnd_5258870 : Nat := 4983230072969 + 3 ^ 40 * 5258870 * 2
def baseEnd_5258870 : Nat := 100012148500368328912589

theorem tailTrace_5258870 : CollatzResearch.WordTrace tailWord_5258870 prefixEnd_5258870 100012148500368328912589 := by
  unfold tailWord_5258870
  simp only [CollatzResearch.WordTrace]
  refine ⟨11987921653626225521015879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127871164305346405557502709 11987921653626225521015879)
  ·
    refine ⟨17981882480439338281523819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11987921653626225521015879 17981882480439338281523819)
    ·
      refine ⟨26972823720659007422285729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17981882480439338281523819 26972823720659007422285729)
      ·
        refine ⟨20229617790494255566714297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26972823720659007422285729 20229617790494255566714297)
        ·
          refine ⟨15172213342870691675035723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20229617790494255566714297 15172213342870691675035723)
          ·
            refine ⟨22758320014306037512553585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15172213342870691675035723 22758320014306037512553585)
            ·
              refine ⟨17068740010729528134415189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22758320014306037512553585 17068740010729528134415189)
              ·
                refine ⟨100012148500368328912589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17068740010729528134415189 100012148500368328912589)
                ·
                  rfl

theorem cell23_5258870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_5258870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258870 prefixEnd_5258870 := by exact prefixLift 5258870
  have htrace : WordTrace (prefixWord ++ tailWord_5258870) baseStart_5258870 baseEnd_5258870 := by
    simpa [prefixWord, tailWord_5258870, baseEnd_5258870] using wordTrace_append hprefix tailTrace_5258870
  have hstable : (prefixWord ++ tailWord_5258870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258870).length < 2 ^ (prefixWord ++ tailWord_5258870).sum := by decide
  have hdescent : baseEnd_5258870 < baseStart_5258870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258880 : List Nat := [2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 3]
def baseStart_5258880 : Nat := 118140960795 + 5258880 * 2 ^ 59
def prefixEnd_5258880 : Nat := 4983230072969 + 3 ^ 40 * 5258880 * 2
def baseEnd_5258880 : Nat := 2700333144316489841514857

theorem tailTrace_5258880 : CollatzResearch.WordTrace tailWord_5258880 prefixEnd_5258880 2700333144316489841514857 := by
  unfold tailWord_5258880
  simp only [CollatzResearch.WordTrace]
  refine ⟨95903555593991690022059047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127871407458655586696078729 95903555593991690022059047)
  ·
    refine ⟨143855333390987535033088571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95903555593991690022059047 143855333390987535033088571)
    ·
      refine ⟨215783000086481302549632857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143855333390987535033088571 215783000086481302549632857)
      ·
        refine ⟨161837250064860976912224643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215783000086481302549632857 161837250064860976912224643)
        ·
          refine ⟨242755875097291465368336965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161837250064860976912224643 242755875097291465368336965)
          ·
            refine ⟨45516726580742149756563181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 242755875097291465368336965 45516726580742149756563181)
            ·
              refine ⟨17068772467778306158711193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45516726580742149756563181 17068772467778306158711193)
              ·
                refine ⟨12801579350833729619033395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17068772467778306158711193 12801579350833729619033395)
                ·
                  refine ⟨19202369026250594428550093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12801579350833729619033395 19202369026250594428550093)
                  ·
                    refine ⟨7200888384843972910706285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19202369026250594428550093 7200888384843972910706285)
                    ·
                      refine ⟨2700333144316489841514857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7200888384843972910706285 2700333144316489841514857)
                      ·
                        rfl

theorem cell23_5258880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 3].length) (baseStart_5258880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258880 prefixEnd_5258880 := by exact prefixLift 5258880
  have htrace : WordTrace (prefixWord ++ tailWord_5258880) baseStart_5258880 baseEnd_5258880 := by
    simpa [prefixWord, tailWord_5258880, baseEnd_5258880] using wordTrace_append hprefix tailTrace_5258880
  have hstable : (prefixWord ++ tailWord_5258880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258880).length < 2 ^ (prefixWord ++ tailWord_5258880).sum := by decide
  have hdescent : baseEnd_5258880 < baseStart_5258880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258884 : List Nat := [2, 3, 2, 1, 5, 1, 1, 1, 1, 1, 5]
def baseStart_5258884 : Nat := 118140960795 + 5258884 * 2 ^ 59
def prefixEnd_5258884 : Nat := 4983230072969 + 3 ^ 40 * 5258884 * 2
def baseEnd_5258884 : Nat := 2700335198239107825864839

theorem tailTrace_5258884 : CollatzResearch.WordTrace tailWord_5258884 prefixEnd_5258884 2700335198239107825864839 := by
  unfold tailWord_5258884
  simp only [CollatzResearch.WordTrace]
  refine ⟨95903628539984444363631853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127871504719979259151509137 95903628539984444363631853)
  ·
    refine ⟨35963860702494166636361945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95903628539984444363631853 35963860702494166636361945)
    ·
      refine ⟨26972895526870624977271459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35963860702494166636361945 26972895526870624977271459)
      ·
        refine ⟨40459343290305937465907189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26972895526870624977271459 40459343290305937465907189)
        ·
          refine ⟨3793063433466181637428799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40459343290305937465907189 3793063433466181637428799)
          ·
            refine ⟨5689595150199272456143199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3793063433466181637428799 5689595150199272456143199)
            ·
              refine ⟨8534392725298908684214799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5689595150199272456143199 8534392725298908684214799)
              ·
                refine ⟨12801589087948363026322199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8534392725298908684214799 12801589087948363026322199)
                ·
                  refine ⟨19202383631922544539483299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12801589087948363026322199 19202383631922544539483299)
                  ·
                    refine ⟨28803575447883816809224949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19202383631922544539483299 28803575447883816809224949)
                    ·
                      refine ⟨2700335198239107825864839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28803575447883816809224949 2700335198239107825864839)
                      ·
                        rfl

theorem cell23_5258884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_5258884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258884 prefixEnd_5258884 := by exact prefixLift 5258884
  have htrace : WordTrace (prefixWord ++ tailWord_5258884) baseStart_5258884 baseEnd_5258884 := by
    simpa [prefixWord, tailWord_5258884, baseEnd_5258884] using wordTrace_append hprefix tailTrace_5258884
  have hstable : (prefixWord ++ tailWord_5258884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258884).length < 2 ^ (prefixWord ++ tailWord_5258884).sum := by decide
  have hdescent : baseEnd_5258884 < baseStart_5258884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258898 : List Nat := [3, 2, 3, 1, 3, 1, 1, 4, 1, 2, 2]
def baseStart_5258898 : Nat := 118140960795 + 5258898 * 2 ^ 59
def prefixEnd_5258898 : Nat := 4983230072969 + 3 ^ 40 * 5258898 * 2
def baseEnd_5258898 : Nat := 2700342386968270771089775

theorem tailTrace_5258898 : CollatzResearch.WordTrace tailWord_5258898 prefixEnd_5258898 2700342386968270771089775 := by
  unfold tailWord_5258898
  simp only [CollatzResearch.WordTrace]
  refine ⟨47951941925479542279568337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127871845134612112745515565 47951941925479542279568337)
  ·
    refine ⟨35963956444109656709676253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47951941925479542279568337 35963956444109656709676253)
    ·
      refine ⟨13486483666541121266128595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35963956444109656709676253 13486483666541121266128595)
      ·
        refine ⟨20229725499811681899192893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13486483666541121266128595 20229725499811681899192893)
        ·
          refine ⟨7586147062429380712197335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20229725499811681899192893 7586147062429380712197335)
          ·
            refine ⟨11379220593644071068296003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7586147062429380712197335 11379220593644071068296003)
            ·
              refine ⟨17068830890466106602444005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11379220593644071068296003 17068830890466106602444005)
              ·
                refine ⟨3200405791962394987958251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17068830890466106602444005 3200405791962394987958251)
                ·
                  refine ⟨4800608687943592481937377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3200405791962394987958251 4800608687943592481937377)
                  ·
                    refine ⟨3600456515957694361453033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4800608687943592481937377 3600456515957694361453033)
                    ·
                      refine ⟨2700342386968270771089775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3600456515957694361453033 2700342386968270771089775)
                      ·
                        rfl

theorem cell23_5258898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_5258898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258898 prefixEnd_5258898 := by exact prefixLift 5258898
  have htrace : WordTrace (prefixWord ++ tailWord_5258898) baseStart_5258898 baseEnd_5258898 := by
    simpa [prefixWord, tailWord_5258898, baseEnd_5258898] using wordTrace_append hprefix tailTrace_5258898
  have hstable : (prefixWord ++ tailWord_5258898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258898).length < 2 ^ (prefixWord ++ tailWord_5258898).sum := by decide
  have hdescent : baseEnd_5258898 < baseStart_5258898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258937 : List Nat := [1, 2, 1, 4, 1, 1, 4, 2, 1, 4, 2]
def baseStart_5258937 : Nat := 118140960795 + 5258937 * 2 ^ 59
def prefixEnd_5258937 : Nat := 4983230072969 + 3 ^ 40 * 5258937 * 2
def baseEnd_5258937 : Nat := 2700362412713796118502095

theorem tailTrace_5258937 : CollatzResearch.WordTrace tailWord_5258937 prefixEnd_5258937 2700362412713796118502095 := by
  unfold tailWord_5258937
  simp only [CollatzResearch.WordTrace]
  refine ⟨191809190148776878778943065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127872793432517919185962043 191809190148776878778943065)
  ·
    refine ⟨143856892611582659084207299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191809190148776878778943065 143856892611582659084207299)
    ·
      refine ⟨215785338917373988626310949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143856892611582659084207299 215785338917373988626310949)
      ·
        refine ⟨40459751047007622867433303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 215785338917373988626310949 40459751047007622867433303)
        ·
          refine ⟨60689626570511434301149955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40459751047007622867433303 60689626570511434301149955)
          ·
            refine ⟨91034439855767151451724933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60689626570511434301149955 91034439855767151451724933)
            ·
              refine ⟨17068957472956340897198425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91034439855767151451724933 17068957472956340897198425)
              ·
                refine ⟨12801718104717255672898819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17068957472956340897198425 12801718104717255672898819)
                ·
                  refine ⟨19202577157075883509348229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12801718104717255672898819 19202577157075883509348229)
                  ·
                    refine ⟨3600483216951728158002793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19202577157075883509348229 3600483216951728158002793)
                    ·
                      refine ⟨2700362412713796118502095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3600483216951728158002793 2700362412713796118502095)
                      ·
                        rfl

theorem cell23_5258937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_5258937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258937 prefixEnd_5258937 := by exact prefixLift 5258937
  have htrace : WordTrace (prefixWord ++ tailWord_5258937) baseStart_5258937 baseEnd_5258937 := by
    simpa [prefixWord, tailWord_5258937, baseEnd_5258937] using wordTrace_append hprefix tailTrace_5258937
  have hstable : (prefixWord ++ tailWord_5258937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258937).length < 2 ^ (prefixWord ++ tailWord_5258937).sum := by decide
  have hdescent : baseEnd_5258937 < baseStart_5258937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258943 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 9]
def baseStart_5258943 : Nat := 118140960795 + 5258943 * 2 ^ 59
def prefixEnd_5258943 : Nat := 4983230072969 + 3 ^ 40 * 5258943 * 2
def baseEnd_5258943 : Nat := 300040610399747010558563

theorem tailTrace_5258943 : CollatzResearch.WordTrace tailWord_5258943 prefixEnd_5258943 300040610399747010558563 := by
  unfold tailWord_5258943
  simp only [CollatzResearch.WordTrace]
  refine ⟨191809408986755141803661483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127872939324503427869107655 191809408986755141803661483)
  ·
    refine ⟨287714113480132712705492225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191809408986755141803661483 287714113480132712705492225)
    ·
      refine ⟨215785585110099534529119169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287714113480132712705492225 215785585110099534529119169)
      ·
        refine ⟨161839188832574650896839377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215785585110099534529119169 161839188832574650896839377)
        ·
          refine ⟨121379391624430988172629533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161839188832574650896839377 121379391624430988172629533)
          ·
            refine ⟨45517271859161620564736075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121379391624430988172629533 45517271859161620564736075)
            ·
              refine ⟨68275907788742430847104113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45517271859161620564736075 68275907788742430847104113)
              ·
                refine ⟨51206930841556823135328085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68275907788742430847104113 51206930841556823135328085)
                ·
                  refine ⟨300040610399747010558563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51206930841556823135328085 300040610399747010558563)
                  ·
                    rfl

theorem cell23_5258943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 9].length) (baseStart_5258943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258943 prefixEnd_5258943 := by exact prefixLift 5258943
  have htrace : WordTrace (prefixWord ++ tailWord_5258943) baseStart_5258943 baseEnd_5258943 := by
    simpa [prefixWord, tailWord_5258943, baseEnd_5258943] using wordTrace_append hprefix tailTrace_5258943
  have hstable : (prefixWord ++ tailWord_5258943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258943).length < 2 ^ (prefixWord ++ tailWord_5258943).sum := by decide
  have hdescent : baseEnd_5258943 < baseStart_5258943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5258990 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 1, 7]
def baseStart_5258990 : Nat := 118140960795 + 5258990 * 2 ^ 59
def prefixEnd_5258990 : Nat := 4983230072969 + 3 ^ 40 * 5258990 * 2
def baseEnd_5258990 : Nat := 900129875729494803713117

theorem tailTrace_5258990 : CollatzResearch.WordTrace tailWord_5258990 prefixEnd_5258990 900129875729494803713117 := by
  unfold tailWord_5258990
  simp only [CollatzResearch.WordTrace]
  refine ⟨23976390402198108603827803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127874082145056579220414949 23976390402198108603827803)
  ·
    refine ⟨35964585603297162905741705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23976390402198108603827803 35964585603297162905741705)
    ·
      refine ⟨26973439202472872179306279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35964585603297162905741705 26973439202472872179306279)
      ·
        refine ⟨40460158803709308268959419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26973439202472872179306279 40460158803709308268959419)
        ·
          refine ⟨60690238205563962403439129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40460158803709308268959419 60690238205563962403439129)
          ·
            refine ⟨45517678654172971802579347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60690238205563962403439129 45517678654172971802579347)
            ·
              refine ⟨68276517981259457703869021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45517678654172971802579347 68276517981259457703869021)
              ·
                refine ⟨25603694242972296638950883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68276517981259457703869021 25603694242972296638950883)
                ·
                  refine ⟨38405541364458444958426325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25603694242972296638950883 38405541364458444958426325)
                  ·
                    refine ⟨900129875729494803713117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38405541364458444958426325 900129875729494803713117)
                    ·
                      rfl

theorem cell23_5258990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_5258990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5258990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5258990 prefixEnd_5258990 := by exact prefixLift 5258990
  have htrace : WordTrace (prefixWord ++ tailWord_5258990) baseStart_5258990 baseEnd_5258990 := by
    simpa [prefixWord, tailWord_5258990, baseEnd_5258990] using wordTrace_append hprefix tailTrace_5258990
  have hstable : (prefixWord ++ tailWord_5258990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5258990).length < 2 ^ (prefixWord ++ tailWord_5258990).sum := by decide
  have hdescent : baseEnd_5258990 < baseStart_5258990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5258990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259044 : List Nat := [2, 3, 1, 3, 2, 2, 2, 1, 2, 1, 4]
def baseStart_5259044 : Nat := 118140960795 + 5259044 * 2 ^ 59
def prefixEnd_5259044 : Nat := 4983230072969 + 3 ^ 40 * 5259044 * 2
def baseEnd_5259044 : Nat := 2700417355143827199864103

theorem tailTrace_5259044 : CollatzResearch.WordTrace tailWord_5259044 prefixEnd_5259044 2700417355143827199864103 := by
  unfold tailWord_5259044
  simp only [CollatzResearch.WordTrace]
  refine ⟨95906546379694618026544093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127875395172926157368725457 95906546379694618026544093)
  ·
    refine ⟨35964954892385481759954035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95906546379694618026544093 35964954892385481759954035)
    ·
      refine ⟨53947432338578222639931053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35964954892385481759954035 53947432338578222639931053)
      ·
        refine ⟨20230287126966833489974145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53947432338578222639931053 20230287126966833489974145)
        ·
          refine ⟨15172715345225125117480609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20230287126966833489974145 15172715345225125117480609)
          ·
            refine ⟨11379536508918843838110457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15172715345225125117480609 11379536508918843838110457)
            ·
              refine ⟨8534652381689132878582843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11379536508918843838110457 8534652381689132878582843)
              ·
                refine ⟨12801978572533699317874265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8534652381689132878582843 12801978572533699317874265)
                ·
                  refine ⟨9601483929400274488405699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12801978572533699317874265 9601483929400274488405699)
                  ·
                    refine ⟨14402225894100411732608549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9601483929400274488405699 14402225894100411732608549)
                    ·
                      refine ⟨2700417355143827199864103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14402225894100411732608549 2700417355143827199864103)
                      ·
                        rfl

theorem cell23_5259044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_5259044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259044 prefixEnd_5259044 := by exact prefixLift 5259044
  have htrace : WordTrace (prefixWord ++ tailWord_5259044) baseStart_5259044 baseEnd_5259044 := by
    simpa [prefixWord, tailWord_5259044, baseEnd_5259044] using wordTrace_append hprefix tailTrace_5259044
  have hstable : (prefixWord ++ tailWord_5259044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259044).length < 2 ^ (prefixWord ++ tailWord_5259044).sum := by decide
  have hdescent : baseEnd_5259044 < baseStart_5259044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259071 : List Nat := [1, 1, 2, 2, 6, 1, 1, 4, 1, 4]
def baseStart_5259071 : Nat := 118140960795 + 5259071 * 2 ^ 59
def prefixEnd_5259071 : Nat := 4983230072969 + 3 ^ 40 * 5259071 * 2
def baseEnd_5259071 : Nat := 900143739707166198075493

theorem tailTrace_5259071 : CollatzResearch.WordTrace tailWord_5259071 prefixEnd_5259071 900143739707166198075493 := by
  unfold tailWord_5259071
  simp only [CollatzResearch.WordTrace]
  refine ⟨191814077530291419664321067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127876051686860946442880711 191814077530291419664321067)
  ·
    refine ⟨287721116295437129496481601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191814077530291419664321067 287721116295437129496481601)
    ·
      refine ⟨215790837221577847122361201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287721116295437129496481601 215790837221577847122361201)
      ·
        refine ⟨161843127916183385341770901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215790837221577847122361201 161843127916183385341770901)
        ·
          refine ⟨7586396621071096187895511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 161843127916183385341770901 7586396621071096187895511)
          ·
            refine ⟨11379594931606644281843267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7586396621071096187895511 11379594931606644281843267)
            ·
              refine ⟨17069392397409966422764901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11379594931606644281843267 17069392397409966422764901)
              ·
                refine ⟨3200511074514368704268419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17069392397409966422764901 3200511074514368704268419)
                ·
                  refine ⟨4800766611771553056402629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3200511074514368704268419 4800766611771553056402629)
                  ·
                    refine ⟨900143739707166198075493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4800766611771553056402629 900143739707166198075493)
                    ·
                      rfl

theorem cell23_5259071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 1, 4].length) (baseStart_5259071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259071 prefixEnd_5259071 := by exact prefixLift 5259071
  have htrace : WordTrace (prefixWord ++ tailWord_5259071) baseStart_5259071 baseEnd_5259071 := by
    simpa [prefixWord, tailWord_5259071, baseEnd_5259071] using wordTrace_append hprefix tailTrace_5259071
  have hstable : (prefixWord ++ tailWord_5259071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259071).length < 2 ^ (prefixWord ++ tailWord_5259071).sum := by decide
  have hdescent : baseEnd_5259071 < baseStart_5259071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259078 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2]
def baseStart_5259078 : Nat := 118140960795 + 5259078 * 2 ^ 59
def prefixEnd_5259078 : Nat := 4983230072969 + 3 ^ 40 * 5259078 * 2
def baseEnd_5259078 : Nat := 2700434813486080066838947

theorem tailTrace_5259078 : CollatzResearch.WordTrace tailWord_5259078 prefixEnd_5259078 2700434813486080066838947 := by
  unfold tailWord_5259078
  simp only [CollatzResearch.WordTrace]
  refine ⟨5994197901289564370619559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 127876221894177373239883925 5994197901289564370619559)
  ·
    refine ⟨8991296851934346555929339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5994197901289564370619559 8991296851934346555929339)
    ·
      refine ⟨13486945277901519833894009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8991296851934346555929339 13486945277901519833894009)
      ·
        refine ⟨10115208958426139875420507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13486945277901519833894009 10115208958426139875420507)
        ·
          refine ⟨15172813437639209813130761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10115208958426139875420507 15172813437639209813130761)
          ·
            refine ⟨11379610078229407359848071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15172813437639209813130761 11379610078229407359848071)
            ·
              refine ⟨17069415117344111039772107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11379610078229407359848071 17069415117344111039772107)
              ·
                refine ⟨25604122676016166559658161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17069415117344111039772107 25604122676016166559658161)
                ·
                  refine ⟨19203092007012124919743621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25604122676016166559658161 19203092007012124919743621)
                  ·
                    refine ⟨3600579751314773422451929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19203092007012124919743621 3600579751314773422451929)
                    ·
                      refine ⟨2700434813486080066838947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3600579751314773422451929 2700434813486080066838947)
                      ·
                        rfl

theorem cell23_5259078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_5259078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259078 prefixEnd_5259078 := by exact prefixLift 5259078
  have htrace : WordTrace (prefixWord ++ tailWord_5259078) baseStart_5259078 baseEnd_5259078 := by
    simpa [prefixWord, tailWord_5259078, baseEnd_5259078] using wordTrace_append hprefix tailTrace_5259078
  have hstable : (prefixWord ++ tailWord_5259078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259078).length < 2 ^ (prefixWord ++ tailWord_5259078).sum := by decide
  have hdescent : baseEnd_5259078 < baseStart_5259078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259097 : List Nat := [1, 2, 1, 2, 2, 3, 2, 4, 1, 5]
def baseStart_5259097 : Nat := 118140960795 + 5259097 * 2 ^ 59
def prefixEnd_5259097 : Nat := 4983230072969 + 3 ^ 40 * 5259097 * 2
def baseEnd_5259097 : Nat := 900148189872838497500453

theorem tailTrace_5259097 : CollatzResearch.WordTrace tailWord_5259097 prefixEnd_5259097 900148189872838497500453 := by
  unfold tailWord_5259097
  simp only [CollatzResearch.WordTrace]
  refine ⟨191815025828197226104767545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127876683885464817403178363 191815025828197226104767545)
  ·
    refine ⟨143861269371147919578575659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191815025828197226104767545 143861269371147919578575659)
    ·
      refine ⟨215791904056721879367863489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143861269371147919578575659 215791904056721879367863489)
      ·
        refine ⟨161843928042541409525897617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215791904056721879367863489 161843928042541409525897617)
        ·
          refine ⟨121382946031906057144423213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161843928042541409525897617 121382946031906057144423213)
          ·
            refine ⟨45518604761964771429158705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121382946031906057144423213 45518604761964771429158705)
            ·
              refine ⟨34138953571473578571869029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45518604761964771429158705 34138953571473578571869029)
              ·
                refine ⟨6401053794651295982225443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34138953571473578571869029 6401053794651295982225443)
                ·
                  refine ⟨9601580691976943973338165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6401053794651295982225443 9601580691976943973338165)
                  ·
                    refine ⟨900148189872838497500453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9601580691976943973338165 900148189872838497500453)
                    ·
                      rfl

theorem cell23_5259097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 5].length) (baseStart_5259097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259097 prefixEnd_5259097 := by exact prefixLift 5259097
  have htrace : WordTrace (prefixWord ++ tailWord_5259097) baseStart_5259097 baseEnd_5259097 := by
    simpa [prefixWord, tailWord_5259097, baseEnd_5259097] using wordTrace_append hprefix tailTrace_5259097
  have hstable : (prefixWord ++ tailWord_5259097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259097).length < 2 ^ (prefixWord ++ tailWord_5259097).sum := by decide
  have hdescent : baseEnd_5259097 < baseStart_5259097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259104 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 1, 5, 2]
def baseStart_5259104 : Nat := 118140960795 + 5259104 * 2 ^ 59
def prefixEnd_5259104 : Nat := 4983230072969 + 3 ^ 40 * 5259104 * 2
def baseEnd_5259104 : Nat := 2700448163983096965113827

theorem tailTrace_5259104 : CollatzResearch.WordTrace tailWord_5259104 prefixEnd_5259104 2700448163983096965113827 := by
  unfold tailWord_5259104
  simp only [CollatzResearch.WordTrace]
  refine ⟨95907640569585933150136183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127876854092781244200181577 95907640569585933150136183)
  ·
    refine ⟨143861460854378899725204275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95907640569585933150136183 143861460854378899725204275)
    ·
      refine ⟨215792191281568349587806413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143861460854378899725204275 215792191281568349587806413)
      ·
        refine ⟨80922071730588131095427405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215792191281568349587806413 80922071730588131095427405)
        ·
          refine ⟨30345776898970549160785277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80922071730588131095427405 30345776898970549160785277)
          ·
            refine ⟨11379666337113955935294479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30345776898970549160785277 11379666337113955935294479)
            ·
              refine ⟨17069499505670933902941719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11379666337113955935294479 17069499505670933902941719)
              ·
                refine ⟨25604249258506400854412579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17069499505670933902941719 25604249258506400854412579)
                ·
                  refine ⟨38406373887759601281618869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25604249258506400854412579 38406373887759601281618869)
                  ·
                    refine ⟨3600597551977462620151769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38406373887759601281618869 3600597551977462620151769)
                    ·
                      refine ⟨2700448163983096965113827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3600597551977462620151769 2700448163983096965113827)
                      ·
                        rfl

theorem cell23_5259104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 1, 5, 2].length) (baseStart_5259104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259104 prefixEnd_5259104 := by exact prefixLift 5259104
  have htrace : WordTrace (prefixWord ++ tailWord_5259104) baseStart_5259104 baseEnd_5259104 := by
    simpa [prefixWord, tailWord_5259104, baseEnd_5259104] using wordTrace_append hprefix tailTrace_5259104
  have hstable : (prefixWord ++ tailWord_5259104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259104).length < 2 ^ (prefixWord ++ tailWord_5259104).sum := by decide
  have hdescent : baseEnd_5259104 < baseStart_5259104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259247 : List Nat := [1, 1, 2, 1, 4, 2, 2, 3, 7]
def baseStart_5259247 : Nat := 118140960795 + 5259247 * 2 ^ 59
def prefixEnd_5259247 : Nat := 4983230072969 + 3 ^ 40 * 5259247 * 2
def baseEnd_5259247 : Nat := 300057954635187767291741

theorem tailTrace_5259247 : CollatzResearch.WordTrace tailWord_5259247 prefixEnd_5259247 300057954635187767291741 := by
  unfold tailWord_5259247
  simp only [CollatzResearch.WordTrace]
  refine ⟨191820496777653801722727995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127880331185102534481818663 191820496777653801722727995)
  ·
    refine ⟨287730745166480702584091993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191820496777653801722727995 287730745166480702584091993)
    ·
      refine ⟨215798058874860526938068995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287730745166480702584091993 215798058874860526938068995)
      ·
        refine ⟨323697088312290790407103493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215798058874860526938068995 323697088312290790407103493)
        ·
          refine ⟨60693204058554523201331905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 323697088312290790407103493 60693204058554523201331905)
          ·
            refine ⟨45519903043915892400998929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60693204058554523201331905 45519903043915892400998929)
            ·
              refine ⟨34139927282936919300749197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45519903043915892400998929 34139927282936919300749197)
              ·
                refine ⟨12802472731101344737780949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34139927282936919300749197 12802472731101344737780949)
                ·
                  refine ⟨300057954635187767291741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12802472731101344737780949 300057954635187767291741)
                  ·
                    rfl

theorem cell23_5259247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 7].length) (baseStart_5259247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259247 prefixEnd_5259247 := by exact prefixLift 5259247
  have htrace : WordTrace (prefixWord ++ tailWord_5259247) baseStart_5259247 baseEnd_5259247 := by
    simpa [prefixWord, tailWord_5259247, baseEnd_5259247] using wordTrace_append hprefix tailTrace_5259247
  have hstable : (prefixWord ++ tailWord_5259247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259247).length < 2 ^ (prefixWord ++ tailWord_5259247).sum := by decide
  have hdescent : baseEnd_5259247 < baseStart_5259247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259314 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4]
def baseStart_5259314 : Nat := 118140960795 + 5259314 * 2 ^ 59
def prefixEnd_5259314 : Nat := 4983230072969 + 3 ^ 40 * 5259314 * 2
def baseEnd_5259314 : Nat := 2700555994920541143487861

theorem tailTrace_5259314 : CollatzResearch.WordTrace tailWord_5259314 prefixEnd_5259314 2700555994920541143487861 := by
  unfold tailWord_5259314
  simp only [CollatzResearch.WordTrace]
  refine ⟨47955735117102768041354249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127881960312274048110277997 47955735117102768041354249)
  ·
    refine ⟨35966801337827076031015687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47955735117102768041354249 35966801337827076031015687)
    ·
      refine ⟨53950202006740614046523531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35966801337827076031015687 53950202006740614046523531)
      ·
        refine ⟨80925303010110921069785297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53950202006740614046523531 80925303010110921069785297)
        ·
          refine ⟨60693977257583190802338973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80925303010110921069785297 60693977257583190802338973)
          ·
            refine ⟨22760241471593696550877115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60693977257583190802338973 22760241471593696550877115)
            ·
              refine ⟨34140362207390544826315673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22760241471593696550877115 34140362207390544826315673)
              ·
                refine ⟨25605271655542908619736755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34140362207390544826315673 25605271655542908619736755)
                ·
                  refine ⟨38407907483314362929605133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25605271655542908619736755 38407907483314362929605133)
                  ·
                    refine ⟨14402965306242886098601925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38407907483314362929605133 14402965306242886098601925)
                    ·
                      refine ⟨2700555994920541143487861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14402965306242886098601925 2700555994920541143487861)
                      ·
                        rfl

theorem cell23_5259314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_5259314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259314 prefixEnd_5259314 := by exact prefixLift 5259314
  have htrace : WordTrace (prefixWord ++ tailWord_5259314) baseStart_5259314 baseEnd_5259314 := by
    simpa [prefixWord, tailWord_5259314, baseEnd_5259314] using wordTrace_append hprefix tailTrace_5259314
  have hstable : (prefixWord ++ tailWord_5259314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259314).length < 2 ^ (prefixWord ++ tailWord_5259314).sum := by decide
  have hdescent : baseEnd_5259314 < baseStart_5259314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259337 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 10]
def baseStart_5259337 : Nat := 118140960795 + 5259337 * 2 ^ 59
def prefixEnd_5259337 : Nat := 4983230072969 + 3 ^ 40 * 5259337 * 2
def baseEnd_5259337 : Nat := 300063089441732728166695

theorem tailTrace_5259337 : CollatzResearch.WordTrace tailWord_5259337 prefixEnd_5259337 300063089441732728166695 := by
  unfold tailWord_5259337
  simp only [CollatzResearch.WordTrace]
  refine ⟨191823779347327747093504265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127882519564885164729002843 191823779347327747093504265)
  ·
    refine ⟨143867834510495810320128199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191823779347327747093504265 143867834510495810320128199)
    ·
      refine ⟨215801751765743715480192299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143867834510495810320128199 215801751765743715480192299)
      ·
        refine ⟨323702627648615573220288449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215801751765743715480192299 323702627648615573220288449)
        ·
          refine ⟨242776970736461679915216337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323702627648615573220288449 242776970736461679915216337)
          ·
            refine ⟨182082728052346259936412253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242776970736461679915216337 182082728052346259936412253)
            ·
              refine ⟨68281023019629847476154595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182082728052346259936412253 68281023019629847476154595)
              ·
                refine ⟨102421534529444771214231893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68281023019629847476154595 102421534529444771214231893)
                ·
                  refine ⟨300063089441732728166695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 102421534529444771214231893 300063089441732728166695)
                  ·
                    rfl

theorem cell23_5259337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 10].length) (baseStart_5259337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259337 prefixEnd_5259337 := by exact prefixLift 5259337
  have htrace : WordTrace (prefixWord ++ tailWord_5259337) baseStart_5259337 baseEnd_5259337 := by
    simpa [prefixWord, tailWord_5259337, baseEnd_5259337] using wordTrace_append hprefix tailTrace_5259337
  have hstable : (prefixWord ++ tailWord_5259337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259337).length < 2 ^ (prefixWord ++ tailWord_5259337).sum := by decide
  have hdescent : baseEnd_5259337 < baseStart_5259337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259354 : List Nat := [3, 1, 1, 2, 1, 1, 4, 4, 6]
def baseStart_5259354 : Nat := 118140960795 + 5259354 * 2 ^ 59
def prefixEnd_5259354 : Nat := 4983230072969 + 3 ^ 40 * 5259354 * 2
def baseEnd_5259354 : Nat := 300064059349635665220853

theorem tailTrace_5259354 : CollatzResearch.WordTrace tailWord_5259354 prefixEnd_5259354 300064059349635665220853 := by
  unfold tailWord_5259354
  simp only [CollatzResearch.WordTrace]
  refine ⟨47956099847066539749218279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127882932925510772664582077 47956099847066539749218279)
  ·
    refine ⟨71934149770599809623827419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47956099847066539749218279 71934149770599809623827419)
    ·
      refine ⟨107901224655899714435741129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71934149770599809623827419 107901224655899714435741129)
      ·
        refine ⟨80925918491924785826805847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107901224655899714435741129 80925918491924785826805847)
        ·
          refine ⟨121388877737887178740208771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80925918491924785826805847 121388877737887178740208771)
          ·
            refine ⟨182083316606830768110313157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121388877737887178740208771 182083316606830768110313157)
            ·
              refine ⟨34140621863780769020683717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 182083316606830768110313157 34140621863780769020683717)
              ·
                refine ⟨6401366599458894191378197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34140621863780769020683717 6401366599458894191378197)
                ·
                  refine ⟨300064059349635665220853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6401366599458894191378197 300064059349635665220853)
                  ·
                    rfl

theorem cell23_5259354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 6].length) (baseStart_5259354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259354 prefixEnd_5259354 := by exact prefixLift 5259354
  have htrace : WordTrace (prefixWord ++ tailWord_5259354) baseStart_5259354 baseEnd_5259354 := by
    simpa [prefixWord, tailWord_5259354, baseEnd_5259354] using wordTrace_append hprefix tailTrace_5259354
  have hstable : (prefixWord ++ tailWord_5259354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259354).length < 2 ^ (prefixWord ++ tailWord_5259354).sum := by decide
  have hdescent : baseEnd_5259354 < baseStart_5259354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259421 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_5259421 : Nat := 118140960795 + 5259421 * 2 ^ 59
def prefixEnd_5259421 : Nat := 4983230072969 + 3 ^ 40 * 5259421 * 2
def baseEnd_5259421 : Nat := 2700610937350572224849869

theorem tailTrace_5259421 : CollatzResearch.WordTrace tailWord_5259421 prefixEnd_5259421 2700610937350572224849869 := by
  unfold tailWord_5259421
  simp only [CollatzResearch.WordTrace]
  refine ⟨191826843079023429439562117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127884562052682286293041411 191826843079023429439562117)
  ·
    refine ⟨35967533077316893019917897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191826843079023429439562117 35967533077316893019917897)
    ·
      refine ⟨26975649807987669764938423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35967533077316893019917897 26975649807987669764938423)
      ·
        refine ⟨40463474711981504647407635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26975649807987669764938423 40463474711981504647407635)
        ·
          refine ⟨60695212067972256971111453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40463474711981504647407635 60695212067972256971111453)
          ·
            refine ⟨22760704525489596364166795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60695212067972256971111453 22760704525489596364166795)
            ·
              refine ⟨34141056788234394546250193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22760704525489596364166795 34141056788234394546250193)
              ·
                refine ⟨25605792591175795909687645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34141056788234394546250193 25605792591175795909687645)
                ·
                  refine ⟨9602172221690923466132867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25605792591175795909687645 9602172221690923466132867)
                  ·
                    refine ⟨14403258332536385199199301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9602172221690923466132867 14403258332536385199199301)
                    ·
                      refine ⟨2700610937350572224849869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14403258332536385199199301 2700610937350572224849869)
                      ·
                        rfl

theorem cell23_5259421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_5259421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259421 prefixEnd_5259421 := by exact prefixLift 5259421
  have htrace : WordTrace (prefixWord ++ tailWord_5259421) baseStart_5259421 baseEnd_5259421 := by
    simpa [prefixWord, tailWord_5259421, baseEnd_5259421] using wordTrace_append hprefix tailTrace_5259421
  have hstable : (prefixWord ++ tailWord_5259421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259421).length < 2 ^ (prefixWord ++ tailWord_5259421).sum := by decide
  have hdescent : baseEnd_5259421 < baseStart_5259421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259452 : List Nat := [2, 2, 2, 3, 4, 1, 2, 1, 1, 5]
def baseStart_5259452 : Nat := 118140960795 + 5259452 * 2 ^ 59
def prefixEnd_5259452 : Nat := 4983230072969 + 3 ^ 40 * 5259452 * 2
def baseEnd_5259452 : Nat := 900208951750287201187409

theorem tailTrace_5259452 : CollatzResearch.WordTrace tailWord_5259452 prefixEnd_5259452 900208951750287201187409 := by
  unfold tailWord_5259452
  simp only [CollatzResearch.WordTrace]
  refine ⟨95913986870955560866970305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127885315827940747822627073 95913986870955560866970305)
  ·
    refine ⟨71935490153216670650227729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95913986870955560866970305 71935490153216670650227729)
    ·
      refine ⟨53951617614912502987670797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71935490153216670650227729 53951617614912502987670797)
      ·
        refine ⟨20231856605592188620376549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53951617614912502987670797 20231856605592188620376549)
        ·
          refine ⟨3793473113548535366320603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20231856605592188620376549 3793473113548535366320603)
          ·
            refine ⟨5690209670322803049480905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3793473113548535366320603 5690209670322803049480905)
            ·
              refine ⟨4267657252742102287110679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5690209670322803049480905 4267657252742102287110679)
              ·
                refine ⟨6401485879113153430666019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4267657252742102287110679 6401485879113153430666019)
                ·
                  refine ⟨9602228818669730145999029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6401485879113153430666019 9602228818669730145999029)
                  ·
                    refine ⟨900208951750287201187409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9602228818669730145999029 900208951750287201187409)
                    ·
                      rfl

theorem cell23_5259452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_5259452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259452 prefixEnd_5259452 := by exact prefixLift 5259452
  have htrace : WordTrace (prefixWord ++ tailWord_5259452) baseStart_5259452 baseEnd_5259452 := by
    simpa [prefixWord, tailWord_5259452, baseEnd_5259452] using wordTrace_append hprefix tailTrace_5259452
  have hstable : (prefixWord ++ tailWord_5259452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259452).length < 2 ^ (prefixWord ++ tailWord_5259452).sum := by decide
  have hdescent : baseEnd_5259452 < baseStart_5259452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259464 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 2, 2, 6]
def baseStart_5259464 : Nat := 118140960795 + 5259464 * 2 ^ 59
def prefixEnd_5259464 : Nat := 4983230072969 + 3 ^ 40 * 5259464 * 2
def baseEnd_5259464 : Nat := 2700633017018715556612171

theorem tailTrace_5259464 : CollatzResearch.WordTrace tailWord_5259464 prefixEnd_5259464 2700633017018715556612171 := by
  unfold tailWord_5259464
  simp only [CollatzResearch.WordTrace]
  refine ⟨95914205708933823891688723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127885607611911765188918297 95914205708933823891688723)
  ·
    refine ⟨143871308563400735837533085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95914205708933823891688723 143871308563400735837533085)
    ·
      refine ⟨53951740711275275939074907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143871308563400735837533085 53951740711275275939074907)
      ·
        refine ⟨80927611066912913908612361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53951740711275275939074907 80927611066912913908612361)
        ·
          refine ⟨60695708300184685431459271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80927611066912913908612361 60695708300184685431459271)
          ·
            refine ⟨91043562450277028147188907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60695708300184685431459271 91043562450277028147188907)
            ·
              refine ⟨136565343675415542220783361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91043562450277028147188907 136565343675415542220783361)
              ·
                refine ⟨102424007756561656665587521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136565343675415542220783361 102424007756561656665587521)
                ·
                  refine ⟨76818005817421242499190641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102424007756561656665587521 76818005817421242499190641)
                  ·
                    refine ⟨57613504363065931874392981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76818005817421242499190641 57613504363065931874392981)
                    ·
                      refine ⟨2700633017018715556612171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57613504363065931874392981 2700633017018715556612171)
                      ·
                        rfl

theorem cell23_5259464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_5259464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259464 prefixEnd_5259464 := by exact prefixLift 5259464
  have htrace : WordTrace (prefixWord ++ tailWord_5259464) baseStart_5259464 baseEnd_5259464 := by
    simpa [prefixWord, tailWord_5259464, baseEnd_5259464] using wordTrace_append hprefix tailTrace_5259464
  have hstable : (prefixWord ++ tailWord_5259464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259464).length < 2 ^ (prefixWord ++ tailWord_5259464).sum := by decide
  have hdescent : baseEnd_5259464 < baseStart_5259464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259485 : List Nat := [1, 4, 3, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_5259485 : Nat := 118140960795 + 5259485 * 2 ^ 59
def prefixEnd_5259485 : Nat := 4983230072969 + 3 ^ 40 * 5259485 * 2
def baseEnd_5259485 : Nat := 2700643800112459974449575

theorem tailTrace_5259485 : CollatzResearch.WordTrace tailWord_5259485 prefixEnd_5259485 2700643800112459974449575 := by
  unfold tailWord_5259485
  simp only [CollatzResearch.WordTrace]
  refine ⟨191829177350791568369891909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127886118233861045579927939 191829177350791568369891909)
  ·
    refine ⟨35967970753273419069354733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191829177350791568369891909 35967970753273419069354733)
    ·
      refine ⟨13487989032477532151008025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35967970753273419069354733 13487989032477532151008025)
      ·
        refine ⟨10115991774358149113256019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13487989032477532151008025 10115991774358149113256019)
        ·
          refine ⟨15173987661537223669884029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10115991774358149113256019 15173987661537223669884029)
          ·
            refine ⟨5690245373076458876206511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15173987661537223669884029 5690245373076458876206511)
            ·
              refine ⟨8535368059614688314309767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5690245373076458876206511 8535368059614688314309767)
              ·
                refine ⟨12803052089422032471464651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8535368059614688314309767 12803052089422032471464651)
                ·
                  refine ⟨19204578134133048707196977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12803052089422032471464651 19204578134133048707196977)
                  ·
                    refine ⟨14403433600599786530397733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19204578134133048707196977 14403433600599786530397733)
                    ·
                      refine ⟨2700643800112459974449575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14403433600599786530397733 2700643800112459974449575)
                      ·
                        rfl

theorem cell23_5259485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_5259485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259485 prefixEnd_5259485 := by exact prefixLift 5259485
  have htrace : WordTrace (prefixWord ++ tailWord_5259485) baseStart_5259485 baseEnd_5259485 := by
    simpa [prefixWord, tailWord_5259485, baseEnd_5259485] using wordTrace_append hprefix tailTrace_5259485
  have hstable : (prefixWord ++ tailWord_5259485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259485).length < 2 ^ (prefixWord ++ tailWord_5259485).sum := by decide
  have hdescent : baseEnd_5259485 < baseStart_5259485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259504 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 1, 8]
def baseStart_5259504 : Nat := 118140960795 + 5259504 * 2 ^ 59
def prefixEnd_5259504 : Nat := 4983230072969 + 3 ^ 40 * 5259504 * 2
def baseEnd_5259504 : Nat := 900217852081631800037329

theorem tailTrace_5259504 : CollatzResearch.WordTrace tailWord_5259504 prefixEnd_5259504 900217852081631800037329 := by
  unfold tailWord_5259504
  simp only [CollatzResearch.WordTrace]
  refine ⟨95914935168861367307416783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127886580225148489743222377 95914935168861367307416783)
  ·
    refine ⟨143872402753292050961125175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95914935168861367307416783 143872402753292050961125175)
    ·
      refine ⟨215808604129938076441687763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143872402753292050961125175 215808604129938076441687763)
      ·
        refine ⟨323712906194907114662531645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215808604129938076441687763 323712906194907114662531645)
        ·
          refine ⟨121392339823090167998449367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 323712906194907114662531645 121392339823090167998449367)
          ·
            refine ⟨182088509734635251997674051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121392339823090167998449367 182088509734635251997674051)
            ·
              refine ⟨273132764601952877996511077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182088509734635251997674051 273132764601952877996511077)
              ·
                refine ⟨51212393362866164624345827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 273132764601952877996511077 51212393362866164624345827)
                ·
                  refine ⟨76818590044299246936518741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51212393362866164624345827 76818590044299246936518741)
                  ·
                    refine ⟨900217852081631800037329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76818590044299246936518741 900217852081631800037329)
                    ·
                      rfl

theorem cell23_5259504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 1, 8].length) (baseStart_5259504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259504 prefixEnd_5259504 := by exact prefixLift 5259504
  have htrace : WordTrace (prefixWord ++ tailWord_5259504) baseStart_5259504 baseEnd_5259504 := by
    simpa [prefixWord, tailWord_5259504, baseEnd_5259504] using wordTrace_append hprefix tailTrace_5259504
  have hstable : (prefixWord ++ tailWord_5259504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259504).length < 2 ^ (prefixWord ++ tailWord_5259504).sum := by decide
  have hdescent : baseEnd_5259504 < baseStart_5259504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259531 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 3]
def baseStart_5259531 : Nat := 118140960795 + 5259531 * 2 ^ 59
def prefixEnd_5259531 : Nat := 4983230072969 + 3 ^ 40 * 5259531 * 2
def baseEnd_5259531 : Nat := 2700667420222566794474363

theorem tailTrace_5259531 : CollatzResearch.WordTrace tailWord_5259531 prefixEnd_5259531 2700667420222566794474363 := by
  unfold tailWord_5259531
  simp only [CollatzResearch.WordTrace]
  refine ⟨191830855108624918226066447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127887236739083278817377631 191830855108624918226066447)
  ·
    refine ⟨287746282662937377339099671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191830855108624918226066447 287746282662937377339099671)
    ·
      refine ⟨431619423994406066008649507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287746282662937377339099671 431619423994406066008649507)
      ·
        refine ⟨647429135991609099012974261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431619423994406066008649507 647429135991609099012974261)
        ·
          refine ⟨60696481499213353032466337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 647429135991609099012974261 60696481499213353032466337)
          ·
            refine ⟨45522361124410014774349753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60696481499213353032466337 45522361124410014774349753)
            ·
              refine ⟨34141770843307511080762315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45522361124410014774349753 34141770843307511080762315)
              ·
                refine ⟨51212656264961266621143473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34141770843307511080762315 51212656264961266621143473)
                ·
                  refine ⟨38409492198720949965857605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51212656264961266621143473 38409492198720949965857605)
                  ·
                    refine ⟨7201779787260178118598301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38409492198720949965857605 7201779787260178118598301)
                    ·
                      refine ⟨2700667420222566794474363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7201779787260178118598301 2700667420222566794474363)
                      ·
                        rfl

theorem cell23_5259531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 3].length) (baseStart_5259531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259531 prefixEnd_5259531 := by exact prefixLift 5259531
  have htrace : WordTrace (prefixWord ++ tailWord_5259531) baseStart_5259531 baseEnd_5259531 := by
    simpa [prefixWord, tailWord_5259531, baseEnd_5259531] using wordTrace_append hprefix tailTrace_5259531
  have hstable : (prefixWord ++ tailWord_5259531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259531).length < 2 ^ (prefixWord ++ tailWord_5259531).sum := by decide
  have hdescent : baseEnd_5259531 < baseStart_5259531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259541 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 2, 2, 4]
def baseStart_5259541 : Nat := 118140960795 + 5259541 * 2 ^ 59
def prefixEnd_5259541 : Nat := 4983230072969 + 3 ^ 40 * 5259541 * 2
def baseEnd_5259541 : Nat := 2700672555029111755349317

theorem tailTrace_5259541 : CollatzResearch.WordTrace tailWord_5259541 prefixEnd_5259541 2700672555029111755349317 := by
  unfold tailWord_5259541
  simp only [CollatzResearch.WordTrace]
  refine ⟨191831219838588689933930477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127887479892392459955953651 191831219838588689933930477)
  ·
    refine ⟨71936707439470758725223929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191831219838588689933930477 71936707439470758725223929)
    ·
      refine ⟨53952530579603069043917947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71936707439470758725223929 53952530579603069043917947)
      ·
        refine ⟨80928795869404603565876921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53952530579603069043917947 80928795869404603565876921)
        ·
          refine ⟨60696596902053452674407691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80928795869404603565876921 60696596902053452674407691)
          ·
            refine ⟨91044895353080179011611537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60696596902053452674407691 91044895353080179011611537)
            ·
              refine ⟨68283671514810134258708653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91044895353080179011611537 68283671514810134258708653)
              ·
                refine ⟨25606376818053800347015745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68283671514810134258708653 25606376818053800347015745)
                ·
                  refine ⟨19204782613540350260261809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25606376818053800347015745 19204782613540350260261809)
                  ·
                    refine ⟨14403586960155262695196357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19204782613540350260261809 14403586960155262695196357)
                    ·
                      refine ⟨2700672555029111755349317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14403586960155262695196357 2700672555029111755349317)
                      ·
                        rfl

theorem cell23_5259541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_5259541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259541 prefixEnd_5259541 := by exact prefixLift 5259541
  have htrace : WordTrace (prefixWord ++ tailWord_5259541) baseStart_5259541 baseEnd_5259541 := by
    simpa [prefixWord, tailWord_5259541, baseEnd_5259541] using wordTrace_append hprefix tailTrace_5259541
  have hstable : (prefixWord ++ tailWord_5259541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259541).length < 2 ^ (prefixWord ++ tailWord_5259541).sum := by decide
  have hdescent : baseEnd_5259541 < baseStart_5259541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259549 : List Nat := [1, 4, 2, 3, 2, 2, 1, 2, 1, 3, 2]
def baseStart_5259549 : Nat := 118140960795 + 5259549 * 2 ^ 59
def prefixEnd_5259549 : Nat := 4983230072969 + 3 ^ 40 * 5259549 * 2
def baseEnd_5259549 : Nat := 2700676662874347724049281

theorem tailTrace_5259549 : CollatzResearch.WordTrace tailWord_5259549 prefixEnd_5259549 2700676662874347724049281 := by
  unfold tailWord_5259549
  simp only [CollatzResearch.WordTrace]
  refine ⟨191831511622559707300221701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127887674415039804866814467 191831511622559707300221701)
  ·
    refine ⟨35968408429229945118791569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191831511622559707300221701 35968408429229945118791569)
    ·
      refine ⟨26976306321922458839093677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35968408429229945118791569 26976306321922458839093677)
      ·
        refine ⟨10116114870720922064660129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26976306321922458839093677 10116114870720922064660129)
        ·
          refine ⟨7587086153040691548495097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10116114870720922064660129 7587086153040691548495097)
          ·
            refine ⟨5690314614780518661371323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7587086153040691548495097 5690314614780518661371323)
            ·
              refine ⟨8535471922170777992056985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5690314614780518661371323 8535471922170777992056985)
              ·
                refine ⟨6401603941628083494042739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8535471922170777992056985 6401603941628083494042739)
                ·
                  refine ⟨9602405912442125241064109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6401603941628083494042739 9602405912442125241064109)
                  ·
                    refine ⟨3600902217165796965399041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9602405912442125241064109 3600902217165796965399041)
                    ·
                      refine ⟨2700676662874347724049281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3600902217165796965399041 2700676662874347724049281)
                      ·
                        rfl

theorem cell23_5259549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_5259549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259549 prefixEnd_5259549 := by exact prefixLift 5259549
  have htrace : WordTrace (prefixWord ++ tailWord_5259549) baseStart_5259549 baseEnd_5259549 := by
    simpa [prefixWord, tailWord_5259549, baseEnd_5259549] using wordTrace_append hprefix tailTrace_5259549
  have hstable : (prefixWord ++ tailWord_5259549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259549).length < 2 ^ (prefixWord ++ tailWord_5259549).sum := by decide
  have hdescent : baseEnd_5259549 < baseStart_5259549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259562 : List Nat := [3, 1, 4, 2, 2, 1, 1, 2, 1, 4, 2]
def baseStart_5259562 : Nat := 118140960795 + 5259562 * 2 ^ 59
def prefixEnd_5259562 : Nat := 4983230072969 + 3 ^ 40 * 5259562 * 2
def baseEnd_5259562 : Nat := 2700683338122856173186721

theorem tailTrace_5259562 : CollatzResearch.WordTrace tailWord_5259562 prefixEnd_5259562 2700683338122856173186721 := by
  unfold tailWord_5259562
  simp only [CollatzResearch.WordTrace]
  refine ⟨47957996442878152630111235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127887990514341740346963293 47957996442878152630111235)
  ·
    refine ⟨71936994664317228945166853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47957996442878152630111235 71936994664317228945166853)
    ·
      refine ⟨13488186499559480427218785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71936994664317228945166853 13488186499559480427218785)
      ·
        refine ⟨10116139874669610320414089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13488186499559480427218785 10116139874669610320414089)
        ·
          refine ⟨7587104906002207740310567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10116139874669610320414089 7587104906002207740310567)
          ·
            refine ⟨11380657359003311610465851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7587104906002207740310567 11380657359003311610465851)
            ·
              refine ⟨17070986038504967415698777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11380657359003311610465851 17070986038504967415698777)
              ·
                refine ⟨12803239528878725561774083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17070986038504967415698777 12803239528878725561774083)
                ·
                  refine ⟨19204859293318088342661125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12803239528878725561774083 19204859293318088342661125)
                  ·
                    refine ⟨3600911117497141564248961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19204859293318088342661125 3600911117497141564248961)
                    ·
                      refine ⟨2700683338122856173186721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3600911117497141564248961 2700683338122856173186721)
                      ·
                        rfl

theorem cell23_5259562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_5259562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259562 prefixEnd_5259562 := by exact prefixLift 5259562
  have htrace : WordTrace (prefixWord ++ tailWord_5259562) baseStart_5259562 baseEnd_5259562 := by
    simpa [prefixWord, tailWord_5259562, baseEnd_5259562] using wordTrace_append hprefix tailTrace_5259562
  have hstable : (prefixWord ++ tailWord_5259562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259562).length < 2 ^ (prefixWord ++ tailWord_5259562).sum := by decide
  have hdescent : baseEnd_5259562 < baseStart_5259562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259566 : List Nat := [4, 1, 3, 3, 1, 1, 3, 1, 1, 3, 2]
def baseStart_5259566 : Nat := 118140960795 + 5259566 * 2 ^ 59
def prefixEnd_5259566 : Nat := 4983230072969 + 3 ^ 40 * 5259566 * 2
def baseEnd_5259566 : Nat := 2700685392045474157536703

theorem tailTrace_5259566 : CollatzResearch.WordTrace tailWord_5259566 prefixEnd_5259566 2700685392045474157536703 := by
  unfold tailWord_5259566
  simp only [CollatzResearch.WordTrace]
  refine ⟨23979016457937264900448819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127888087775665412802393701 23979016457937264900448819)
  ·
    refine ⟨35968524686905897350673229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23979016457937264900448819 35968524686905897350673229)
    ·
      refine ⟨13488196757589711506502461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35968524686905897350673229 13488196757589711506502461)
      ·
        refine ⟨5058073784096141814938423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13488196757589711506502461 5058073784096141814938423)
        ·
          refine ⟨7587110676144212722407635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5058073784096141814938423 7587110676144212722407635)
          ·
            refine ⟨11380666014216319083611453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7587110676144212722407635 11380666014216319083611453)
            ·
              refine ⟨4267749755331119656354295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11380666014216319083611453 4267749755331119656354295)
              ·
                refine ⟨6401624632996679484531443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4267749755331119656354295 6401624632996679484531443)
                ·
                  refine ⟨9602436949495019226797165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6401624632996679484531443 9602436949495019226797165)
                  ·
                    refine ⟨3600913856060632210048937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9602436949495019226797165 3600913856060632210048937)
                    ·
                      refine ⟨2700685392045474157536703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3600913856060632210048937 2700685392045474157536703)
                      ·
                        rfl

theorem cell23_5259566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_5259566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259566 prefixEnd_5259566 := by exact prefixLift 5259566
  have htrace : WordTrace (prefixWord ++ tailWord_5259566) baseStart_5259566 baseEnd_5259566 := by
    simpa [prefixWord, tailWord_5259566, baseEnd_5259566] using wordTrace_append hprefix tailTrace_5259566
  have hstable : (prefixWord ++ tailWord_5259566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259566).length < 2 ^ (prefixWord ++ tailWord_5259566).sum := by decide
  have hdescent : baseEnd_5259566 < baseStart_5259566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259591 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 5]
def baseStart_5259591 : Nat := 118140960795 + 5259591 * 2 ^ 59
def prefixEnd_5259591 : Nat := 4983230072969 + 3 ^ 40 * 5259591 * 2
def baseEnd_5259591 : Nat := 2700698229061836559724087

theorem tailTrace_5259591 : CollatzResearch.WordTrace tailWord_5259591 prefixEnd_5259591 2700698229061836559724087 := by
  unfold tailWord_5259591
  simp only [CollatzResearch.WordTrace]
  refine ⟨191833043488407548473250627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127888695658938365648833751 191833043488407548473250627)
  ·
    refine ⟨287749565232611322709875941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191833043488407548473250627 287749565232611322709875941)
    ·
      refine ⟨53953043481114623008101739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 287749565232611322709875941 53953043481114623008101739)
      ·
        refine ⟨80929565221671934512152609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53953043481114623008101739 80929565221671934512152609)
        ·
          refine ⟨60697173916253950884114457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80929565221671934512152609 60697173916253950884114457)
          ·
            refine ⟨45522880437190463163085843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60697173916253950884114457 45522880437190463163085843)
            ·
              refine ⟨68284320655785694744628765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45522880437190463163085843 68284320655785694744628765)
              ·
                refine ⟨25606620245919635529235787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68284320655785694744628765 25606620245919635529235787)
                ·
                  refine ⟨38409930368879453293853681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25606620245919635529235787 38409930368879453293853681)
                  ·
                    refine ⟨28807447776659589970390261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38409930368879453293853681 28807447776659589970390261)
                    ·
                      refine ⟨2700698229061836559724087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28807447776659589970390261 2700698229061836559724087)
                      ·
                        rfl

theorem cell23_5259591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_5259591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259591 prefixEnd_5259591 := by exact prefixLift 5259591
  have htrace : WordTrace (prefixWord ++ tailWord_5259591) baseStart_5259591 baseEnd_5259591 := by
    simpa [prefixWord, tailWord_5259591, baseEnd_5259591] using wordTrace_append hprefix tailTrace_5259591
  have hstable : (prefixWord ++ tailWord_5259591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259591).length < 2 ^ (prefixWord ++ tailWord_5259591).sum := by decide
  have hdescent : baseEnd_5259591 < baseStart_5259591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259645 : List Nat := [1, 4, 1, 1, 2, 4, 2, 1, 3, 4]
def baseStart_5259645 : Nat := 118140960795 + 5259645 * 2 ^ 59
def prefixEnd_5259645 : Nat := 4983230072969 + 3 ^ 40 * 5259645 * 2
def baseEnd_5259645 : Nat := 900241985672393116149613

theorem tailTrace_5259645 : CollatzResearch.WordTrace tailWord_5259645 prefixEnd_5259645 900241985672393116149613 := by
  unfold tailWord_5259645
  simp only [CollatzResearch.WordTrace]
  refine ⟨191835013030211915695716389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127890008686807943797144259 191835013030211915695716389)
  ·
    refine ⟨35969064943164734192946823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191835013030211915695716389 35969064943164734192946823)
    ·
      refine ⟨53953597414747101289420235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35969064943164734192946823 53953597414747101289420235)
      ·
        refine ⟨80930396122120651934130353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53953597414747101289420235 80930396122120651934130353)
        ·
          refine ⟨60697797091590488950597765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80930396122120651934130353 60697797091590488950597765)
          ·
            refine ⟨11380836954673216678237081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60697797091590488950597765 11380836954673216678237081)
            ·
              refine ⟨8535627716004912508677811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11380836954673216678237081 8535627716004912508677811)
              ·
                refine ⟨12803441574007368763016717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8535627716004912508677811 12803441574007368763016717)
                ·
                  refine ⟨4801290590252763286131269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12803441574007368763016717 4801290590252763286131269)
                  ·
                    refine ⟨900241985672393116149613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4801290590252763286131269 900241985672393116149613)
                    ·
                      rfl

theorem cell23_5259645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_5259645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259645 prefixEnd_5259645 := by exact prefixLift 5259645
  have htrace : WordTrace (prefixWord ++ tailWord_5259645) baseStart_5259645 baseEnd_5259645 := by
    simpa [prefixWord, tailWord_5259645, baseEnd_5259645] using wordTrace_append hprefix tailTrace_5259645
  have hstable : (prefixWord ++ tailWord_5259645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259645).length < 2 ^ (prefixWord ++ tailWord_5259645).sum := by decide
  have hdescent : baseEnd_5259645 < baseStart_5259645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259752 : List Nat := [2, 1, 4, 1, 1, 4, 2, 2, 2, 4]
def baseStart_5259752 : Nat := 118140960795 + 5259752 * 2 ^ 59
def prefixEnd_5259752 : Nat := 4983230072969 + 3 ^ 40 * 5259752 * 2
def baseEnd_5259752 : Nat := 900260299815736809936949

theorem tailTrace_5259752 : CollatzResearch.WordTrace tailWord_5259752 prefixEnd_5259752 900260299815736809936949 := by
  unfold tailWord_5259752
  simp only [CollatzResearch.WordTrace]
  refine ⟨95919457820412136484930755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127892610427216181979907673 95919457820412136484930755)
  ·
    refine ⟨143879186730618204727396133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95919457820412136484930755 143879186730618204727396133)
    ·
      refine ⟨26977347511990913386386775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143879186730618204727396133 26977347511990913386386775)
      ·
        refine ⟨40466021267986370079580163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26977347511990913386386775 40466021267986370079580163)
        ·
          refine ⟨60699031901979555119370245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40466021267986370079580163 60699031901979555119370245)
          ·
            refine ⟨11381068481621166584881921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60699031901979555119370245 11381068481621166584881921)
            ·
              refine ⟨8535801361215874938661441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11381068481621166584881921 8535801361215874938661441)
              ·
                refine ⟨6401851020911906203996081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8535801361215874938661441 6401851020911906203996081)
                ·
                  refine ⟨4801388265683929652997061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6401851020911906203996081 4801388265683929652997061)
                  ·
                    refine ⟨900260299815736809936949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4801388265683929652997061 900260299815736809936949)
                    ·
                      rfl

theorem cell23_5259752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_5259752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259752 prefixEnd_5259752 := by exact prefixLift 5259752
  have htrace : WordTrace (prefixWord ++ tailWord_5259752) baseStart_5259752 baseEnd_5259752 := by
    simpa [prefixWord, tailWord_5259752, baseEnd_5259752] using wordTrace_append hprefix tailTrace_5259752
  have hstable : (prefixWord ++ tailWord_5259752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259752).length < 2 ^ (prefixWord ++ tailWord_5259752).sum := by decide
  have hdescent : baseEnd_5259752 < baseStart_5259752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259775 : List Nat := [1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 3]
def baseStart_5259775 : Nat := 118140960795 + 5259775 * 2 ^ 59
def prefixEnd_5259775 : Nat := 4983230072969 + 3 ^ 40 * 5259775 * 2
def baseEnd_5259775 : Nat := 2700792709502263839823241

theorem tailTrace_5259775 : CollatzResearch.WordTrace tailWord_5259775 prefixEnd_5259775 2700792709502263839823241 := by
  unfold tailWord_5259775
  simp only [CollatzResearch.WordTrace]
  refine ⟨191839754519740947897948779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127893169679827298598632519 191839754519740947897948779)
  ·
    refine ⟨287759631779611421846923169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191839754519740947897948779 287759631779611421846923169)
    ·
      refine ⟨215819723834708566385192377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287759631779611421846923169 215819723834708566385192377)
      ·
        refine ⟨161864792876031424788894283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215819723834708566385192377 161864792876031424788894283)
        ·
          refine ⟨242797189314047137183341425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161864792876031424788894283 242797189314047137183341425)
          ·
            refine ⟨182097891985535352887506069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242797189314047137183341425 182097891985535352887506069)
            ·
              refine ⟨8535838686821969666601847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 182097891985535352887506069 8535838686821969666601847)
              ·
                refine ⟨12803758030232954499902771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8535838686821969666601847 12803758030232954499902771)
                ·
                  refine ⟨19205637045349431749854157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12803758030232954499902771 19205637045349431749854157)
                  ·
                    refine ⟨7202113892006036906195309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19205637045349431749854157 7202113892006036906195309)
                    ·
                      refine ⟨2700792709502263839823241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7202113892006036906195309 2700792709502263839823241)
                      ·
                        rfl

theorem cell23_5259775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 3].length) (baseStart_5259775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259775 prefixEnd_5259775 := by exact prefixLift 5259775
  have htrace : WordTrace (prefixWord ++ tailWord_5259775) baseStart_5259775 baseEnd_5259775 := by
    simpa [prefixWord, tailWord_5259775, baseEnd_5259775] using wordTrace_append hprefix tailTrace_5259775
  have hstable : (prefixWord ++ tailWord_5259775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259775).length < 2 ^ (prefixWord ++ tailWord_5259775).sum := by decide
  have hdescent : baseEnd_5259775 < baseStart_5259775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259789 : List Nat := [1, 7, 1, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_5259789 : Nat := 118140960795 + 5259789 * 2 ^ 59
def prefixEnd_5259789 : Nat := 4983230072969 + 3 ^ 40 * 5259789 * 2
def baseEnd_5259789 : Nat := 2700799898231426785048177

theorem tailTrace_5259789 : CollatzResearch.WordTrace tailWord_5259789 prefixEnd_5259789 2700799898231426785048177 := by
  unfold tailWord_5259789
  simp only [CollatzResearch.WordTrace]
  refine ⟨191840265141690228288958421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127893510094460152192638947 191840265141690228288958421)
  ·
    refine ⟨4496256214258364725522463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 191840265141690228288958421 4496256214258364725522463)
    ·
      refine ⟨6744384321387547088283695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4496256214258364725522463 6744384321387547088283695)
      ·
        refine ⟨10116576482081320632425543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6744384321387547088283695 10116576482081320632425543)
        ·
          refine ⟨15174864723121980948638315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10116576482081320632425543 15174864723121980948638315)
          ·
            refine ⟨22762297084682971422957473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15174864723121980948638315 22762297084682971422957473)
            ·
              refine ⟨17071722813512228567218105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22762297084682971422957473 17071722813512228567218105)
              ·
                refine ⟨12803792110134171425413579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17071722813512228567218105 12803792110134171425413579)
                ·
                  refine ⟨19205688165201257138120369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12803792110134171425413579 19205688165201257138120369)
                  ·
                    refine ⟨14404266123900942853590277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19205688165201257138120369 14404266123900942853590277)
                    ·
                      refine ⟨2700799898231426785048177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14404266123900942853590277 2700799898231426785048177)
                      ·
                        rfl

theorem cell23_5259789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_5259789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259789 prefixEnd_5259789 := by exact prefixLift 5259789
  have htrace : WordTrace (prefixWord ++ tailWord_5259789) baseStart_5259789 baseEnd_5259789 := by
    simpa [prefixWord, tailWord_5259789, baseEnd_5259789] using wordTrace_append hprefix tailTrace_5259789
  have hstable : (prefixWord ++ tailWord_5259789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259789).length < 2 ^ (prefixWord ++ tailWord_5259789).sum := by decide
  have hdescent : baseEnd_5259789 < baseStart_5259789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259796 : List Nat := [2, 4, 3, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_5259796 : Nat := 118140960795 + 5259796 * 2 ^ 59
def prefixEnd_5259796 : Nat := 4983230072969 + 3 ^ 40 * 5259796 * 2
def baseEnd_5259796 : Nat := 2700803492596008257660645

theorem tailTrace_5259796 : CollatzResearch.WordTrace tailWord_5259796 prefixEnd_5259796 2700803492596008257660645 := by
  unfold tailWord_5259796
  simp only [CollatzResearch.WordTrace]
  refine ⟨95920260226332434242231621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127893680301776578989642161 95920260226332434242231621)
  ·
    refine ⟨17985048792437331420418429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95920260226332434242231621 17985048792437331420418429)
    ·
      refine ⟨6744393297163999282656911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17985048792437331420418429 6744393297163999282656911)
      ·
        refine ⟨10116589945745998923985367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6744393297163999282656911 10116589945745998923985367)
        ·
          refine ⟨15174884918618998385978051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10116589945745998923985367 15174884918618998385978051)
          ·
            refine ⟨22762327377928497578967077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15174884918618998385978051 22762327377928497578967077)
            ·
              refine ⟨4267936383361593296056327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22762327377928497578967077 4267936383361593296056327)
              ·
                refine ⟨6401904575042389944084491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4267936383361593296056327 6401904575042389944084491)
                ·
                  refine ⟨9602856862563584916126737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6401904575042389944084491 9602856862563584916126737)
                  ·
                    refine ⟨7202142646922688687095053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9602856862563584916126737 7202142646922688687095053)
                    ·
                      refine ⟨2700803492596008257660645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7202142646922688687095053 2700803492596008257660645)
                      ·
                        rfl

theorem cell23_5259796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_5259796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259796 prefixEnd_5259796 := by exact prefixLift 5259796
  have htrace : WordTrace (prefixWord ++ tailWord_5259796) baseStart_5259796 baseEnd_5259796 := by
    simpa [prefixWord, tailWord_5259796, baseEnd_5259796] using wordTrace_append hprefix tailTrace_5259796
  have hstable : (prefixWord ++ tailWord_5259796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259796).length < 2 ^ (prefixWord ++ tailWord_5259796).sum := by decide
  have hdescent : baseEnd_5259796 < baseStart_5259796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259844 : List Nat := [2, 3, 5, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_5259844 : Nat := 118140960795 + 5259844 * 2 ^ 59
def prefixEnd_5259844 : Nat := 4983230072969 + 3 ^ 40 * 5259844 * 2
def baseEnd_5259844 : Nat := 2700828139667424069860425

theorem tailTrace_5259844 : CollatzResearch.WordTrace tailWord_5259844 prefixEnd_5259844 2700828139667424069860425 := by
  unfold tailWord_5259844
  simp only [CollatzResearch.WordTrace]
  refine ⟨95921135578245486341105293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127894847437660648454807057 95921135578245486341105293)
  ·
    refine ⟨35970425841842057377914485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95921135578245486341105293 35970425841842057377914485)
    ·
      refine ⟨3372227422672692879179483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35970425841842057377914485 3372227422672692879179483)
      ·
        refine ⟨5058341134009039318769225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3372227422672692879179483 5058341134009039318769225)
        ·
          refine ⟨3793755850506779489076919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5058341134009039318769225 3793755850506779489076919)
          ·
            refine ⟨5690633775760169233615379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3793755850506779489076919 5690633775760169233615379)
            ·
              refine ⟨8535950663640253850423069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5690633775760169233615379 8535950663640253850423069)
              ·
                refine ⟨3200981498865095193908651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8535950663640253850423069 3200981498865095193908651)
                ·
                  refine ⟨4801472248297642790862977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3200981498865095193908651 4801472248297642790862977)
                  ·
                    refine ⟨3601104186223232093147233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4801472248297642790862977 3601104186223232093147233)
                    ·
                      refine ⟨2700828139667424069860425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3601104186223232093147233 2700828139667424069860425)
                      ·
                        rfl

theorem cell23_5259844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_5259844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259844 prefixEnd_5259844 := by exact prefixLift 5259844
  have htrace : WordTrace (prefixWord ++ tailWord_5259844) baseStart_5259844 baseEnd_5259844 := by
    simpa [prefixWord, tailWord_5259844, baseEnd_5259844] using wordTrace_append hprefix tailTrace_5259844
  have hstable : (prefixWord ++ tailWord_5259844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259844).length < 2 ^ (prefixWord ++ tailWord_5259844).sum := by decide
  have hdescent : baseEnd_5259844 < baseStart_5259844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259915 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 7, 4]
def baseStart_5259915 : Nat := 118140960795 + 5259915 * 2 ^ 59
def prefixEnd_5259915 : Nat := 4983230072969 + 3 ^ 40 * 5259915 * 2
def baseEnd_5259915 : Nat := 900288198931297764024199

theorem tailTrace_5259915 : CollatzResearch.WordTrace tailWord_5259915 prefixEnd_5259915 900288198931297764024199 := by
  unfold tailWord_5259915
  simp only [CollatzResearch.WordTrace]
  refine ⟨191844860739233751808045199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127896573826155834538696799 191844860739233751808045199)
  ·
    refine ⟨287767291108850627712067799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191844860739233751808045199 287767291108850627712067799)
    ·
      refine ⟨431650936663275941568101699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287767291108850627712067799 431650936663275941568101699)
      ·
        refine ⟨647476404994913912352152549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431650936663275941568101699 647476404994913912352152549)
        ·
          refine ⟨121401825936546358566028603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 647476404994913912352152549 121401825936546358566028603)
          ·
            refine ⟨182102738904819537849042905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121401825936546358566028603 182102738904819537849042905)
            ·
              refine ⟨136577054178614653386782179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182102738904819537849042905 136577054178614653386782179)
              ·
                refine ⟨204865581267921980080173269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136577054178614653386782179 204865581267921980080173269)
                ·
                  refine ⟨4801537060966921408129061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 204865581267921980080173269 4801537060966921408129061)
                  ·
                    refine ⟨900288198931297764024199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4801537060966921408129061 900288198931297764024199)
                    ·
                      rfl

theorem cell23_5259915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 4].length) (baseStart_5259915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259915 prefixEnd_5259915 := by exact prefixLift 5259915
  have htrace : WordTrace (prefixWord ++ tailWord_5259915) baseStart_5259915 baseEnd_5259915 := by
    simpa [prefixWord, tailWord_5259915, baseEnd_5259915] using wordTrace_append hprefix tailTrace_5259915
  have hstable : (prefixWord ++ tailWord_5259915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259915).length < 2 ^ (prefixWord ++ tailWord_5259915).sum := by decide
  have hdescent : baseEnd_5259915 < baseStart_5259915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259925 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 5, 4, 3]
def baseStart_5259925 : Nat := 118140960795 + 5259925 * 2 ^ 59
def prefixEnd_5259925 : Nat := 4983230072969 + 3 ^ 40 * 5259925 * 2
def baseEnd_5259925 : Nat := 2700869731600438252947551

theorem tailTrace_5259925 : CollatzResearch.WordTrace tailWord_5259925 prefixEnd_5259925 2700869731600438252947551 := by
  unfold tailWord_5259925
  simp only [CollatzResearch.WordTrace]
  refine ⟨191845225469197523515909229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127896816979465015677272819 191845225469197523515909229)
  ·
    refine ⟨71941959550949071318465961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191845225469197523515909229 71941959550949071318465961)
    ·
      refine ⟨53956469663211803488849471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71941959550949071318465961 53956469663211803488849471)
      ·
        refine ⟨80934704494817705233274207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53956469663211803488849471 80934704494817705233274207)
        ·
          refine ⟨121402056742226557849911311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80934704494817705233274207 121402056742226557849911311)
          ·
            refine ⟨182103085113339836774866967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121402056742226557849911311 182103085113339836774866967)
            ·
              refine ⟨273154627670009755162300451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182103085113339836774866967 273154627670009755162300451)
              ·
                refine ⟨409731941505014632743450677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273154627670009755162300451 409731941505014632743450677)
                ·
                  refine ⟨38412369516095121819698501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 409731941505014632743450677 38412369516095121819698501)
                  ·
                    refine ⟨7202319284267835341193469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38412369516095121819698501 7202319284267835341193469)
                    ·
                      refine ⟨2700869731600438252947551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7202319284267835341193469 2700869731600438252947551)
                      ·
                        rfl

theorem cell23_5259925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_5259925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259925 prefixEnd_5259925 := by exact prefixLift 5259925
  have htrace : WordTrace (prefixWord ++ tailWord_5259925) baseStart_5259925 baseEnd_5259925 := by
    simpa [prefixWord, tailWord_5259925, baseEnd_5259925] using wordTrace_append hprefix tailTrace_5259925
  have hstable : (prefixWord ++ tailWord_5259925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259925).length < 2 ^ (prefixWord ++ tailWord_5259925).sum := by decide
  have hdescent : baseEnd_5259925 < baseStart_5259925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259949 : List Nat := [1, 5, 2, 1, 1, 3, 1, 2, 3, 4]
def baseStart_5259949 : Nat := 118140960795 + 5259949 * 2 ^ 59
def prefixEnd_5259949 : Nat := 4983230072969 + 3 ^ 40 * 5259949 * 2
def baseEnd_5259949 : Nat := 900294018378715386349147

theorem tailTrace_5259949 : CollatzResearch.WordTrace tailWord_5259949 prefixEnd_5259949 900294018378715386349147 := by
  unfold tailWord_5259949
  simp only [CollatzResearch.WordTrace]
  refine ⟨191846100821110575614782901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127897400547407050409855267 191846100821110575614782901)
  ·
    refine ⟨17985571951979116463885897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191846100821110575614782901 17985571951979116463885897)
    ·
      refine ⟨13489178963984337347914423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17985571951979116463885897 13489178963984337347914423)
      ·
        refine ⟨20233768445976506021871635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13489178963984337347914423 20233768445976506021871635)
        ·
          refine ⟨30350652668964759032807453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20233768445976506021871635 30350652668964759032807453)
          ·
            refine ⟨11381494750861784637302795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30350652668964759032807453 11381494750861784637302795)
            ·
              refine ⟨17072242126292676955954193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11381494750861784637302795 17072242126292676955954193)
              ·
                refine ⟨12804181594719507716965645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17072242126292676955954193 12804181594719507716965645)
                ·
                  refine ⟨4801568098019815393862117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12804181594719507716965645 4801568098019815393862117)
                  ·
                    refine ⟨900294018378715386349147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4801568098019815393862117 900294018378715386349147)
                    ·
                      rfl

theorem cell23_5259949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_5259949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259949 prefixEnd_5259949 := by exact prefixLift 5259949
  have htrace : WordTrace (prefixWord ++ tailWord_5259949) baseStart_5259949 baseEnd_5259949 := by
    simpa [prefixWord, tailWord_5259949, baseEnd_5259949] using wordTrace_append hprefix tailTrace_5259949
  have hstable : (prefixWord ++ tailWord_5259949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259949).length < 2 ^ (prefixWord ++ tailWord_5259949).sum := by decide
  have hdescent : baseEnd_5259949 < baseStart_5259949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259966 : List Nat := [4, 2, 1, 1, 2, 1, 4, 3, 1, 4]
def baseStart_5259966 : Nat := 118140960795 + 5259966 * 2 ^ 59
def prefixEnd_5259966 : Nat := 4983230072969 + 3 ^ 40 * 5259966 * 2
def baseEnd_5259966 : Nat := 900296928102424197511621

theorem tailTrace_5259966 : CollatzResearch.WordTrace tailWord_5259966 prefixEnd_5259966 900296928102424197511621 := by
  unfold tailWord_5259966
  simp only [CollatzResearch.WordTrace]
  refine ⟨23980840107756123439768969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127897813908032658345434501 23980840107756123439768969)
  ·
    refine ⟨17985630080817092579826727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23980840107756123439768969 17985630080817092579826727)
    ·
      refine ⟨26978445121225638869740091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17985630080817092579826727 26978445121225638869740091)
      ·
        refine ⟨40467667681838458304610137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26978445121225638869740091 40467667681838458304610137)
        ·
          refine ⟨30350750761378843728457603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40467667681838458304610137 30350750761378843728457603)
          ·
            refine ⟨45526126142068265592686405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30350750761378843728457603 45526126142068265592686405)
            ·
              refine ⟨8536148651637799798628701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45526126142068265592686405 8536148651637799798628701)
              ·
                refine ⟨3201055744364174924485763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8536148651637799798628701 3201055744364174924485763)
                ·
                  refine ⟨4801583616546262386728645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3201055744364174924485763 4801583616546262386728645)
                  ·
                    refine ⟨900296928102424197511621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4801583616546262386728645 900296928102424197511621)
                    ·
                      rfl

theorem cell23_5259966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_5259966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259966 prefixEnd_5259966 := by exact prefixLift 5259966
  have htrace : WordTrace (prefixWord ++ tailWord_5259966) baseStart_5259966 baseEnd_5259966 := by
    simpa [prefixWord, tailWord_5259966, baseEnd_5259966] using wordTrace_append hprefix tailTrace_5259966
  have hstable : (prefixWord ++ tailWord_5259966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259966).length < 2 ^ (prefixWord ++ tailWord_5259966).sum := by decide
  have hdescent : baseEnd_5259966 < baseStart_5259966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259975 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 5, 5]
def baseStart_5259975 : Nat := 118140960795 + 5259975 * 2 ^ 59
def prefixEnd_5259975 : Nat := 4983230072969 + 3 ^ 40 * 5259975 * 2
def baseEnd_5259975 : Nat := 900298468544387685774107

theorem tailTrace_5259975 : CollatzResearch.WordTrace tailWord_5259975 prefixEnd_5259975 900298468544387685774107 := by
  unfold tailWord_5259975
  simp only [CollatzResearch.WordTrace]
  refine ⟨191847049119016382055229379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127898032746010921370152919 191847049119016382055229379)
  ·
    refine ⟨287770573678524573082844069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191847049119016382055229379 287770573678524573082844069)
    ·
      refine ⟨53956982564723357453033263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 287770573678524573082844069 53956982564723357453033263)
      ·
        refine ⟨80935473847085036179549895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53956982564723357453033263 80935473847085036179549895)
        ·
          refine ⟨121403210770627554269324843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80935473847085036179549895 121403210770627554269324843)
          ·
            refine ⟨182104816155941331403987265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121403210770627554269324843 182104816155941331403987265)
            ·
              refine ⟨136578612116955998552990449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182104816155941331403987265 136578612116955998552990449)
              ·
                refine ⟨102433959087716998914742837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136578612116955998552990449 102433959087716998914742837)
                ·
                  refine ⟨9603183664473468648257141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102433959087716998914742837 9603183664473468648257141)
                  ·
                    refine ⟨900298468544387685774107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9603183664473468648257141 900298468544387685774107)
                    ·
                      rfl

theorem cell23_5259975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_5259975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259975 prefixEnd_5259975 := by exact prefixLift 5259975
  have htrace : WordTrace (prefixWord ++ tailWord_5259975) baseStart_5259975 baseEnd_5259975 := by
    simpa [prefixWord, tailWord_5259975, baseEnd_5259975] using wordTrace_append hprefix tailTrace_5259975
  have hstable : (prefixWord ++ tailWord_5259975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259975).length < 2 ^ (prefixWord ++ tailWord_5259975).sum := by decide
  have hdescent : baseEnd_5259975 < baseStart_5259975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5259996 : List Nat := [2, 2, 5, 1, 1, 2, 3, 1, 6]
def baseStart_5259996 : Nat := 118140960795 + 5259996 * 2 ^ 59
def prefixEnd_5259996 : Nat := 4983230072969 + 3 ^ 40 * 5259996 * 2
def baseEnd_5259996 : Nat := 300100687636323052795525

theorem tailTrace_5259996 : CollatzResearch.WordTrace tailWord_5259996 prefixEnd_5259996 300100687636323052795525 := by
  unfold tailWord_5259996
  simp only [CollatzResearch.WordTrace]
  refine ⟨95923907525970151320871921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127898543367960201761162561 95923907525970151320871921)
  ·
    refine ⟨71942930644477613490653941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95923907525970151320871921 71942930644477613490653941)
    ·
      refine ⟨6744649747919776264748807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71942930644477613490653941 6744649747919776264748807)
      ·
        refine ⟨10116974621879664397123211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6744649747919776264748807 10116974621879664397123211)
        ·
          refine ⟨15175461932819496595684817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10116974621879664397123211 15175461932819496595684817)
          ·
            refine ⟨11381596449614622446763613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15175461932819496595684817 11381596449614622446763613)
            ·
              refine ⟨4268098668605483417536355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11381596449614622446763613 4268098668605483417536355)
              ·
                refine ⟨6402148002908225126304533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4268098668605483417536355 6402148002908225126304533)
                ·
                  refine ⟨300100687636323052795525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6402148002908225126304533 300100687636323052795525)
                  ·
                    rfl

theorem cell23_5259996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 6].length) (baseStart_5259996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5259996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5259996 prefixEnd_5259996 := by exact prefixLift 5259996
  have htrace : WordTrace (prefixWord ++ tailWord_5259996) baseStart_5259996 baseEnd_5259996 := by
    simpa [prefixWord, tailWord_5259996, baseEnd_5259996] using wordTrace_append hprefix tailTrace_5259996
  have hstable : (prefixWord ++ tailWord_5259996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5259996).length < 2 ^ (prefixWord ++ tailWord_5259996).sum := by decide
  have hdescent : baseEnd_5259996 < baseStart_5259996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5259996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260012 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 1, 8, 2]
def baseStart_5260012 : Nat := 118140960795 + 5260012 * 2 ^ 59
def prefixEnd_5260012 : Nat := 4983230072969 + 3 ^ 40 * 5260012 * 2
def baseEnd_5260012 : Nat := 2700914404417379412559651

theorem tailTrace_5260012 : CollatzResearch.WordTrace tailWord_5260012 prefixEnd_5260012 2700914404417379412559651 := by
  unfold tailWord_5260012
  simp only [CollatzResearch.WordTrace]
  refine ⟨95924199309941168687163145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127898932413254891582884193 95924199309941168687163145)
  ·
    refine ⟨71943149482455876515372359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95924199309941168687163145 71943149482455876515372359)
    ·
      refine ⟨107914724223683814773058539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71943149482455876515372359 107914724223683814773058539)
      ·
        refine ⟨161872086335525722159587809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107914724223683814773058539 161872086335525722159587809)
        ·
          refine ⟨121404064751644291619690857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161872086335525722159587809 121404064751644291619690857)
          ·
            refine ⟨91053048563733218714768143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121404064751644291619690857 91053048563733218714768143)
            ·
              refine ⟨136579572845599828072152215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91053048563733218714768143 136579572845599828072152215)
              ·
                refine ⟨204869359268399742108228323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136579572845599828072152215 204869359268399742108228323)
                ·
                  refine ⟨307304038902599613162342485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204869359268399742108228323 307304038902599613162342485)
                  ·
                    refine ⟨3601219205889839216746201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 307304038902599613162342485 3601219205889839216746201)
                    ·
                      refine ⟨2700914404417379412559651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3601219205889839216746201 2700914404417379412559651)
                      ·
                        rfl

theorem cell23_5260012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 8, 2].length) (baseStart_5260012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260012 prefixEnd_5260012 := by exact prefixLift 5260012
  have htrace : WordTrace (prefixWord ++ tailWord_5260012) baseStart_5260012 baseEnd_5260012 := by
    simpa [prefixWord, tailWord_5260012, baseEnd_5260012] using wordTrace_append hprefix tailTrace_5260012
  have hstable : (prefixWord ++ tailWord_5260012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260012).length < 2 ^ (prefixWord ++ tailWord_5260012).sum := by decide
  have hdescent : baseEnd_5260012 < baseStart_5260012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260022 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 3, 6]
def baseStart_5260022 : Nat := 118140960795 + 5260022 * 2 ^ 59
def prefixEnd_5260022 : Nat := 4983230072969 + 3 ^ 40 * 5260022 * 2
def baseEnd_5260022 : Nat := 900306513074641457811535

theorem tailTrace_5260022 : CollatzResearch.WordTrace tailWord_5260022 prefixEnd_5260022 900306513074641457811535 := by
  unfold tailWord_5260022
  simp only [CollatzResearch.WordTrace]
  refine ⟨11990547709365381817636895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127899175566564072721460213 11990547709365381817636895)
  ·
    refine ⟨17985821564048072726455343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11990547709365381817636895 17985821564048072726455343)
    ·
      refine ⟨26978732346072109089683015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17985821564048072726455343 26978732346072109089683015)
      ·
        refine ⟨40468098519108163634524523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26978732346072109089683015 40468098519108163634524523)
        ·
          refine ⟨60702147778662245451786785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40468098519108163634524523 60702147778662245451786785)
          ·
            refine ⟨45526610833996684088840089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60702147778662245451786785 45526610833996684088840089)
            ·
              refine ⟨34144958125497513066630067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45526610833996684088840089 34144958125497513066630067)
              ·
                refine ⟨51217437188246269599945101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34144958125497513066630067 51217437188246269599945101)
                ·
                  refine ⟨19206538945592351099979413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51217437188246269599945101 19206538945592351099979413)
                  ·
                    refine ⟨900306513074641457811535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19206538945592351099979413 900306513074641457811535)
                    ·
                      rfl

theorem cell23_5260022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_5260022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260022 prefixEnd_5260022 := by exact prefixLift 5260022
  have htrace : WordTrace (prefixWord ++ tailWord_5260022) baseStart_5260022 baseEnd_5260022 := by
    simpa [prefixWord, tailWord_5260022, baseEnd_5260022] using wordTrace_append hprefix tailTrace_5260022
  have hstable : (prefixWord ++ tailWord_5260022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260022).length < 2 ^ (prefixWord ++ tailWord_5260022).sum := by decide
  have hdescent : baseEnd_5260022 < baseStart_5260022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260039 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 4, 4]
def baseStart_5260039 : Nat := 118140960795 + 5260039 * 2 ^ 59
def prefixEnd_5260039 : Nat := 4983230072969 + 3 ^ 40 * 5260039 * 2
def baseEnd_5260039 : Nat := 900309422798350268974009

theorem tailTrace_5260039 : CollatzResearch.WordTrace tailWord_5260039 prefixEnd_5260039 900309422798350268974009 := by
  unfold tailWord_5260039
  simp only [CollatzResearch.WordTrace]
  refine ⟨191849383390784520985559171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127899588927189680657039447 191849383390784520985559171)
  ·
    refine ⟨287774075086176781478338757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191849383390784520985559171 287774075086176781478338757)
    ·
      refine ⟨53957639078658146527188517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 287774075086176781478338757 53957639078658146527188517)
      ·
        refine ⟨10117057327248402473847847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53957639078658146527188517 10117057327248402473847847)
        ·
          refine ⟨15175585990872603710771771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10117057327248402473847847 15175585990872603710771771)
          ·
            refine ⟨22763378986308905566157657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15175585990872603710771771 22763378986308905566157657)
            ·
              refine ⟨17072534239731679174618243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22763378986308905566157657 17072534239731679174618243)
              ·
                refine ⟨25608801359597518761927365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17072534239731679174618243 25608801359597518761927365)
                ·
                  refine ⟨4801650254924534767861381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25608801359597518761927365 4801650254924534767861381)
                  ·
                    refine ⟨900309422798350268974009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4801650254924534767861381 900309422798350268974009)
                    ·
                      rfl

theorem cell23_5260039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_5260039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260039 prefixEnd_5260039 := by exact prefixLift 5260039
  have htrace : WordTrace (prefixWord ++ tailWord_5260039) baseStart_5260039 baseEnd_5260039 := by
    simpa [prefixWord, tailWord_5260039, baseEnd_5260039] using wordTrace_append hprefix tailTrace_5260039
  have hstable : (prefixWord ++ tailWord_5260039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260039).length < 2 ^ (prefixWord ++ tailWord_5260039).sum := by decide
  have hdescent : baseEnd_5260039 < baseStart_5260039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260066 : List Nat := [3, 3, 1, 1, 2, 2, 3, 2, 1, 2, 3]
def baseStart_5260066 : Nat := 118140960795 + 5260066 * 2 ^ 59
def prefixEnd_5260066 : Nat := 4983230072969 + 3 ^ 40 * 5260066 * 2
def baseEnd_5260066 : Nat := 2700942132372722201284403

theorem tailTrace_5260066 : CollatzResearch.WordTrace tailWord_5260066 prefixEnd_5260066 2700942132372722201284403 := by
  unfold tailWord_5260066
  simp only [CollatzResearch.WordTrace]
  refine ⟨47962592040421676149198013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127900245441124469731194701 47962592040421676149198013)
  ·
    refine ⟨17985972015158128555949255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47962592040421676149198013 17985972015158128555949255)
    ·
      refine ⟨26978958022737192833923883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17985972015158128555949255 26978958022737192833923883)
      ·
        refine ⟨40468437034105789250885825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26978958022737192833923883 40468437034105789250885825)
        ·
          refine ⟨30351327775579341938164369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40468437034105789250885825 30351327775579341938164369)
          ·
            refine ⟨22763495831684506453623277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30351327775579341938164369 22763495831684506453623277)
            ·
              refine ⟨8536310936881689920108729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22763495831684506453623277 8536310936881689920108729)
              ·
                refine ⟨6402233202661267440081547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8536310936881689920108729 6402233202661267440081547)
                ·
                  refine ⟨9603349803991901160122321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6402233202661267440081547 9603349803991901160122321)
                  ·
                    refine ⟨7202512352993925870091741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9603349803991901160122321 7202512352993925870091741)
                    ·
                      refine ⟨2700942132372722201284403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7202512352993925870091741 2700942132372722201284403)
                      ·
                        rfl

theorem cell23_5260066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_5260066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260066 prefixEnd_5260066 := by exact prefixLift 5260066
  have htrace : WordTrace (prefixWord ++ tailWord_5260066) baseStart_5260066 baseEnd_5260066 := by
    simpa [prefixWord, tailWord_5260066, baseEnd_5260066] using wordTrace_append hprefix tailTrace_5260066
  have hstable : (prefixWord ++ tailWord_5260066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260066).length < 2 ^ (prefixWord ++ tailWord_5260066).sum := by decide
  have hdescent : baseEnd_5260066 < baseStart_5260066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260097 : List Nat := [1, 2, 5, 3, 1, 1, 1, 4, 1, 2, 2]
def baseStart_5260097 : Nat := 118140960795 + 5260097 * 2 ^ 59
def prefixEnd_5260097 : Nat := 4983230072969 + 3 ^ 40 * 5260097 * 2
def baseEnd_5260097 : Nat := 2700958050273011579996761

theorem tailTrace_5260097 : CollatzResearch.WordTrace tailWord_5260097 prefixEnd_5260097 2700958050273011579996761 := by
  unfold tailWord_5260097
  simp only [CollatzResearch.WordTrace]
  refine ⟨191851498824574396891170545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127900999216382931260780363 191851498824574396891170545)
  ·
    refine ⟨143888624118430797668377909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191851498824574396891170545 143888624118430797668377909)
    ·
      refine ⟨13489558511102887281410429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143888624118430797668377909 13489558511102887281410429)
      ·
        refine ⟨5058584441663582730528911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13489558511102887281410429 5058584441663582730528911)
        ·
          refine ⟨7587876662495374095793367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5058584441663582730528911 7587876662495374095793367)
          ·
            refine ⟨11381814993743061143690051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7587876662495374095793367 11381814993743061143690051)
            ·
              refine ⟨17072722490614591715535077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11381814993743061143690051 17072722490614591715535077)
              ·
                refine ⟨3201135466990235946662827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17072722490614591715535077 3201135466990235946662827)
                ·
                  refine ⟨4801703200485353919994241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3201135466990235946662827 4801703200485353919994241)
                  ·
                    refine ⟨3601277400364015439995681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4801703200485353919994241 3601277400364015439995681)
                    ·
                      refine ⟨2700958050273011579996761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3601277400364015439995681 2700958050273011579996761)
                      ·
                        rfl

theorem cell23_5260097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_5260097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260097 prefixEnd_5260097 := by exact prefixLift 5260097
  have htrace : WordTrace (prefixWord ++ tailWord_5260097) baseStart_5260097 baseEnd_5260097 := by
    simpa [prefixWord, tailWord_5260097, baseEnd_5260097] using wordTrace_append hprefix tailTrace_5260097
  have hstable : (prefixWord ++ tailWord_5260097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260097).length < 2 ^ (prefixWord ++ tailWord_5260097).sum := by decide
  have hdescent : baseEnd_5260097 < baseStart_5260097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260136 : List Nat := [2, 1, 4, 2, 1, 2, 2, 2, 1, 4, 2]
def baseStart_5260136 : Nat := 118140960795 + 5260136 * 2 ^ 59
def prefixEnd_5260136 : Nat := 4983230072969 + 3 ^ 40 * 5260136 * 2
def baseEnd_5260136 : Nat := 2700978076018536927409081

theorem tailTrace_5260136 : CollatzResearch.WordTrace tailWord_5260136 prefixEnd_5260136 2700978076018536927409081 := by
  unfold tailWord_5260136
  simp only [CollatzResearch.WordTrace]
  refine ⟨95926460635716553275920131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127901947514288737701226841 95926460635716553275920131)
  ·
    refine ⟨143889690953574829913880197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95926460635716553275920131 143889690953574829913880197)
    ·
      refine ⟨26979317053795280608852537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143889690953574829913880197 26979317053795280608852537)
      ·
        refine ⟨20234487790346460456639403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26979317053795280608852537 20234487790346460456639403)
        ·
          refine ⟨30351731685519690684959105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20234487790346460456639403 30351731685519690684959105)
          ·
            refine ⟨22763798764139768013719329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30351731685519690684959105 22763798764139768013719329)
            ·
              refine ⟨17072849073104826010289497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22763798764139768013719329 17072849073104826010289497)
              ·
                refine ⟨12804636804828619507717123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17072849073104826010289497 12804636804828619507717123)
                ·
                  refine ⟨19206955207242929261575685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12804636804828619507717123 19206955207242929261575685)
                  ·
                    refine ⟨3601304101358049236545441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19206955207242929261575685 3601304101358049236545441)
                    ·
                      refine ⟨2700978076018536927409081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3601304101358049236545441 2700978076018536927409081)
                      ·
                        rfl

theorem cell23_5260136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_5260136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260136 prefixEnd_5260136 := by exact prefixLift 5260136
  have htrace : WordTrace (prefixWord ++ tailWord_5260136) baseStart_5260136 baseEnd_5260136 := by
    simpa [prefixWord, tailWord_5260136, baseEnd_5260136] using wordTrace_append hprefix tailTrace_5260136
  have hstable : (prefixWord ++ tailWord_5260136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260136).length < 2 ^ (prefixWord ++ tailWord_5260136).sum := by decide
  have hdescent : baseEnd_5260136 < baseStart_5260136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260149 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_5260149 : Nat := 118140960795 + 5260149 * 2 ^ 59
def prefixEnd_5260149 : Nat := 4983230072969 + 3 ^ 40 * 5260149 * 2
def baseEnd_5260149 : Nat := 2700984751267045376546521

theorem tailTrace_5260149 : CollatzResearch.WordTrace tailWord_5260149 prefixEnd_5260149 2700984751267045376546521 := by
  unfold tailWord_5260149
  simp only [CollatzResearch.WordTrace]
  refine ⟨191853395420386009772063501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127902263613590673181375667 191853395420386009772063501)
  ·
    refine ⟨71945023282644753664523813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191853395420386009772063501 71945023282644753664523813)
    ·
      refine ⟨13489691865495891312098215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71945023282644753664523813 13489691865495891312098215)
      ·
        refine ⟨20234537798243836968147323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13489691865495891312098215 20234537798243836968147323)
        ·
          refine ⟨30351806697365755452220985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20234537798243836968147323 30351806697365755452220985)
          ·
            refine ⟨22763855023024316589165739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30351806697365755452220985 22763855023024316589165739)
            ·
              refine ⟨34145782534536474883748609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22763855023024316589165739 34145782534536474883748609)
              ·
                refine ⟨25609336900902356162811457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34145782534536474883748609 25609336900902356162811457)
                ·
                  refine ⟨19207002675676767122108593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25609336900902356162811457 19207002675676767122108593)
                  ·
                    refine ⟨14405252006757575341581445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19207002675676767122108593 14405252006757575341581445)
                    ·
                      refine ⟨2700984751267045376546521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14405252006757575341581445 2700984751267045376546521)
                      ·
                        rfl

theorem cell23_5260149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_5260149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260149 prefixEnd_5260149 := by exact prefixLift 5260149
  have htrace : WordTrace (prefixWord ++ tailWord_5260149) baseStart_5260149 baseEnd_5260149 := by
    simpa [prefixWord, tailWord_5260149, baseEnd_5260149] using wordTrace_append hprefix tailTrace_5260149
  have hstable : (prefixWord ++ tailWord_5260149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260149).length < 2 ^ (prefixWord ++ tailWord_5260149).sum := by decide
  have hdescent : baseEnd_5260149 < baseStart_5260149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260153 : List Nat := [1, 2, 1, 3, 2, 3, 3, 2, 2, 2, 2]
def baseStart_5260153 : Nat := 118140960795 + 5260153 * 2 ^ 59
def prefixEnd_5260153 : Nat := 4983230072969 + 3 ^ 40 * 5260153 * 2
def baseEnd_5260153 : Nat := 2700986805189663360896503

theorem tailTrace_5260153 : CollatzResearch.WordTrace tailWord_5260153 prefixEnd_5260153 2700986805189663360896503 := by
  unfold tailWord_5260153
  simp only [CollatzResearch.WordTrace]
  refine ⟨191853541312371518455209113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127902360874914345636806075 191853541312371518455209113)
  ·
    refine ⟨143890155984278638841406835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191853541312371518455209113 143890155984278638841406835)
    ·
      refine ⟨215835233976417958262110253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143890155984278638841406835 215835233976417958262110253)
      ·
        refine ⟨80938212741156734348291345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215835233976417958262110253 80938212741156734348291345)
        ·
          refine ⟨60703659555867550761218509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80938212741156734348291345 60703659555867550761218509)
          ·
            refine ⟨22763872333450331535456941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60703659555867550761218509 22763872333450331535456941)
            ·
              refine ⟨8536452125043874325796353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22763872333450331535456941 8536452125043874325796353)
              ·
                refine ⟨6402339093782905744347265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8536452125043874325796353 6402339093782905744347265)
                ·
                  refine ⟨4801754320337179308260449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6402339093782905744347265 4801754320337179308260449)
                  ·
                    refine ⟨3601315740252884481195337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4801754320337179308260449 3601315740252884481195337)
                    ·
                      refine ⟨2700986805189663360896503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3601315740252884481195337 2700986805189663360896503)
                      ·
                        rfl

theorem cell23_5260153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 2, 2].length) (baseStart_5260153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260153 prefixEnd_5260153 := by exact prefixLift 5260153
  have htrace : WordTrace (prefixWord ++ tailWord_5260153) baseStart_5260153 baseEnd_5260153 := by
    simpa [prefixWord, tailWord_5260153, baseEnd_5260153] using wordTrace_append hprefix tailTrace_5260153
  have hstable : (prefixWord ++ tailWord_5260153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260153).length < 2 ^ (prefixWord ++ tailWord_5260153).sum := by decide
  have hdescent : baseEnd_5260153 < baseStart_5260153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260159 : List Nat := [1, 1, 2, 2, 1, 1, 6, 4, 5]
def baseStart_5260159 : Nat := 118140960795 + 5260159 * 2 ^ 59
def prefixEnd_5260159 : Nat := 4983230072969 + 3 ^ 40 * 5260159 * 2
def baseEnd_5260159 : Nat := 300109987341510037491275

theorem tailTrace_5260159 : CollatzResearch.WordTrace tailWord_5260159 prefixEnd_5260159 300109987341510037491275 := by
  unfold tailWord_5260159
  simp only [CollatzResearch.WordTrace]
  refine ⟨191853760150349781479927531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127902506766899854319951687 191853760150349781479927531)
  ·
    refine ⟨287780640225524672219891297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191853760150349781479927531 287780640225524672219891297)
    ·
      refine ⟨215835480169143504164918473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287780640225524672219891297 215835480169143504164918473)
      ·
        refine ⟨161876610126857628123688855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215835480169143504164918473 161876610126857628123688855)
        ·
          refine ⟨242814915190286442185533283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161876610126857628123688855 242814915190286442185533283)
          ·
            refine ⟨364222372785429663278299925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242814915190286442185533283 364222372785429663278299925)
            ·
              refine ⟨17072923724317015466170309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 364222372785429663278299925 17072923724317015466170309)
              ·
                refine ⟨3201173198309440399906933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17072923724317015466170309 3201173198309440399906933)
                ·
                  refine ⟨300109987341510037491275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3201173198309440399906933 300109987341510037491275)
                  ·
                    rfl

theorem cell23_5260159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 5].length) (baseStart_5260159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260159 prefixEnd_5260159 := by exact prefixLift 5260159
  have htrace : WordTrace (prefixWord ++ tailWord_5260159) baseStart_5260159 baseEnd_5260159 := by
    simpa [prefixWord, tailWord_5260159, baseEnd_5260159] using wordTrace_append hprefix tailTrace_5260159
  have hstable : (prefixWord ++ tailWord_5260159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260159).length < 2 ^ (prefixWord ++ tailWord_5260159).sum := by decide
  have hdescent : baseEnd_5260159 < baseStart_5260159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260169 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 2, 3, 3]
def baseStart_5260169 : Nat := 118140960795 + 5260169 * 2 ^ 59
def prefixEnd_5260169 : Nat := 4983230072969 + 3 ^ 40 * 5260169 * 2
def baseEnd_5260169 : Nat := 2700995020880135298296429

theorem tailTrace_5260169 : CollatzResearch.WordTrace tailWord_5260169 prefixEnd_5260169 2700995020880135298296429 := by
  unfold tailWord_5260169
  simp only [CollatzResearch.WordTrace]
  refine ⟨191854124880313553187791561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127902749920209035458527707 191854124880313553187791561)
  ·
    refine ⟨143890593660235164890843671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191854124880313553187791561 143890593660235164890843671)
    ·
      refine ⟨215835890490352747336265507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143890593660235164890843671 215835890490352747336265507)
      ·
        refine ⟨323753835735529121004398261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215835890490352747336265507 323753835735529121004398261)
        ·
          refine ⟨30351922100205855094162337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 323753835735529121004398261 30351922100205855094162337)
          ·
            refine ⟨22763941575154391320621753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30351922100205855094162337 22763941575154391320621753)
            ·
              refine ⟨17072956181365793490466315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22763941575154391320621753 17072956181365793490466315)
              ·
                refine ⟨25609434272048690235699473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17072956181365793490466315 25609434272048690235699473)
                ·
                  refine ⟨19207075704036517676774605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25609434272048690235699473 19207075704036517676774605)
                  ·
                    refine ⟨7202653389013694128790477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19207075704036517676774605 7202653389013694128790477)
                    ·
                      refine ⟨2700995020880135298296429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7202653389013694128790477 2700995020880135298296429)
                      ·
                        rfl

theorem cell23_5260169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 3, 3].length) (baseStart_5260169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260169 prefixEnd_5260169 := by exact prefixLift 5260169
  have htrace : WordTrace (prefixWord ++ tailWord_5260169) baseStart_5260169 baseEnd_5260169 := by
    simpa [prefixWord, tailWord_5260169, baseEnd_5260169] using wordTrace_append hprefix tailTrace_5260169
  have hstable : (prefixWord ++ tailWord_5260169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260169).length < 2 ^ (prefixWord ++ tailWord_5260169).sum := by decide
  have hdescent : baseEnd_5260169 < baseStart_5260169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260172 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 1, 7]
def baseStart_5260172 : Nat := 118140960795 + 5260172 * 2 ^ 59
def prefixEnd_5260172 : Nat := 4983230072969 + 3 ^ 40 * 5260172 * 2
def baseEnd_5260172 : Nat := 900332187107366262186305

theorem tailTrace_5260172 : CollatzResearch.WordTrace tailWord_5260172 prefixEnd_5260172 900332187107366262186305 := by
  unfold tailWord_5260172
  simp only [CollatzResearch.WordTrace]
  refine ⟨95927117149651342350075385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127902822866201789800100513 95927117149651342350075385)
  ·
    refine ⟨71945337862238506762556539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95927117149651342350075385 71945337862238506762556539)
    ·
      refine ⟨107918006793357760143834809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71945337862238506762556539 107918006793357760143834809)
      ·
        refine ⟨80938505095018320107876107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107918006793357760143834809 80938505095018320107876107)
        ·
          refine ⟨121407757642527480161814161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80938505095018320107876107 121407757642527480161814161)
          ·
            refine ⟨91055818231895610121360621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121407757642527480161814161 91055818231895610121360621)
            ·
              refine ⟨34145931836960853795510233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91055818231895610121360621 34145931836960853795510233)
              ·
                refine ⟨25609448877720640346632675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34145931836960853795510233 25609448877720640346632675)
                ·
                  refine ⟨38414173316580960519949013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25609448877720640346632675 38414173316580960519949013)
                  ·
                    refine ⟨900332187107366262186305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38414173316580960519949013 900332187107366262186305)
                    ·
                      rfl

theorem cell23_5260172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_5260172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260172 prefixEnd_5260172 := by exact prefixLift 5260172
  have htrace : WordTrace (prefixWord ++ tailWord_5260172) baseStart_5260172 baseEnd_5260172 := by
    simpa [prefixWord, tailWord_5260172, baseEnd_5260172] using wordTrace_append hprefix tailTrace_5260172
  have hstable : (prefixWord ++ tailWord_5260172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260172).length < 2 ^ (prefixWord ++ tailWord_5260172).sum := by decide
  have hdescent : baseEnd_5260172 < baseStart_5260172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260189 : List Nat := [1, 4, 2, 1, 2, 1, 2, 3, 2, 5]
def baseStart_5260189 : Nat := 118140960795 + 5260189 * 2 ^ 59
def prefixEnd_5260189 : Nat := 4983230072969 + 3 ^ 40 * 5260189 * 2
def baseEnd_5260189 : Nat := 900335096831075073348779

theorem tailTrace_5260189 : CollatzResearch.WordTrace tailWord_5260189 prefixEnd_5260189 900335096831075073348779 := by
  unfold tailWord_5260189
  simp only [CollatzResearch.WordTrace]
  refine ⟨191854854340241096603519621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127903236226827397735679747 191854854340241096603519621)
  ·
    refine ⟨35972785188795205613159929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191854854340241096603519621 35972785188795205613159929)
    ·
      refine ⟨26979588891596404209869947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35972785188795205613159929 26979588891596404209869947)
      ·
        refine ⟨40469383337394606314804921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26979588891596404209869947 40469383337394606314804921)
        ·
          refine ⟨30352037503045954736103691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40469383337394606314804921 30352037503045954736103691)
          ·
            refine ⟨45528056254568932104155537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30352037503045954736103691 45528056254568932104155537)
            ·
              refine ⟨34146042190926699078116653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45528056254568932104155537 34146042190926699078116653)
              ·
                refine ⟨12804765821597512154293745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34146042190926699078116653 12804765821597512154293745)
                ·
                  refine ⟨9603574366198134115720309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12804765821597512154293745 9603574366198134115720309)
                  ·
                    refine ⟨900335096831075073348779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9603574366198134115720309 900335096831075073348779)
                    ·
                      rfl

theorem cell23_5260189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_5260189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260189 prefixEnd_5260189 := by exact prefixLift 5260189
  have htrace : WordTrace (prefixWord ++ tailWord_5260189) baseStart_5260189 baseEnd_5260189 := by
    simpa [prefixWord, tailWord_5260189, baseEnd_5260189] using wordTrace_append hprefix tailTrace_5260189
  have hstable : (prefixWord ++ tailWord_5260189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260189).length < 2 ^ (prefixWord ++ tailWord_5260189).sum := by decide
  have hdescent : baseEnd_5260189 < baseStart_5260189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260193 : List Nat := [1, 2, 3, 4, 1, 3, 1, 3, 5]
def baseStart_5260193 : Nat := 118140960795 + 5260193 * 2 ^ 59
def prefixEnd_5260193 : Nat := 4983230072969 + 3 ^ 40 * 5260193 * 2
def baseEnd_5260193 : Nat := 300111927157315911599591

theorem tailTrace_5260193 : CollatzResearch.WordTrace tailWord_5260193 prefixEnd_5260193 300111927157315911599591 := by
  unfold tailWord_5260193
  simp only [CollatzResearch.WordTrace]
  refine ⟨191855000232226605286665233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127903333488151070191110155 191855000232226605286665233)
  ·
    refine ⟨143891250174169953964998925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191855000232226605286665233 143891250174169953964998925)
    ·
      refine ⟨53959218815313732736874597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143891250174169953964998925 53959218815313732736874597)
      ·
        refine ⟨10117353527871324888163987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53959218815313732736874597 10117353527871324888163987)
        ·
          refine ⟨15176030291806987332245981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10117353527871324888163987 15176030291806987332245981)
          ·
            refine ⟨5691011359427620249592243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15176030291806987332245981 5691011359427620249592243)
            ·
              refine ⟨8536517039141430374388365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5691011359427620249592243 8536517039141430374388365)
              ·
                refine ⟨3201193889678036390395637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8536517039141430374388365 3201193889678036390395637)
                ·
                  refine ⟨300111927157315911599591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3201193889678036390395637 300111927157315911599591)
                  ·
                    rfl

theorem cell23_5260193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 5].length) (baseStart_5260193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260193 prefixEnd_5260193 := by exact prefixLift 5260193
  have htrace : WordTrace (prefixWord ++ tailWord_5260193) baseStart_5260193 baseEnd_5260193 := by
    simpa [prefixWord, tailWord_5260193, baseEnd_5260193] using wordTrace_append hprefix tailTrace_5260193
  have hstable : (prefixWord ++ tailWord_5260193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260193).length < 2 ^ (prefixWord ++ tailWord_5260193).sum := by decide
  have hdescent : baseEnd_5260193 < baseStart_5260193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260266 : List Nat := [3, 1, 3, 1, 2, 3, 2, 2, 6]
def baseStart_5260266 : Nat := 118140960795 + 5260266 * 2 ^ 59
def prefixEnd_5260266 : Nat := 4983230072969 + 3 ^ 40 * 5260266 * 2
def baseEnd_5260266 : Nat := 300116092055957935420387

theorem tailTrace_5260266 : CollatzResearch.WordTrace tailWord_5260266 prefixEnd_5260266 300116092055957935420387 := by
  unfold tailWord_5260266
  simp only [CollatzResearch.WordTrace]
  refine ⟨47964415690240534688518163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127905108507308092502715101 47964415690240534688518163)
  ·
    refine ⟨71946623535360802032777245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47964415690240534688518163 71946623535360802032777245)
    ·
      refine ⟨26979983825760300762291467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71946623535360802032777245 26979983825760300762291467)
      ·
        refine ⟨40469975738640451143437201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26979983825760300762291467 40469975738640451143437201)
        ·
          refine ⟨30352481803980338357577901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40469975738640451143437201 30352481803980338357577901)
          ·
            refine ⟨11382180676492626884091713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30352481803980338357577901 11382180676492626884091713)
            ·
              refine ⟨8536635507369470163068785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11382180676492626884091713 8536635507369470163068785)
              ·
                refine ⟨6402476630527102622301589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8536635507369470163068785 6402476630527102622301589)
                ·
                  refine ⟨300116092055957935420387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6402476630527102622301589 300116092055957935420387)
                  ·
                    rfl

theorem cell23_5260266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 6].length) (baseStart_5260266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260266 prefixEnd_5260266 := by exact prefixLift 5260266
  have htrace : WordTrace (prefixWord ++ tailWord_5260266) baseStart_5260266 baseEnd_5260266 := by
    simpa [prefixWord, tailWord_5260266, baseEnd_5260266] using wordTrace_append hprefix tailTrace_5260266
  have hstable : (prefixWord ++ tailWord_5260266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260266).length < 2 ^ (prefixWord ++ tailWord_5260266).sum := by decide
  have hdescent : baseEnd_5260266 < baseStart_5260266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260270 : List Nat := [4, 1, 2, 1, 4, 1, 1, 4, 1, 4]
def baseStart_5260270 : Nat := 118140960795 + 5260270 * 2 ^ 59
def prefixEnd_5260270 : Nat := 4983230072969 + 3 ^ 40 * 5260270 * 2
def baseEnd_5260270 : Nat := 900348960808746467711155

theorem tailTrace_5260270 : CollatzResearch.WordTrace tailWord_5260270 prefixEnd_5260270 900348960808746467711155 := by
  unfold tailWord_5260270
  simp only [CollatzResearch.WordTrace]
  refine ⟨23982226081618455929652283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127905205768631764958145509 23982226081618455929652283)
  ·
    refine ⟨35973339122427683894478425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23982226081618455929652283 35973339122427683894478425)
    ·
      refine ⟨26980004341820762920858819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35973339122427683894478425 26980004341820762920858819)
      ·
        refine ⟨40470006512731144381288229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26980004341820762920858819 40470006512731144381288229)
        ·
          refine ⟨7588126221137089571491543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40470006512731144381288229 7588126221137089571491543)
          ·
            refine ⟨11382189331705634357237315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7588126221137089571491543 11382189331705634357237315)
            ·
              refine ⟨17073283997558451535855973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11382189331705634357237315 17073283997558451535855973)
              ·
                refine ⟨3201240749542209662972995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17073283997558451535855973 3201240749542209662972995)
                ·
                  refine ⟨4801861124313314494459493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3201240749542209662972995 4801861124313314494459493)
                  ·
                    refine ⟨900348960808746467711155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4801861124313314494459493 900348960808746467711155)
                    ·
                      rfl

theorem cell23_5260270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_5260270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260270 prefixEnd_5260270 := by exact prefixLift 5260270
  have htrace : WordTrace (prefixWord ++ tailWord_5260270) baseStart_5260270 baseEnd_5260270 := by
    simpa [prefixWord, tailWord_5260270, baseEnd_5260270] using wordTrace_append hprefix tailTrace_5260270
  have hstable : (prefixWord ++ tailWord_5260270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260270).length < 2 ^ (prefixWord ++ tailWord_5260270).sum := by decide
  have hdescent : baseEnd_5260270 < baseStart_5260270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260327 : List Nat := [1, 1, 7, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_5260327 : Nat := 118140960795 + 5260327 * 2 ^ 59
def prefixEnd_5260327 : Nat := 4983230072969 + 3 ^ 40 * 5260327 * 2
def baseEnd_5260327 : Nat := 2701076150823545680120703

theorem tailTrace_5260327 : CollatzResearch.WordTrace tailWord_5260327 prefixEnd_5260327 2701076150823545680120703 := by
  unfold tailWord_5260327
  simp only [CollatzResearch.WordTrace]
  refine ⟨191859887613741146172043235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127906591742494097448028823 191859887613741146172043235)
  ·
    refine ⟨287789831420611719258064853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191859887613741146172043235 287789831420611719258064853)
    ·
      refine ⟨6745074173920587170110895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 287789831420611719258064853 6745074173920587170110895)
      ·
        refine ⟨10117611260880880755166343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6745074173920587170110895 10117611260880880755166343)
        ·
          refine ⟨15176416891321321132749515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10117611260880880755166343 15176416891321321132749515)
          ·
            refine ⟨22764625336981981699124273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15176416891321321132749515 22764625336981981699124273)
            ·
              refine ⟨17073469002736486274343205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22764625336981981699124273 17073469002736486274343205)
              ·
                refine ⟨3201275438013091176439351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17073469002736486274343205 3201275438013091176439351)
                ·
                  refine ⟨4801913157019636764659027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3201275438013091176439351 4801913157019636764659027)
                  ·
                    refine ⟨7202869735529455146988541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4801913157019636764659027 7202869735529455146988541)
                    ·
                      refine ⟨2701076150823545680120703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7202869735529455146988541 2701076150823545680120703)
                      ·
                        rfl

theorem cell23_5260327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_5260327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260327 prefixEnd_5260327 := by exact prefixLift 5260327
  have htrace : WordTrace (prefixWord ++ tailWord_5260327) baseStart_5260327 baseEnd_5260327 := by
    simpa [prefixWord, tailWord_5260327, baseEnd_5260327] using wordTrace_append hprefix tailTrace_5260327
  have hstable : (prefixWord ++ tailWord_5260327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260327).length < 2 ^ (prefixWord ++ tailWord_5260327).sum := by decide
  have hdescent : baseEnd_5260327 < baseStart_5260327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260346 : List Nat := [3, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4]
def baseStart_5260346 : Nat := 118140960795 + 5260346 * 2 ^ 59
def prefixEnd_5260346 : Nat := 4983230072969 + 3 ^ 40 * 5260346 * 2
def baseEnd_5260346 : Nat := 2701085906955981105783115

theorem tailTrace_5260346 : CollatzResearch.WordTrace tailWord_5260346 prefixEnd_5260346 2701085906955981105783115 := by
  unfold tailWord_5260346
  simp only [CollatzResearch.WordTrace]
  refine ⟨47965145150168078104246223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127907053733781541611323261 47965145150168078104246223)
  ·
    refine ⟨71947717725252117156369335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47965145150168078104246223 71947717725252117156369335)
    ·
      refine ⟨107921576587878175734554003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71947717725252117156369335 107921576587878175734554003)
      ·
        refine ⟨161882364881817263601831005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107921576587878175734554003 161882364881817263601831005)
        ·
          refine ⟨60705886830681473850686627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161882364881817263601831005 60705886830681473850686627)
          ·
            refine ⟨91058830246022210776029941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60705886830681473850686627 91058830246022210776029941)
            ·
              refine ⟨8536765335564582260252807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91058830246022210776029941 8536765335564582260252807)
              ·
                refine ⟨12805148003346873390379211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8536765335564582260252807 12805148003346873390379211)
                ·
                  refine ⟨19207722005020310085568817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12805148003346873390379211 19207722005020310085568817)
                  ·
                    refine ⟨14405791503765232564176613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19207722005020310085568817 14405791503765232564176613)
                    ·
                      refine ⟨2701085906955981105783115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14405791503765232564176613 2701085906955981105783115)
                      ·
                        rfl

theorem cell23_5260346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4].length) (baseStart_5260346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260346 prefixEnd_5260346 := by exact prefixLift 5260346
  have htrace : WordTrace (prefixWord ++ tailWord_5260346) baseStart_5260346 baseEnd_5260346 := by
    simpa [prefixWord, tailWord_5260346, baseEnd_5260346] using wordTrace_append hprefix tailTrace_5260346
  have hstable : (prefixWord ++ tailWord_5260346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260346).length < 2 ^ (prefixWord ++ tailWord_5260346).sum := by decide
  have hdescent : baseEnd_5260346 < baseStart_5260346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260350 : List Nat := [4, 2, 1, 3, 1, 2, 2, 2, 1, 1, 4]
def baseStart_5260350 : Nat := 118140960795 + 5260350 * 2 ^ 59
def prefixEnd_5260350 : Nat := 4983230072969 + 3 ^ 40 * 5260350 * 2
def baseEnd_5260350 : Nat := 2701087960878599090133097

theorem tailTrace_5260350 : CollatzResearch.WordTrace tailWord_5260350 prefixEnd_5260350 2701087960878599090133097 := by
  unfold tailWord_5260350
  simp only [CollatzResearch.WordTrace]
  refine ⟨23982590811582227637516313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127907150995105214066753669 23982590811582227637516313)
  ·
    refine ⟨17986943108686670728137235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23982590811582227637516313 17986943108686670728137235)
    ·
      refine ⟨26980414663030006092205853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17986943108686670728137235 26980414663030006092205853)
      ·
        refine ⟨10117655498636252284577195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26980414663030006092205853 10117655498636252284577195)
        ·
          refine ⟨15176483247954378426865793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10117655498636252284577195 15176483247954378426865793)
          ·
            refine ⟨11382362435965783820149345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15176483247954378426865793 11382362435965783820149345)
            ·
              refine ⟨8536771826974337865112009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11382362435965783820149345 8536771826974337865112009)
              ·
                refine ⟨6402578870230753398834007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8536771826974337865112009 6402578870230753398834007)
                ·
                  refine ⟨9603868305346130098251011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6402578870230753398834007 9603868305346130098251011)
                  ·
                    refine ⟨14405802458019195147376517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9603868305346130098251011 14405802458019195147376517)
                    ·
                      refine ⟨2701087960878599090133097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14405802458019195147376517 2701087960878599090133097)
                      ·
                        rfl

theorem cell23_5260350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_5260350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260350 prefixEnd_5260350 := by exact prefixLift 5260350
  have htrace : WordTrace (prefixWord ++ tailWord_5260350) baseStart_5260350 baseEnd_5260350 := by
    simpa [prefixWord, tailWord_5260350, baseEnd_5260350] using wordTrace_append hprefix tailTrace_5260350
  have hstable : (prefixWord ++ tailWord_5260350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260350).length < 2 ^ (prefixWord ++ tailWord_5260350).sum := by decide
  have hdescent : baseEnd_5260350 < baseStart_5260350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260366 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3]
def baseStart_5260366 : Nat := 118140960795 + 5260366 * 2 ^ 59
def prefixEnd_5260366 : Nat := 4983230072969 + 3 ^ 40 * 5260366 * 2
def baseEnd_5260366 : Nat := 2701096176569071027533023

theorem tailTrace_5260366 : CollatzResearch.WordTrace tailWord_5260366 prefixEnd_5260366 2701096176569071027533023 := by
  unfold tailWord_5260366
  simp only [CollatzResearch.WordTrace]
  refine ⟨23982663757574981979089119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127907540040399903888475301 23982663757574981979089119)
  ·
    refine ⟨35973995636362472968633679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23982663757574981979089119 35973995636362472968633679)
    ·
      refine ⟨53960993454543709452950519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35973995636362472968633679 53960993454543709452950519)
      ·
        refine ⟨80941490181815564179425779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53960993454543709452950519 80941490181815564179425779)
        ·
          refine ⟨121412235272723346269138669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80941490181815564179425779 121412235272723346269138669)
          ·
            refine ⟨45529588227271254850927001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121412235272723346269138669 45529588227271254850927001)
            ·
              refine ⟨34147191170453441138195251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45529588227271254850927001 34147191170453441138195251)
              ·
                refine ⟨51220786755680161707292877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34147191170453441138195251 51220786755680161707292877)
                ·
                  refine ⟨19207795033380060640234829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51220786755680161707292877 19207795033380060640234829)
                  ·
                    refine ⟨7202923137517522740088061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19207795033380060640234829 7202923137517522740088061)
                    ·
                      refine ⟨2701096176569071027533023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7202923137517522740088061 2701096176569071027533023)
                      ·
                        rfl

theorem cell23_5260366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_5260366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260366 prefixEnd_5260366 := by exact prefixLift 5260366
  have htrace : WordTrace (prefixWord ++ tailWord_5260366) baseStart_5260366 baseEnd_5260366 := by
    simpa [prefixWord, tailWord_5260366, baseEnd_5260366] using wordTrace_append hprefix tailTrace_5260366
  have hstable : (prefixWord ++ tailWord_5260366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260366).length < 2 ^ (prefixWord ++ tailWord_5260366).sum := by decide
  have hdescent : baseEnd_5260366 < baseStart_5260366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260383 : List Nat := [1, 1, 2, 3, 1, 1, 4, 4, 2, 1, 3]
def baseStart_5260383 : Nat := 118140960795 + 5260383 * 2 ^ 59
def prefixEnd_5260383 : Nat := 4983230072969 + 3 ^ 40 * 5260383 * 2
def baseEnd_5260383 : Nat := 2701104905740197461020445

theorem tailTrace_5260383 : CollatzResearch.WordTrace tailWord_5260383 prefixEnd_5260383 2701104905740197461020445 := by
  unfold tailWord_5260383
  simp only [CollatzResearch.WordTrace]
  refine ⟨191861930101538267736081803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127907953401025511824054535 191861930101538267736081803)
  ·
    refine ⟨287792895152307401604122705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191861930101538267736081803 287792895152307401604122705)
    ·
      refine ⟨215844671364230551203092029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287792895152307401604122705 215844671364230551203092029)
      ·
        refine ⟨80941751761586456701159511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215844671364230551203092029 80941751761586456701159511)
        ·
          refine ⟨121412627642379685051739267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80941751761586456701159511 121412627642379685051739267)
          ·
            refine ⟨182118941463569527577608901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121412627642379685051739267 182118941463569527577608901)
            ·
              refine ⟨34147301524419286420801669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 182118941463569527577608901 34147301524419286420801669)
              ·
                refine ⟨6402619035828616203900313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34147301524419286420801669 6402619035828616203900313)
                ·
                  refine ⟨4801964276871462152925235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6402619035828616203900313 4801964276871462152925235)
                  ·
                    refine ⟨7202946415307193229387853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4801964276871462152925235 7202946415307193229387853)
                    ·
                      refine ⟨2701104905740197461020445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7202946415307193229387853 2701104905740197461020445)
                      ·
                        rfl

theorem cell23_5260383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_5260383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260383 prefixEnd_5260383 := by exact prefixLift 5260383
  have htrace : WordTrace (prefixWord ++ tailWord_5260383) baseStart_5260383 baseEnd_5260383 := by
    simpa [prefixWord, tailWord_5260383, baseEnd_5260383] using wordTrace_append hprefix tailTrace_5260383
  have hstable : (prefixWord ++ tailWord_5260383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260383).length < 2 ^ (prefixWord ++ tailWord_5260383).sum := by decide
  have hdescent : baseEnd_5260383 < baseStart_5260383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260399 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 1, 8]
def baseStart_5260399 : Nat := 118140960795 + 5260399 * 2 ^ 59
def prefixEnd_5260399 : Nat := 4983230072969 + 3 ^ 40 * 5260399 * 2
def baseEnd_5260399 : Nat := 900371040476889799473457

theorem tailTrace_5260399 : CollatzResearch.WordTrace tailWord_5260399 prefixEnd_5260399 900371040476889799473457 := by
  unfold tailWord_5260399
  simp only [CollatzResearch.WordTrace]
  refine ⟨191862513669480302468664251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127908342446320201645776167 191862513669480302468664251)
  ·
    refine ⟨287793770504220453702996377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191862513669480302468664251 287793770504220453702996377)
    ·
      refine ⟨215845327878165340277247283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287793770504220453702996377 215845327878165340277247283)
      ·
        refine ⟨323767991817248010415870925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215845327878165340277247283 323767991817248010415870925)
        ·
          refine ⟨121412996931468003905951597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 323767991817248010415870925 121412996931468003905951597)
          ·
            refine ⟨45529873849300501464731849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121412996931468003905951597 45529873849300501464731849)
            ·
              refine ⟨34147405386975376098548887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45529873849300501464731849 34147405386975376098548887)
              ·
                refine ⟨51221108080463064147823331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34147405386975376098548887 51221108080463064147823331)
                ·
                  refine ⟨76831662120694596221734997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51221108080463064147823331 76831662120694596221734997)
                  ·
                    refine ⟨900371040476889799473457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76831662120694596221734997 900371040476889799473457)
                    ·
                      rfl

theorem cell23_5260399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 8].length) (baseStart_5260399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260399 prefixEnd_5260399 := by exact prefixLift 5260399
  have htrace : WordTrace (prefixWord ++ tailWord_5260399) baseStart_5260399 baseEnd_5260399 := by
    simpa [prefixWord, tailWord_5260399, baseEnd_5260399] using wordTrace_append hprefix tailTrace_5260399
  have hstable : (prefixWord ++ tailWord_5260399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260399).length < 2 ^ (prefixWord ++ tailWord_5260399).sum := by decide
  have hdescent : baseEnd_5260399 < baseStart_5260399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260426 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 2, 1, 5]
def baseStart_5260426 : Nat := 118140960795 + 5260426 * 2 ^ 59
def prefixEnd_5260426 : Nat := 4983230072969 + 3 ^ 40 * 5260426 * 2
def baseEnd_5260426 : Nat := 2701126985408340792782747

theorem tailTrace_5260426 : CollatzResearch.WordTrace tailWord_5260426 prefixEnd_5260426 2701126985408340792782747 := by
  unfold tailWord_5260426
  simp only [CollatzResearch.WordTrace]
  refine ⟨47965874610095621519974283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127908998960254990719931421 47965874610095621519974283)
  ·
    refine ⟨71948811915143432279961425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47965874610095621519974283 71948811915143432279961425)
    ·
      refine ⟨53961608936357574209971069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71948811915143432279961425 53961608936357574209971069)
      ·
        refine ⟨20235603351134090328739151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53961608936357574209971069 20235603351134090328739151)
        ·
          refine ⟨30353405026701135493108727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20235603351134090328739151 30353405026701135493108727)
          ·
            refine ⟨45530107540051703239663091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30353405026701135493108727 45530107540051703239663091)
            ·
              refine ⟨68295161310077554859494637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45530107540051703239663091 68295161310077554859494637)
              ·
                refine ⟨25610685491279083072310489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68295161310077554859494637 25610685491279083072310489)
                ·
                  refine ⟨19208014118459312304232867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25610685491279083072310489 19208014118459312304232867)
                  ·
                    refine ⟨28812021177688968456349301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19208014118459312304232867 28812021177688968456349301)
                    ·
                      refine ⟨2701126985408340792782747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28812021177688968456349301 2701126985408340792782747)
                      ·
                        rfl

theorem cell23_5260426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_5260426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260426 prefixEnd_5260426 := by exact prefixLift 5260426
  have htrace : WordTrace (prefixWord ++ tailWord_5260426) baseStart_5260426 baseEnd_5260426 := by
    simpa [prefixWord, tailWord_5260426, baseEnd_5260426] using wordTrace_append hprefix tailTrace_5260426
  have hstable : (prefixWord ++ tailWord_5260426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260426).length < 2 ^ (prefixWord ++ tailWord_5260426).sum := by decide
  have hdescent : baseEnd_5260426 < baseStart_5260426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260480 : List Nat := [2, 1, 1, 2, 6, 1, 2, 3, 5]
def baseStart_5260480 : Nat := 118140960795 + 5260480 * 2 ^ 59
def prefixEnd_5260480 : Nat := 4983230072969 + 3 ^ 40 * 5260480 * 2
def baseEnd_5260480 : Nat := 300128301484853731278611

theorem tailTrace_5260480 : CollatzResearch.WordTrace tailWord_5260480 prefixEnd_5260480 300128301484853731278611 := by
  unfold tailWord_5260480
  simp only [CollatzResearch.WordTrace]
  refine ⟨95932733991093426651181447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127910311988124568868241929 95932733991093426651181447)
  ·
    refine ⟨143899100986640139976772171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95932733991093426651181447 143899100986640139976772171)
    ·
      refine ⟨215848651479960209965158257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143899100986640139976772171 215848651479960209965158257)
      ·
        refine ⟨161886488609970157473868693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215848651479960209965158257 161886488609970157473868693)
        ·
          refine ⟨7588429153592351131587595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 161886488609970157473868693 7588429153592351131587595)
          ·
            refine ⟨11382643730388526697381393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7588429153592351131587595 11382643730388526697381393)
            ·
              refine ⟨8536982797791395023036045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11382643730388526697381393 8536982797791395023036045)
              ·
                refine ⟨3201368549171773133638517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8536982797791395023036045 3201368549171773133638517)
                ·
                  refine ⟨300128301484853731278611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3201368549171773133638517 300128301484853731278611)
                  ·
                    rfl

theorem cell23_5260480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 5].length) (baseStart_5260480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260480 prefixEnd_5260480 := by exact prefixLift 5260480
  have htrace : WordTrace (prefixWord ++ tailWord_5260480) baseStart_5260480 baseEnd_5260480 := by
    simpa [prefixWord, tailWord_5260480, baseEnd_5260480] using wordTrace_append hprefix tailTrace_5260480
  have hstable : (prefixWord ++ tailWord_5260480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260480).length < 2 ^ (prefixWord ++ tailWord_5260480).sum := by decide
  have hdescent : baseEnd_5260480 < baseStart_5260480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260523 : List Nat := [1, 1, 1, 1, 2, 6, 2, 2, 3, 4]
def baseStart_5260523 : Nat := 118140960795 + 5260523 * 2 ^ 59
def prefixEnd_5260523 : Nat := 4983230072969 + 3 ^ 40 * 5260523 * 2
def baseEnd_5260523 : Nat := 900392264343942304423267

theorem tailTrace_5260523 : CollatzResearch.WordTrace tailWord_5260523 prefixEnd_5260523 900392264343942304423267 := by
  unfold tailWord_5260523
  simp only [CollatzResearch.WordTrace]
  refine ⟨191867036321031071646178223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127911357547354047764118815 191867036321031071646178223)
  ·
    refine ⟨287800554481546607469267335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191867036321031071646178223 287800554481546607469267335)
    ·
      refine ⟨431700831722319911203901003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287800554481546607469267335 431700831722319911203901003)
      ·
        refine ⟨647551247583479866805851505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431700831722319911203901003 647551247583479866805851505)
        ·
          refine ⟨485663435687609900104388629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 647551247583479866805851505 485663435687609900104388629)
          ·
            refine ⟨22765473547856714067393217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 485663435687609900104388629 22765473547856714067393217)
            ·
              refine ⟨17074105160892535550544913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22765473547856714067393217 17074105160892535550544913)
              ·
                refine ⟨12805578870669401662908685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17074105160892535550544913 12805578870669401662908685)
                ·
                  refine ⟨4802092076501025623590757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12805578870669401662908685 4802092076501025623590757)
                  ·
                    refine ⟨900392264343942304423267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4802092076501025623590757 900392264343942304423267)
                    ·
                      rfl

theorem cell23_5260523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 4].length) (baseStart_5260523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260523 prefixEnd_5260523 := by exact prefixLift 5260523
  have htrace : WordTrace (prefixWord ++ tailWord_5260523) baseStart_5260523 baseEnd_5260523 := by
    simpa [prefixWord, tailWord_5260523, baseEnd_5260523] using wordTrace_append hprefix tailTrace_5260523
  have hstable : (prefixWord ++ tailWord_5260523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260523).length < 2 ^ (prefixWord ++ tailWord_5260523).sum := by decide
  have hdescent : baseEnd_5260523 < baseStart_5260523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260570 : List Nat := [3, 1, 1, 3, 3, 1, 4, 1, 6]
def baseStart_5260570 : Nat := 118140960795 + 5260570 * 2 ^ 59
def prefixEnd_5260570 : Nat := 4983230072969 + 3 ^ 40 * 5260570 * 2
def baseEnd_5260570 : Nat := 300133436291398692153565

theorem tailTrace_5260570 : CollatzResearch.WordTrace tailWord_5260570 prefixEnd_5260570 300133436291398692153565 := by
  unfold tailWord_5260570
  simp only [CollatzResearch.WordTrace]
  refine ⟨47967187637965199668284791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127912500367907199115426109 47967187637965199668284791)
  ·
    refine ⟨71950781456947799502427187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47967187637965199668284791 71950781456947799502427187)
    ·
      refine ⟨107926172185421699253640781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71950781456947799502427187 107926172185421699253640781)
      ·
        refine ⟨40472314569533137220115293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107926172185421699253640781 40472314569533137220115293)
        ·
          refine ⟨15177117963574926457543235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40472314569533137220115293 15177117963574926457543235)
          ·
            refine ⟨22765676945362389686314853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15177117963574926457543235 22765676945362389686314853)
            ·
              refine ⟨4268564427255448066184035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22765676945362389686314853 4268564427255448066184035)
              ·
                refine ⟨6402846640883172099276053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4268564427255448066184035 6402846640883172099276053)
                ·
                  refine ⟨300133436291398692153565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6402846640883172099276053 300133436291398692153565)
                  ·
                    rfl

theorem cell23_5260570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 6].length) (baseStart_5260570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260570 prefixEnd_5260570 := by exact prefixLift 5260570
  have htrace : WordTrace (prefixWord ++ tailWord_5260570) baseStart_5260570 baseEnd_5260570 := by
    simpa [prefixWord, tailWord_5260570, baseEnd_5260570] using wordTrace_append hprefix tailTrace_5260570
  have hstable : (prefixWord ++ tailWord_5260570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260570).length < 2 ^ (prefixWord ++ tailWord_5260570).sum := by decide
  have hdescent : baseEnd_5260570 < baseStart_5260570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260580 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 5, 1, 3]
def baseStart_5260580 : Nat := 118140960795 + 5260580 * 2 ^ 59
def prefixEnd_5260580 : Nat := 4983230072969 + 3 ^ 40 * 5260580 * 2
def baseEnd_5260580 : Nat := 2701206061429133190257039

theorem tailTrace_5260580 : CollatzResearch.WordTrace tailWord_5260580 prefixEnd_5260580 2701206061429133190257039 := by
  unfold tailWord_5260580
  simp only [CollatzResearch.WordTrace]
  refine ⟨95934557640912285190501597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127912743521216380254002129 95934557640912285190501597)
  ·
    refine ⟨35975459115342106946438099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95934557640912285190501597 35975459115342106946438099)
    ·
      refine ⟨53963188673013160419657149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35975459115342106946438099 53963188673013160419657149)
      ·
        refine ⟨20236195752379935157371431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53963188673013160419657149 20236195752379935157371431)
        ·
          refine ⟨30354293628569902736057147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20236195752379935157371431 30354293628569902736057147)
          ·
            refine ⟨45531440442854854104085721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30354293628569902736057147 45531440442854854104085721)
            ·
              refine ⟨34148580332141140578064291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45531440442854854104085721 34148580332141140578064291)
              ·
                refine ⟨51222870498211710867096437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34148580332141140578064291 51222870498211710867096437)
                ·
                  refine ⟨4802144109207347893790291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51222870498211710867096437 4802144109207347893790291)
                  ·
                    refine ⟨7203216163811021840685437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4802144109207347893790291 7203216163811021840685437)
                    ·
                      refine ⟨2701206061429133190257039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7203216163811021840685437 2701206061429133190257039)
                      ·
                        rfl

theorem cell23_5260580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_5260580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260580 prefixEnd_5260580 := by exact prefixLift 5260580
  have htrace : WordTrace (prefixWord ++ tailWord_5260580) baseStart_5260580 baseEnd_5260580 := by
    simpa [prefixWord, tailWord_5260580, baseEnd_5260580] using wordTrace_append hprefix tailTrace_5260580
  have hstable : (prefixWord ++ tailWord_5260580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260580).length < 2 ^ (prefixWord ++ tailWord_5260580).sum := by decide
  have hdescent : baseEnd_5260580 < baseStart_5260580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260603 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 6, 6, 2]
def baseStart_5260603 : Nat := 118140960795 + 5260603 * 2 ^ 59
def prefixEnd_5260603 : Nat := 4983230072969 + 3 ^ 40 * 5260603 * 2
def baseEnd_5260603 : Nat := 2701217871484186600269433

theorem tailTrace_5260603 : CollatzResearch.WordTrace tailWord_5260603 prefixEnd_5260603 2701217871484186600269433 := by
  unfold tailWord_5260603
  simp only [CollatzResearch.WordTrace]
  refine ⟨191869954160741245309090463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127913302773827496872726975 191869954160741245309090463)
  ·
    refine ⟨287804931241111867963635695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191869954160741245309090463 287804931241111867963635695)
    ·
      refine ⟨431707396861667801945453543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287804931241111867963635695 431707396861667801945453543)
      ·
        refine ⟨647561095292501702918180315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431707396861667801945453543 647561095292501702918180315)
        ·
          refine ⟨971341642938752554377270473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647561095292501702918180315 971341642938752554377270473)
          ·
            refine ⟨728506232204064415782952855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 971341642938752554377270473 728506232204064415782952855)
            ·
              refine ⟨1092759348306096623674429283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 728506232204064415782952855 1092759348306096623674429283)
              ·
                refine ⟨1639139022459144935511643925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1092759348306096623674429283 1639139022459144935511643925)
                ·
                  refine ⟨76834641677772418852108309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1639139022459144935511643925 76834641677772418852108309)
                  ·
                    refine ⟨3601623828645582133692577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76834641677772418852108309 3601623828645582133692577)
                    ·
                      refine ⟨2701217871484186600269433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3601623828645582133692577 2701217871484186600269433)
                      ·
                        rfl

theorem cell23_5260603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 6, 2].length) (baseStart_5260603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260603 prefixEnd_5260603 := by exact prefixLift 5260603
  have htrace : WordTrace (prefixWord ++ tailWord_5260603) baseStart_5260603 baseEnd_5260603 := by
    simpa [prefixWord, tailWord_5260603, baseEnd_5260603] using wordTrace_append hprefix tailTrace_5260603
  have hstable : (prefixWord ++ tailWord_5260603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260603).length < 2 ^ (prefixWord ++ tailWord_5260603).sum := by decide
  have hdescent : baseEnd_5260603 < baseStart_5260603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260613 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 4, 4]
def baseStart_5260613 : Nat := 118140960795 + 5260613 * 2 ^ 59
def prefixEnd_5260613 : Nat := 4983230072969 + 3 ^ 40 * 5260613 * 2
def baseEnd_5260613 : Nat := 900407668763577187048129

theorem tailTrace_5260613 : CollatzResearch.WordTrace tailWord_5260613 prefixEnd_5260613 900407668763577187048129 := by
  unfold tailWord_5260613
  simp only [CollatzResearch.WordTrace]
  refine ⟨191870318890705017016954493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127913545927136678011302995 191870318890705017016954493)
  ·
    refine ⟨71951369584014381381357935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191870318890705017016954493 71951369584014381381357935)
    ·
      refine ⟨107927054376021572072036903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71951369584014381381357935 107927054376021572072036903)
      ·
        refine ⟨161890581564032358108055355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107927054376021572072036903 161890581564032358108055355)
        ·
          refine ⟨242835872346048537162083033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161890581564032358108055355 242835872346048537162083033)
          ·
            refine ⟨182126904259536402871562275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242835872346048537162083033 182126904259536402871562275)
            ·
              refine ⟨273190356389304604307343413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182126904259536402871562275 273190356389304604307343413)
              ·
                refine ⟨25611595911497306653813445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 273190356389304604307343413 25611595911497306653813445)
                ·
                  refine ⟨4802174233405744997590021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25611595911497306653813445 4802174233405744997590021)
                  ·
                    refine ⟨900407668763577187048129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4802174233405744997590021 900407668763577187048129)
                    ·
                      rfl

theorem cell23_5260613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 4].length) (baseStart_5260613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260613 prefixEnd_5260613 := by exact prefixLift 5260613
  have htrace : WordTrace (prefixWord ++ tailWord_5260613) baseStart_5260613 baseEnd_5260613 := by
    simpa [prefixWord, tailWord_5260613, baseEnd_5260613] using wordTrace_append hprefix tailTrace_5260613
  have hstable : (prefixWord ++ tailWord_5260613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260613).length < 2 ^ (prefixWord ++ tailWord_5260613).sum := by decide
  have hdescent : baseEnd_5260613 < baseStart_5260613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260633 : List Nat := [1, 2, 1, 2, 2, 2, 3, 3, 1, 2, 4]
def baseStart_5260633 : Nat := 118140960795 + 5260633 * 2 ^ 59
def prefixEnd_5260633 : Nat := 4983230072969 + 3 ^ 40 * 5260633 * 2
def baseEnd_5260633 : Nat := 2701233275903821482894295

theorem tailTrace_5260633 : CollatzResearch.WordTrace tailWord_5260633 prefixEnd_5260633 2701233275903821482894295 := by
  unfold tailWord_5260633
  simp only [CollatzResearch.WordTrace]
  refine ⟨191871048350632560432682553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127914032233755040288455035 191871048350632560432682553)
  ·
    refine ⟨143903286262974420324511915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191871048350632560432682553 143903286262974420324511915)
    ·
      refine ⟨215854929394461630486767873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143903286262974420324511915 215854929394461630486767873)
      ·
        refine ⟨161891197045846222865075905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215854929394461630486767873 161891197045846222865075905)
        ·
          refine ⟨121418397784384667148806929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161891197045846222865075905 121418397784384667148806929)
          ·
            refine ⟨91063798338288500361605197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121418397784384667148806929 91063798338288500361605197)
            ·
              refine ⟨34148924376858187635601949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91063798338288500361605197 34148924376858187635601949)
              ·
                refine ⟨12805846641321820363350731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34148924376858187635601949 12805846641321820363350731)
                ·
                  refine ⟨19208769961982730545026097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12805846641321820363350731 19208769961982730545026097)
                  ·
                    refine ⟨14406577471487047908769573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19208769961982730545026097 14406577471487047908769573)
                    ·
                      refine ⟨2701233275903821482894295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14406577471487047908769573 2701233275903821482894295)
                      ·
                        rfl

theorem cell23_5260633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_5260633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260633 prefixEnd_5260633 := by exact prefixLift 5260633
  have htrace : WordTrace (prefixWord ++ tailWord_5260633) baseStart_5260633 baseEnd_5260633 := by
    simpa [prefixWord, tailWord_5260633, baseEnd_5260633] using wordTrace_append hprefix tailTrace_5260633
  have hstable : (prefixWord ++ tailWord_5260633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260633).length < 2 ^ (prefixWord ++ tailWord_5260633).sum := by decide
  have hdescent : baseEnd_5260633 < baseStart_5260633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260640 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 3]
def baseStart_5260640 : Nat := 118140960795 + 5260640 * 2 ^ 59
def prefixEnd_5260640 : Nat := 4983230072969 + 3 ^ 40 * 5260640 * 2
def baseEnd_5260640 : Nat := 2701236870268402955506763

theorem tailTrace_5260640 : CollatzResearch.WordTrace tailWord_5260640 prefixEnd_5260640 2701236870268402955506763 := by
  unfold tailWord_5260640
  simp only [CollatzResearch.WordTrace]
  refine ⟨95935651830803600314093687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127914202441071467085458249 95935651830803600314093687)
  ·
    refine ⟨143903477746205400471140531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95935651830803600314093687 143903477746205400471140531)
    ·
      refine ⟨215855216619308100706710797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143903477746205400471140531 215855216619308100706710797)
      ·
        refine ⟨80945706232240537765016549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215855216619308100706710797 80945706232240537765016549)
        ·
          refine ⟨15177319918545100830940603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80945706232240537765016549 15177319918545100830940603)
          ·
            refine ⟨22765979877817651246410905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15177319918545100830940603 22765979877817651246410905)
            ·
              refine ⟨17074484908363238434808179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22765979877817651246410905 17074484908363238434808179)
              ·
                refine ⟨25611727362544857652212269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17074484908363238434808179 25611727362544857652212269)
                ·
                  refine ⟨9604397760954321619579601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25611727362544857652212269 9604397760954321619579601)
                  ·
                    refine ⟨7203298320715741214684701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9604397760954321619579601 7203298320715741214684701)
                    ·
                      refine ⟨2701236870268402955506763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7203298320715741214684701 2701236870268402955506763)
                      ·
                        rfl

theorem cell23_5260640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_5260640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260640 prefixEnd_5260640 := by exact prefixLift 5260640
  have htrace : WordTrace (prefixWord ++ tailWord_5260640) baseStart_5260640 baseEnd_5260640 := by
    simpa [prefixWord, tailWord_5260640, baseEnd_5260640] using wordTrace_append hprefix tailTrace_5260640
  have hstable : (prefixWord ++ tailWord_5260640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260640).length < 2 ^ (prefixWord ++ tailWord_5260640).sum := by decide
  have hdescent : baseEnd_5260640 < baseStart_5260640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260654 : List Nat := [4, 1, 2, 4, 1, 1, 1, 3, 1, 1, 4]
def baseStart_5260654 : Nat := 118140960795 + 5260654 * 2 ^ 59
def prefixEnd_5260654 : Nat := 4983230072969 + 3 ^ 40 * 5260654 * 2
def baseEnd_5260654 : Nat := 2701244058997565900731699

theorem tailTrace_5260654 : CollatzResearch.WordTrace tailWord_5260654 prefixEnd_5260654 2701244058997565900731699 := by
  unfold tailWord_5260654
  simp only [CollatzResearch.WordTrace]
  refine ⟨23983976785444560127399627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127914542855704320679464677 23983976785444560127399627)
  ·
    refine ⟨35975965178166840191099441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23983976785444560127399627 35975965178166840191099441)
    ·
      refine ⟨26981973883625130143324581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35975965178166840191099441 26981973883625130143324581)
      ·
        refine ⟨5059120103179711901873359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26981973883625130143324581 5059120103179711901873359)
        ·
          refine ⟨7588680154769567852810039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5059120103179711901873359 7588680154769567852810039)
          ·
            refine ⟨11383020232154351779215059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7588680154769567852810039 11383020232154351779215059)
            ·
              refine ⟨17074530348231527668822589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11383020232154351779215059 17074530348231527668822589)
              ·
                refine ⟨6402948880586822875808471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17074530348231527668822589 6402948880586822875808471)
                ·
                  refine ⟨9604423320880234313712707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6402948880586822875808471 9604423320880234313712707)
                  ·
                    refine ⟨14406634981320351470569061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9604423320880234313712707 14406634981320351470569061)
                    ·
                      refine ⟨2701244058997565900731699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14406634981320351470569061 2701244058997565900731699)
                      ·
                        rfl

theorem cell23_5260654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_5260654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260654 prefixEnd_5260654 := by exact prefixLift 5260654
  have htrace : WordTrace (prefixWord ++ tailWord_5260654) baseStart_5260654 baseEnd_5260654 := by
    simpa [prefixWord, tailWord_5260654, baseEnd_5260654] using wordTrace_append hprefix tailTrace_5260654
  have hstable : (prefixWord ++ tailWord_5260654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260654).length < 2 ^ (prefixWord ++ tailWord_5260654).sum := by decide
  have hdescent : baseEnd_5260654 < baseStart_5260654 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260657 : List Nat := [1, 2, 2, 2, 1, 2, 6, 1, 1, 2, 3]
def baseStart_5260657 : Nat := 118140960795 + 5260657 * 2 ^ 59
def prefixEnd_5260657 : Nat := 4983230072969 + 3 ^ 40 * 5260657 * 2
def baseEnd_5260657 : Nat := 2701245599439529388994185

theorem tailTrace_5260657 : CollatzResearch.WordTrace tailWord_5260657 prefixEnd_5260657 2701245599439529388994185 := by
  unfold tailWord_5260657
  simp only [CollatzResearch.WordTrace]
  refine ⟨191871923702545612531556225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127914615801697075021037483 191871923702545612531556225)
  ·
    refine ⟨143903942776909209398667169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191871923702545612531556225 143903942776909209398667169)
    ·
      refine ⟨107927957082681907049000377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143903942776909209398667169 107927957082681907049000377)
      ·
        refine ⟨80945967812011430286750283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107927957082681907049000377 80945967812011430286750283)
        ·
          refine ⟨121418951718017145430125425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80945967812011430286750283 121418951718017145430125425)
          ·
            refine ⟨91064213788512859072594069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121418951718017145430125425 91064213788512859072594069)
            ·
              refine ⟨4268635021336540269027847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91064213788512859072594069 4268635021336540269027847)
              ·
                refine ⟨6402952532004810403541771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4268635021336540269027847 6402952532004810403541771)
                ·
                  refine ⟨9604428798007215605312657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6402952532004810403541771 9604428798007215605312657)
                  ·
                    refine ⟨7203321598505411703984493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9604428798007215605312657 7203321598505411703984493)
                    ·
                      refine ⟨2701245599439529388994185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7203321598505411703984493 2701245599439529388994185)
                      ·
                        rfl

theorem cell23_5260657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 1, 2, 3].length) (baseStart_5260657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260657 prefixEnd_5260657 := by exact prefixLift 5260657
  have htrace : WordTrace (prefixWord ++ tailWord_5260657) baseStart_5260657 baseEnd_5260657 := by
    simpa [prefixWord, tailWord_5260657, baseEnd_5260657] using wordTrace_append hprefix tailTrace_5260657
  have hstable : (prefixWord ++ tailWord_5260657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260657).length < 2 ^ (prefixWord ++ tailWord_5260657).sum := by decide
  have hdescent : baseEnd_5260657 < baseStart_5260657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260693 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 2, 3, 4]
def baseStart_5260693 : Nat := 118140960795 + 5260693 * 2 ^ 59
def prefixEnd_5260693 : Nat := 4983230072969 + 3 ^ 40 * 5260693 * 2
def baseEnd_5260693 : Nat := 2701264084743091248144019

theorem tailTrace_5260693 : CollatzResearch.WordTrace tailWord_5260693 prefixEnd_5260693 2701264084743091248144019 := by
  unfold tailWord_5260693
  simp only [CollatzResearch.WordTrace]
  refine ⟨191873236730415190679866733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127915491153610127119911155 191873236730415190679866733)
  ·
    refine ⟨71952463773905696504950025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191873236730415190679866733 71952463773905696504950025)
    ·
      refine ⟨53964347830429272378712519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71952463773905696504950025 53964347830429272378712519)
      ·
        refine ⟨80946521745643908568068779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53964347830429272378712519 80946521745643908568068779)
        ·
          refine ⟨121419782618465862852103169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80946521745643908568068779 121419782618465862852103169)
          ·
            refine ⟨91064836963849397139077377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121419782618465862852103169 91064836963849397139077377)
            ·
              refine ⟨68298627722887047854308033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91064836963849397139077377 68298627722887047854308033)
              ·
                refine ⟨51223970792165285890731025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68298627722887047854308033 51223970792165285890731025)
                ·
                  refine ⟨38417978094123964418048269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51223970792165285890731025 38417978094123964418048269)
                  ·
                    refine ⟨14406741785296486656768101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38417978094123964418048269 14406741785296486656768101)
                    ·
                      refine ⟨2701264084743091248144019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14406741785296486656768101 2701264084743091248144019)
                      ·
                        rfl

theorem cell23_5260693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_5260693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260693 prefixEnd_5260693 := by exact prefixLift 5260693
  have htrace : WordTrace (prefixWord ++ tailWord_5260693) baseStart_5260693 baseEnd_5260693 := by
    simpa [prefixWord, tailWord_5260693, baseEnd_5260693] using wordTrace_append hprefix tailTrace_5260693
  have hstable : (prefixWord ++ tailWord_5260693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260693).length < 2 ^ (prefixWord ++ tailWord_5260693).sum := by decide
  have hdescent : baseEnd_5260693 < baseStart_5260693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260697 : List Nat := [1, 2, 1, 2, 1, 5, 1, 4, 1, 3, 2]
def baseStart_5260697 : Nat := 118140960795 + 5260697 * 2 ^ 59
def prefixEnd_5260697 : Nat := 4983230072969 + 3 ^ 40 * 5260697 * 2
def baseEnd_5260697 : Nat := 2701266138665709232494001

theorem tailTrace_5260697 : CollatzResearch.WordTrace tailWord_5260697 prefixEnd_5260697 2701266138665709232494001 := by
  unfold tailWord_5260697
  simp only [CollatzResearch.WordTrace]
  refine ⟨191873382622400699363012345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127915588414933799575341563 191873382622400699363012345)
  ·
    refine ⟨143905036966800524522259259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191873382622400699363012345 143905036966800524522259259)
    ·
      refine ⟨215857555450200786783388889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143905036966800524522259259 215857555450200786783388889)
      ·
        refine ⟨161893166587650590087541667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215857555450200786783388889 161893166587650590087541667)
        ·
          refine ⟨242839749881475885131312501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161893166587650590087541667 242839749881475885131312501)
          ·
            refine ⟨22766226551388364231060547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 242839749881475885131312501 22766226551388364231060547)
            ·
              refine ⟨34149339827082546346590821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22766226551388364231060547 34149339827082546346590821)
              ·
                refine ⟨6403001217577977439985779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34149339827082546346590821 6403001217577977439985779)
                ·
                  refine ⟨9604501826366966159978669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6403001217577977439985779 9604501826366966159978669)
                  ·
                    refine ⟨3601688184887612309992001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9604501826366966159978669 3601688184887612309992001)
                    ·
                      refine ⟨2701266138665709232494001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3601688184887612309992001 2701266138665709232494001)
                      ·
                        rfl

theorem cell23_5260697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 3, 2].length) (baseStart_5260697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260697 prefixEnd_5260697 := by exact prefixLift 5260697
  have htrace : WordTrace (prefixWord ++ tailWord_5260697) baseStart_5260697 baseEnd_5260697 := by
    simpa [prefixWord, tailWord_5260697, baseEnd_5260697] using wordTrace_append hprefix tailTrace_5260697
  have hstable : (prefixWord ++ tailWord_5260697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260697).length < 2 ^ (prefixWord ++ tailWord_5260697).sum := by decide
  have hdescent : baseEnd_5260697 < baseStart_5260697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260713 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 3, 6, 3]
def baseStart_5260713 : Nat := 118140960795 + 5260713 * 2 ^ 59
def prefixEnd_5260713 : Nat := 4983230072969 + 3 ^ 40 * 5260713 * 2
def baseEnd_5260713 : Nat := 2701274354356181169893927

theorem tailTrace_5260713 : CollatzResearch.WordTrace tailWord_5260713 prefixEnd_5260713 2701274354356181169893927 := by
  unfold tailWord_5260713
  simp only [CollatzResearch.WordTrace]
  refine ⟨191873966190342734095594793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127915977460228489397063195 191873966190342734095594793)
  ·
    refine ⟨143905474642757050571696095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191873966190342734095594793 143905474642757050571696095)
    ·
      refine ⟨215858211964135575857544143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143905474642757050571696095 215858211964135575857544143)
      ·
        refine ⟨323787317946203363786316215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215858211964135575857544143 323787317946203363786316215)
        ·
          refine ⟨485680976919305045679474323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323787317946203363786316215 485680976919305045679474323)
          ·
            refine ⟨728521465378957568519211485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485680976919305045679474323 728521465378957568519211485)
            ·
              refine ⟨273195549517109088194704307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 728521465378957568519211485 273195549517109088194704307)
              ·
                refine ⟨409793324275663632292056461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273195549517109088194704307 409793324275663632292056461)
                ·
                  refine ⟨153672496603373862109521173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 409793324275663632292056461 153672496603373862109521173)
                  ·
                    refine ⟨7203398278283149786383805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 153672496603373862109521173 7203398278283149786383805)
                    ·
                      refine ⟨2701274354356181169893927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7203398278283149786383805 2701274354356181169893927)
                      ·
                        rfl

theorem cell23_5260713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 6, 3].length) (baseStart_5260713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260713 prefixEnd_5260713 := by exact prefixLift 5260713
  have htrace : WordTrace (prefixWord ++ tailWord_5260713) baseStart_5260713 baseEnd_5260713 := by
    simpa [prefixWord, tailWord_5260713, baseEnd_5260713] using wordTrace_append hprefix tailTrace_5260713
  have hstable : (prefixWord ++ tailWord_5260713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260713).length < 2 ^ (prefixWord ++ tailWord_5260713).sum := by decide
  have hdescent : baseEnd_5260713 < baseStart_5260713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260723 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 4]
def baseStart_5260723 : Nat := 118140960795 + 5260723 * 2 ^ 59
def prefixEnd_5260723 : Nat := 4983230072969 + 3 ^ 40 * 5260723 * 2
def baseEnd_5260723 : Nat := 2701279489162726130768881

theorem tailTrace_5260723 : CollatzResearch.WordTrace tailWord_5260723 prefixEnd_5260723 2701279489162726130768881 := by
  unfold tailWord_5260723
  simp only [CollatzResearch.WordTrace]
  refine ⟨191874330920306505803458823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127916220613537670535639215 191874330920306505803458823)
  ·
    refine ⟨287811496380459758705188235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191874330920306505803458823 287811496380459758705188235)
    ·
      refine ⟨431717244570689638057782353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287811496380459758705188235 431717244570689638057782353)
      ·
        refine ⟨323787933428017228543336765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 431717244570689638057782353 323787933428017228543336765)
        ·
          refine ⟨121420475035506460703751287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 323787933428017228543336765 121420475035506460703751287)
          ·
            refine ⟨182130712553259691055626931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121420475035506460703751287 182130712553259691055626931)
            ·
              refine ⟨273196068829889536583440397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182130712553259691055626931 273196068829889536583440397)
              ·
                refine ⟨102448525811208576218790149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 273196068829889536583440397 102448525811208576218790149)
                ·
                  refine ⟨19209098589601608041023153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102448525811208576218790149 19209098589601608041023153)
                  ·
                    refine ⟨14406823942201206030767365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19209098589601608041023153 14406823942201206030767365)
                    ·
                      refine ⟨2701279489162726130768881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14406823942201206030767365 2701279489162726130768881)
                      ·
                        rfl

theorem cell23_5260723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 4].length) (baseStart_5260723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260723 prefixEnd_5260723 := by exact prefixLift 5260723
  have htrace : WordTrace (prefixWord ++ tailWord_5260723) baseStart_5260723 baseEnd_5260723 := by
    simpa [prefixWord, tailWord_5260723, baseEnd_5260723] using wordTrace_append hprefix tailTrace_5260723
  have hstable : (prefixWord ++ tailWord_5260723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260723).length < 2 ^ (prefixWord ++ tailWord_5260723).sum := by decide
  have hdescent : baseEnd_5260723 < baseStart_5260723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260727 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 4, 2, 2]
def baseStart_5260727 : Nat := 118140960795 + 5260727 * 2 ^ 59
def prefixEnd_5260727 : Nat := 4983230072969 + 3 ^ 40 * 5260727 * 2
def baseEnd_5260727 : Nat := 2701281543085344115118863

theorem tailTrace_5260727 : CollatzResearch.WordTrace tailWord_5260727 prefixEnd_5260727 2701281543085344115118863 := by
  unfold tailWord_5260727
  simp only [CollatzResearch.WordTrace]
  refine ⟨191874476812292014486604435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127916317874861342991069623 191874476812292014486604435)
  ·
    refine ⟨287811715218438021729906653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191874476812292014486604435 287811715218438021729906653)
    ·
      refine ⟨107929393206914258148714995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287811715218438021729906653 107929393206914258148714995)
      ·
        refine ⟨161894089810371387223072493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107929393206914258148714995 161894089810371387223072493)
        ·
          refine ⟨60710283678889270208652185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161894089810371387223072493 60710283678889270208652185)
          ·
            refine ⟨45532712759166952656489139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60710283678889270208652185 45532712759166952656489139)
            ·
              refine ⟨68299069138750428984733709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45532712759166952656489139 68299069138750428984733709)
              ·
                refine ⟨25612150927031410869275141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68299069138750428984733709 25612150927031410869275141)
                ·
                  refine ⟨4802278298818389537989089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25612150927031410869275141 4802278298818389537989089)
                  ·
                    refine ⟨3601708724113792153491817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4802278298818389537989089 3601708724113792153491817)
                    ·
                      refine ⟨2701281543085344115118863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3601708724113792153491817 2701281543085344115118863)
                      ·
                        rfl

theorem cell23_5260727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 2, 2].length) (baseStart_5260727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260727 prefixEnd_5260727 := by exact prefixLift 5260727
  have htrace : WordTrace (prefixWord ++ tailWord_5260727) baseStart_5260727 baseEnd_5260727 := by
    simpa [prefixWord, tailWord_5260727, baseEnd_5260727] using wordTrace_append hprefix tailTrace_5260727
  have hstable : (prefixWord ++ tailWord_5260727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260727).length < 2 ^ (prefixWord ++ tailWord_5260727).sum := by decide
  have hdescent : baseEnd_5260727 < baseStart_5260727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260744 : List Nat := [2, 1, 3, 1, 3, 1, 3, 3, 2, 2, 2]
def baseStart_5260744 : Nat := 118140960795 + 5260744 * 2 ^ 59
def prefixEnd_5260744 : Nat := 4983230072969 + 3 ^ 40 * 5260744 * 2
def baseEnd_5260744 : Nat := 2701290272256470548606285

theorem tailTrace_5260744 : CollatzResearch.WordTrace tailWord_5260744 prefixEnd_5260744 2701290272256470548606285 := by
  unfold tailWord_5260744
  simp only [CollatzResearch.WordTrace]
  refine ⟨95937548426615213194986643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127916731235486950926648857 95937548426615213194986643)
  ·
    refine ⟨143906322639922819792479965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95937548426615213194986643 143906322639922819792479965)
    ·
      refine ⟨53964870989971057422179987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143906322639922819792479965 53964870989971057422179987)
      ·
        refine ⟨80947306484956586133269981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53964870989971057422179987 80947306484956586133269981)
        ·
          refine ⟨30355239931858719799976243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80947306484956586133269981 30355239931858719799976243)
          ·
            refine ⟨45532859897788079699964365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30355239931858719799976243 45532859897788079699964365)
            ·
              refine ⟨17074822461670529887486637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45532859897788079699964365 17074822461670529887486637)
              ·
                refine ⟨6403058423126448707807489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17074822461670529887486637 6403058423126448707807489)
                ·
                  refine ⟨4802293817344836530855617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6403058423126448707807489 4802293817344836530855617)
                  ·
                    refine ⟨3601720363008627398141713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4802293817344836530855617 3601720363008627398141713)
                    ·
                      refine ⟨2701290272256470548606285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3601720363008627398141713 2701290272256470548606285)
                      ·
                        rfl

theorem cell23_5260744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 2, 2, 2].length) (baseStart_5260744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260744 prefixEnd_5260744 := by exact prefixLift 5260744
  have htrace : WordTrace (prefixWord ++ tailWord_5260744) baseStart_5260744 baseEnd_5260744 := by
    simpa [prefixWord, tailWord_5260744, baseEnd_5260744] using wordTrace_append hprefix tailTrace_5260744
  have hstable : (prefixWord ++ tailWord_5260744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260744).length < 2 ^ (prefixWord ++ tailWord_5260744).sum := by decide
  have hdescent : baseEnd_5260744 < baseStart_5260744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260784 : List Nat := [2, 1, 1, 1, 3, 6, 2, 2, 5]
def baseStart_5260784 : Nat := 118140960795 + 5260784 * 2 ^ 59
def prefixEnd_5260784 : Nat := 4983230072969 + 3 ^ 40 * 5260784 * 2
def baseEnd_5260784 : Nat := 300145645720294488011789

theorem tailTrace_5260784 : CollatzResearch.WordTrace tailWord_5260784 prefixEnd_5260784 300145645720294488011789 := by
  unfold tailWord_5260784
  simp only [CollatzResearch.WordTrace]
  refine ⟨95938277886542756610714703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127917703848723675480952937 95938277886542756610714703)
  ·
    refine ⟨143907416829814134916072055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95938277886542756610714703 143907416829814134916072055)
    ·
      refine ⟨215861125244721202374108083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143907416829814134916072055 215861125244721202374108083)
      ·
        refine ⟨323791687867081803561162125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215861125244721202374108083 323791687867081803561162125)
        ·
          refine ⟨121421882950155676335435797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 323791687867081803561162125 121421882950155676335435797)
          ·
            refine ⟨5691650763288547328223553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 121421882950155676335435797 5691650763288547328223553)
            ·
              refine ⟨4268738072466410496167665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5691650763288547328223553 4268738072466410496167665)
              ·
                refine ⟨3201553554349807872125749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4268738072466410496167665 3201553554349807872125749)
                ·
                  refine ⟨300145645720294488011789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3201553554349807872125749 300145645720294488011789)
                  ·
                    rfl

theorem cell23_5260784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 5].length) (baseStart_5260784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260784 prefixEnd_5260784 := by exact prefixLift 5260784
  have htrace : WordTrace (prefixWord ++ tailWord_5260784) baseStart_5260784 baseEnd_5260784 := by
    simpa [prefixWord, tailWord_5260784, baseEnd_5260784] using wordTrace_append hprefix tailTrace_5260784
  have hstable : (prefixWord ++ tailWord_5260784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260784).length < 2 ^ (prefixWord ++ tailWord_5260784).sum := by decide
  have hdescent : baseEnd_5260784 < baseStart_5260784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260793 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 2, 8]
def baseStart_5260793 : Nat := 118140960795 + 5260793 * 2 ^ 59
def prefixEnd_5260793 : Nat := 4983230072969 + 3 ^ 40 * 5260793 * 2
def baseEnd_5260793 : Nat := 900438477602846952297853

theorem tailTrace_5260793 : CollatzResearch.WordTrace tailWord_5260793 prefixEnd_5260793 900438477602846952297853 := by
  unfold tailWord_5260793
  simp only [CollatzResearch.WordTrace]
  refine ⟨191876884030052907758507033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127917922686701938505671355 191876884030052907758507033)
  ·
    refine ⟨143907663022539680818880275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191876884030052907758507033 143907663022539680818880275)
    ·
      refine ⟨215861494533809521228320413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143907663022539680818880275 215861494533809521228320413)
      ·
        refine ⟨80948060450178570460620155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215861494533809521228320413 80948060450178570460620155)
        ·
          refine ⟨121422090675267855690930233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80948060450178570460620155 121422090675267855690930233)
          ·
            refine ⟨91066568006450891768197675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121422090675267855690930233 91066568006450891768197675)
            ·
              refine ⟨136599852009676337652296513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91066568006450891768197675 136599852009676337652296513)
              ·
                refine ⟨102449889007257253239222385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136599852009676337652296513 102449889007257253239222385)
                ·
                  refine ⟨76837416755442939929416789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102449889007257253239222385 76837416755442939929416789)
                  ·
                    refine ⟨900438477602846952297853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76837416755442939929416789 900438477602846952297853)
                    ·
                      rfl

theorem cell23_5260793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 8].length) (baseStart_5260793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260793 prefixEnd_5260793 := by exact prefixLift 5260793
  have htrace : WordTrace (prefixWord ++ tailWord_5260793) baseStart_5260793 baseEnd_5260793 := by
    simpa [prefixWord, tailWord_5260793, baseEnd_5260793] using wordTrace_append hprefix tailTrace_5260793
  have hstable : (prefixWord ++ tailWord_5260793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260793).length < 2 ^ (prefixWord ++ tailWord_5260793).sum := by decide
  have hdescent : baseEnd_5260793 < baseStart_5260793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260814 : List Nat := [4, 1, 1, 2, 4, 2, 1, 1, 2, 5]
def baseStart_5260814 : Nat := 118140960795 + 5260814 * 2 ^ 59
def prefixEnd_5260814 : Nat := 4983230072969 + 3 ^ 40 * 5260814 * 2
def baseEnd_5260814 : Nat := 900442071967428424910321

theorem tailTrace_5260814 : CollatzResearch.WordTrace tailWord_5260814 prefixEnd_5260814 900442071967428424910321 := by
  unfold tailWord_5260814
  simp only [CollatzResearch.WordTrace]
  refine ⟨23984706245372103543127687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127918433308651218896680997 23984706245372103543127687)
  ·
    refine ⟨35977059368058155314691531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23984706245372103543127687 35977059368058155314691531)
    ·
      refine ⟨53965589052087232972037297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35977059368058155314691531 53965589052087232972037297)
      ·
        refine ⟨40474191789065424729027973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53965589052087232972037297 40474191789065424729027973)
        ·
          refine ⟨7588910960449767136692745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40474191789065424729027973 7588910960449767136692745)
          ·
            refine ⟨5691683220337325352519559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7588910960449767136692745 5691683220337325352519559)
            ·
              refine ⟨8537524830505988028779339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5691683220337325352519559 8537524830505988028779339)
              ·
                refine ⟨12806287245758982043169009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8537524830505988028779339 12806287245758982043169009)
                ·
                  refine ⟨9604715434319236532376757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12806287245758982043169009 9604715434319236532376757)
                  ·
                    refine ⟨900442071967428424910321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9604715434319236532376757 900442071967428424910321)
                    ·
                      rfl

theorem cell23_5260814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_5260814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260814 prefixEnd_5260814 := by exact prefixLift 5260814
  have htrace : WordTrace (prefixWord ++ tailWord_5260814) baseStart_5260814 baseEnd_5260814 := by
    simpa [prefixWord, tailWord_5260814, baseEnd_5260814] using wordTrace_append hprefix tailTrace_5260814
  have hstable : (prefixWord ++ tailWord_5260814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260814).length < 2 ^ (prefixWord ++ tailWord_5260814).sum := by decide
  have hdescent : baseEnd_5260814 < baseStart_5260814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260887 : List Nat := [1, 1, 3, 2, 2, 3, 2, 3, 1, 5]
def baseStart_5260887 : Nat := 118140960795 + 5260887 * 2 ^ 59
def prefixEnd_5260887 : Nat := 4983230072969 + 3 ^ 40 * 5260887 * 2
def baseEnd_5260887 : Nat := 900454566663354496372709

theorem tailTrace_5260887 : CollatzResearch.WordTrace tailWord_5260887 prefixEnd_5260887 900454566663354496372709 := by
  unfold tailWord_5260887
  simp only [CollatzResearch.WordTrace]
  refine ⟨191880312491712361812428915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127920208327808241208285943 191880312491712361812428915)
  ·
    refine ⟨287820468737568542718643373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191880312491712361812428915 287820468737568542718643373)
    ·
      refine ⟨107932675776588203519491265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287820468737568542718643373 107932675776588203519491265)
      ·
        refine ⟨80949506832441152639618449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107932675776588203519491265 80949506832441152639618449)
        ·
          refine ⟨60712130124330864479713837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80949506832441152639618449 60712130124330864479713837)
          ·
            refine ⟨22767048796624074179892689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60712130124330864479713837 22767048796624074179892689)
            ·
              refine ⟨17075286597468055634919517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22767048796624074179892689 17075286597468055634919517)
              ·
                refine ⟨6403232474050520863094819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17075286597468055634919517 6403232474050520863094819)
                ·
                  refine ⟨9604848711075781294642229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6403232474050520863094819 9604848711075781294642229)
                  ·
                    refine ⟨900454566663354496372709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9604848711075781294642229 900454566663354496372709)
                    ·
                      rfl

theorem cell23_5260887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 5].length) (baseStart_5260887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260887 prefixEnd_5260887 := by exact prefixLift 5260887
  have htrace : WordTrace (prefixWord ++ tailWord_5260887) baseStart_5260887 baseEnd_5260887 := by
    simpa [prefixWord, tailWord_5260887, baseEnd_5260887] using wordTrace_append hprefix tailTrace_5260887
  have hstable : (prefixWord ++ tailWord_5260887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260887).length < 2 ^ (prefixWord ++ tailWord_5260887).sum := by decide
  have hdescent : baseEnd_5260887 < baseStart_5260887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260901 : List Nat := [1, 3, 1, 3, 3, 3, 1, 1, 3, 1, 3]
def baseStart_5260901 : Nat := 118140960795 + 5260901 * 2 ^ 59
def prefixEnd_5260901 : Nat := 4983230072969 + 3 ^ 40 * 5260901 * 2
def baseEnd_5260901 : Nat := 2701370888719226434343063

theorem tailTrace_5260901 : CollatzResearch.WordTrace tailWord_5260901 prefixEnd_5260901 2701370888719226434343063 := by
  unfold tailWord_5260901
  simp only [CollatzResearch.WordTrace]
  refine ⟨191880823113661642203438557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127920548742441094802292371 191880823113661642203438557)
  ·
    refine ⟨71955308667623115826289459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191880823113661642203438557 71955308667623115826289459)
    ·
      refine ⟨107932963001434673739434189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71955308667623115826289459 107932963001434673739434189)
      ·
        refine ⟨40474861125538002652287821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107932963001434673739434189 40474861125538002652287821)
        ·
          refine ⟨15178072922076750994607933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40474861125538002652287821 15178072922076750994607933)
          ·
            refine ⟨5691777345778781622977975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15178072922076750994607933 5691777345778781622977975)
            ·
              refine ⟨8537666018668172434466963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5691777345778781622977975 8537666018668172434466963)
              ·
                refine ⟨12806499028002258651700445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8537666018668172434466963 12806499028002258651700445)
                ·
                  refine ⟨4802437135500846994387667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12806499028002258651700445 4802437135500846994387667)
                  ·
                    refine ⟨7203655703251270491581501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4802437135500846994387667 7203655703251270491581501)
                    ·
                      refine ⟨2701370888719226434343063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7203655703251270491581501 2701370888719226434343063)
                      ·
                        rfl

theorem cell23_5260901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_5260901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260901 prefixEnd_5260901 := by exact prefixLift 5260901
  have htrace : WordTrace (prefixWord ++ tailWord_5260901) baseStart_5260901 baseEnd_5260901 := by
    simpa [prefixWord, tailWord_5260901, baseEnd_5260901] using wordTrace_append hprefix tailTrace_5260901
  have hstable : (prefixWord ++ tailWord_5260901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260901).length < 2 ^ (prefixWord ++ tailWord_5260901).sum := by decide
  have hdescent : baseEnd_5260901 < baseStart_5260901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260924 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 5, 2, 2]
def baseStart_5260924 : Nat := 118140960795 + 5260924 * 2 ^ 59
def prefixEnd_5260924 : Nat := 4983230072969 + 3 ^ 40 * 5260924 * 2
def baseEnd_5260924 : Nat := 2701382698774279844355457

theorem tailTrace_5260924 : CollatzResearch.WordTrace tailWord_5260924 prefixEnd_5260924 2701382698774279844355457 := by
  unfold tailWord_5260924
  simp only [CollatzResearch.WordTrace]
  refine ⟨95940830996289158565762913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127921107995052211421017217 95940830996289158565762913)
  ·
    refine ⟨71955623247216868924322185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95940830996289158565762913 71955623247216868924322185)
    ·
      refine ⟨53966717435412651693241639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71955623247216868924322185 53966717435412651693241639)
      ·
        refine ⟨80950076153118977539862459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53966717435412651693241639 80950076153118977539862459)
        ·
          refine ⟨121425114229678466309793689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80950076153118977539862459 121425114229678466309793689)
          ·
            refine ⟨91068835672258849732345267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121425114229678466309793689 91068835672258849732345267)
            ·
              refine ⟨136603253508388274598517901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91068835672258849732345267 136603253508388274598517901)
              ·
                refine ⟨51226220065645602974444213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136603253508388274598517901 51226220065645602974444213)
                ·
                  refine ⟨4802458131154275278854145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51226220065645602974444213 4802458131154275278854145)
                  ·
                    refine ⟨3601843598365706459140609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4802458131154275278854145 3601843598365706459140609)
                    ·
                      refine ⟨2701382698774279844355457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3601843598365706459140609 2701382698774279844355457)
                      ·
                        rfl

theorem cell23_5260924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 5, 2, 2].length) (baseStart_5260924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260924 prefixEnd_5260924 := by exact prefixLift 5260924
  have htrace : WordTrace (prefixWord ++ tailWord_5260924) baseStart_5260924 baseEnd_5260924 := by
    simpa [prefixWord, tailWord_5260924, baseEnd_5260924] using wordTrace_append hprefix tailTrace_5260924
  have hstable : (prefixWord ++ tailWord_5260924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260924).length < 2 ^ (prefixWord ++ tailWord_5260924).sum := by decide
  have hdescent : baseEnd_5260924 < baseStart_5260924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260957 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 5, 3, 3]
def baseStart_5260957 : Nat := 118140960795 + 5260957 * 2 ^ 59
def prefixEnd_5260957 : Nat := 4983230072969 + 3 ^ 40 * 5260957 * 2
def baseEnd_5260957 : Nat := 2701399643635878215242805

theorem tailTrace_5260957 : CollatzResearch.WordTrace tailWord_5260957 prefixEnd_5260957 2701399643635878215242805 := by
  unfold tailWord_5260957
  simp only [CollatzResearch.WordTrace]
  refine ⟨191882865601458763767477125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127921910400972509178318083 191882865601458763767477125)
  ·
    refine ⟨35978037300273518206401961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191882865601458763767477125 35978037300273518206401961)
    ·
      refine ⟨26983527975205138654801471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35978037300273518206401961 26983527975205138654801471)
      ·
        refine ⟨40475291962807707982202207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26983527975205138654801471 40475291962807707982202207)
        ·
          refine ⟨60712937944211561973303311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40475291962807707982202207 60712937944211561973303311)
          ·
            refine ⟨91069406916317342959954967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60712937944211561973303311 91069406916317342959954967)
            ·
              refine ⟨136604110374476014439932451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91069406916317342959954967 136604110374476014439932451)
              ·
                refine ⟨204906165561714021659898677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136604110374476014439932451 204906165561714021659898677)
                ·
                  refine ⟨19209953021410689530615501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 204906165561714021659898677 19209953021410689530615501)
                  ·
                    refine ⟨7203732383029008573980813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19209953021410689530615501 7203732383029008573980813)
                    ·
                      refine ⟨2701399643635878215242805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7203732383029008573980813 2701399643635878215242805)
                      ·
                        rfl

theorem cell23_5260957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_5260957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260957 prefixEnd_5260957 := by exact prefixLift 5260957
  have htrace : WordTrace (prefixWord ++ tailWord_5260957) baseStart_5260957 baseEnd_5260957 := by
    simpa [prefixWord, tailWord_5260957, baseEnd_5260957] using wordTrace_append hprefix tailTrace_5260957
  have hstable : (prefixWord ++ tailWord_5260957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260957).length < 2 ^ (prefixWord ++ tailWord_5260957).sum := by decide
  have hdescent : baseEnd_5260957 < baseStart_5260957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5260968 : List Nat := [2, 1, 7, 1, 1, 1, 2, 1, 1, 6]
def baseStart_5260968 : Nat := 118140960795 + 5260968 * 2 ^ 59
def prefixEnd_5260968 : Nat := 4983230072969 + 3 ^ 40 * 5260968 * 2
def baseEnd_5260968 : Nat := 900468430641025890735085

theorem tailTrace_5260968 : CollatzResearch.WordTrace tailWord_5260968 prefixEnd_5260968 900468430641025890735085 := by
  unfold tailWord_5260968
  simp only [CollatzResearch.WordTrace]
  refine ⟨95941633402209456323063779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127922177869612608430751705 95941633402209456323063779)
  ·
    refine ⟨143912450103314184484595669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95941633402209456323063779 143912450103314184484595669)
    ·
      refine ⟨3372948049296426198857711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 143912450103314184484595669 3372948049296426198857711)
      ·
        refine ⟨5059422073944639298286567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3372948049296426198857711 5059422073944639298286567)
        ·
          refine ⟨7589133110916958947429851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5059422073944639298286567 7589133110916958947429851)
          ·
            refine ⟨11383699666375438421144777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7589133110916958947429851 11383699666375438421144777)
            ·
              refine ⟨8537774749781578815858583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11383699666375438421144777 8537774749781578815858583)
              ·
                refine ⟨12806662124672368223787875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8537774749781578815858583 12806662124672368223787875)
                ·
                  refine ⟨19209993187008552335681813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12806662124672368223787875 19209993187008552335681813)
                  ·
                    refine ⟨900468430641025890735085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19209993187008552335681813 900468430641025890735085)
                    ·
                      rfl

theorem cell23_5260968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_5260968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5260968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5260968 prefixEnd_5260968 := by exact prefixLift 5260968
  have htrace : WordTrace (prefixWord ++ tailWord_5260968) baseStart_5260968 baseEnd_5260968 := by
    simpa [prefixWord, tailWord_5260968, baseEnd_5260968] using wordTrace_append hprefix tailTrace_5260968
  have hstable : (prefixWord ++ tailWord_5260968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5260968).length < 2 ^ (prefixWord ++ tailWord_5260968).sum := by decide
  have hdescent : baseEnd_5260968 < baseStart_5260968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5260968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261047 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 3]
def baseStart_5261047 : Nat := 118140960795 + 5261047 * 2 ^ 59
def prefixEnd_5261047 : Nat := 4983230072969 + 3 ^ 40 * 5261047 * 2
def baseEnd_5261047 : Nat := 2701445856894782863117391

theorem tailTrace_5261047 : CollatzResearch.WordTrace tailWord_5261047 prefixEnd_5261047 2701445856894782863117391 := by
  unfold tailWord_5261047
  simp only [CollatzResearch.WordTrace]
  refine ⟨191886148171132709138253395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127924098780755139425502263 191886148171132709138253395)
  ·
    refine ⟨287829222256699063707380093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191886148171132709138253395 287829222256699063707380093)
    ·
      refine ⟨107935958346262148890267535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287829222256699063707380093 107935958346262148890267535)
      ·
        refine ⟨161903937519393223335401303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107935958346262148890267535 161903937519393223335401303)
        ·
          refine ⟨242855906279089835003101955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161903937519393223335401303 242855906279089835003101955)
          ·
            refine ⟨364283859418634752504652933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242855906279089835003101955 364283859418634752504652933)
            ·
              refine ⟨68303223640994016094622425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 364283859418634752504652933 68303223640994016094622425)
              ·
                refine ⟨51227417730745512070966819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68303223640994016094622425 51227417730745512070966819)
                ·
                  refine ⟨76841126596118268106450229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51227417730745512070966819 76841126596118268106450229)
                  ·
                    refine ⟨7203855618386087634979709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76841126596118268106450229 7203855618386087634979709)
                    ·
                      refine ⟨2701445856894782863117391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7203855618386087634979709 2701445856894782863117391)
                      ·
                        rfl

theorem cell23_5261047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 3].length) (baseStart_5261047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261047 prefixEnd_5261047 := by exact prefixLift 5261047
  have htrace : WordTrace (prefixWord ++ tailWord_5261047) baseStart_5261047 baseEnd_5261047 := by
    simpa [prefixWord, tailWord_5261047, baseEnd_5261047] using wordTrace_append hprefix tailTrace_5261047
  have hstable : (prefixWord ++ tailWord_5261047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261047).length < 2 ^ (prefixWord ++ tailWord_5261047).sum := by decide
  have hdescent : baseEnd_5261047 < baseStart_5261047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261067 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 4, 5]
def baseStart_5261067 : Nat := 118140960795 + 5261067 * 2 ^ 59
def prefixEnd_5261067 : Nat := 4983230072969 + 3 ^ 40 * 5261067 * 2
def baseEnd_5261067 : Nat := 900485375502624261622433

theorem tailTrace_5261067 : CollatzResearch.WordTrace tailWord_5261067 prefixEnd_5261067 900485375502624261622433 := by
  unfold tailWord_5261067
  simp only [CollatzResearch.WordTrace]
  refine ⟨191886877631060252553981455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127924585087373501702654303 191886877631060252553981455)
  ·
    refine ⟨287830316446590378830972183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191886877631060252553981455 287830316446590378830972183)
    ·
      refine ⟨431745474669885568246458275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287830316446590378830972183 431745474669885568246458275)
      ·
        refine ⟨647618212004828352369687413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431745474669885568246458275 647618212004828352369687413)
        ·
          refine ⟨60714207375452658034658195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 647618212004828352369687413 60714207375452658034658195)
          ·
            refine ⟨91071311063178987051987293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60714207375452658034658195 91071311063178987051987293)
            ·
              refine ⟨34151741648692120144495235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91071311063178987051987293 34151741648692120144495235)
              ·
                refine ⟨51227612473038180216742853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34151741648692120144495235 51227612473038180216742853)
                ·
                  refine ⟨9605177338694658790639285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51227612473038180216742853 9605177338694658790639285)
                  ·
                    refine ⟨900485375502624261622433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9605177338694658790639285 900485375502624261622433)
                    ·
                      rfl

theorem cell23_5261067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 5].length) (baseStart_5261067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261067 prefixEnd_5261067 := by exact prefixLift 5261067
  have htrace : WordTrace (prefixWord ++ tailWord_5261067) baseStart_5261067 baseEnd_5261067 := by
    simpa [prefixWord, tailWord_5261067, baseEnd_5261067] using wordTrace_append hprefix tailTrace_5261067
  have hstable : (prefixWord ++ tailWord_5261067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261067).length < 2 ^ (prefixWord ++ tailWord_5261067).sum := by decide
  have hdescent : baseEnd_5261067 < baseStart_5261067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261076 : List Nat := [2, 4, 4, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_5261076 : Nat := 118140960795 + 5261076 * 2 ^ 59
def prefixEnd_5261076 : Nat := 4983230072969 + 3 ^ 40 * 5261076 * 2
def baseEnd_5261076 : Nat := 2701460747833763249654759

theorem tailTrace_5261076 : CollatzResearch.WordTrace tailWord_5261076 prefixEnd_5261076 2701460747833763249654759 := by
  unfold tailWord_5261076
  simp only [CollatzResearch.WordTrace]
  refine ⟨95943602944013823545529541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127924803925351764727372721 95943602944013823545529541)
  ·
    refine ⟨17989425552002591914786789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95943602944013823545529541 17989425552002591914786789)
    ·
      refine ⟨3373017291000485984022523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17989425552002591914786789 3373017291000485984022523)
      ·
        refine ⟨5059525936500728976033785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3373017291000485984022523 5059525936500728976033785)
        ·
          refine ⟨3794644452375546732025339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5059525936500728976033785 3794644452375546732025339)
          ·
            refine ⟨5691966678563320098038009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3794644452375546732025339 5691966678563320098038009)
            ·
              refine ⟨4268975008922490073528507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5691966678563320098038009 4268975008922490073528507)
              ·
                refine ⟨6403462513383735110292761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4268975008922490073528507 6403462513383735110292761)
                ·
                  refine ⟨4802596885037801332719571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6403462513383735110292761 4802596885037801332719571)
                  ·
                    refine ⟨7203895327556701999079357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4802596885037801332719571 7203895327556701999079357)
                    ·
                      refine ⟨2701460747833763249654759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7203895327556701999079357 2701460747833763249654759)
                      ·
                        rfl

theorem cell23_5261076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_5261076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261076 prefixEnd_5261076 := by exact prefixLift 5261076
  have htrace : WordTrace (prefixWord ++ tailWord_5261076) baseStart_5261076 baseEnd_5261076 := by
    simpa [prefixWord, tailWord_5261076, baseEnd_5261076] using wordTrace_append hprefix tailTrace_5261076
  have hstable : (prefixWord ++ tailWord_5261076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261076).length < 2 ^ (prefixWord ++ tailWord_5261076).sum := by decide
  have hdescent : baseEnd_5261076 < baseStart_5261076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261077 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 1, 1, 7]
def baseStart_5261077 : Nat := 118140960795 + 5261077 * 2 ^ 59
def prefixEnd_5261077 : Nat := 4983230072969 + 3 ^ 40 * 5261077 * 2
def baseEnd_5261077 : Nat := 2701461261314417745742253

theorem tailTrace_5261077 : CollatzResearch.WordTrace tailWord_5261077 prefixEnd_5261077 2701461261314417745742253 := by
  unfold tailWord_5261077
  simp only [CollatzResearch.WordTrace]
  refine ⟨191887242361024024261845485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127924828240682682841230323 191887242361024024261845485)
  ·
    refine ⟨71957715885384009098192057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191887242361024024261845485 71957715885384009098192057)
    ·
      refine ⟨53968286914038006823644043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71957715885384009098192057 53968286914038006823644043)
      ·
        refine ⟨80952430371057010235466065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53968286914038006823644043 80952430371057010235466065)
        ·
          refine ⟨60714322778292757676599549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80952430371057010235466065 60714322778292757676599549)
          ·
            refine ⟨22767871041859784128724831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60714322778292757676599549 22767871041859784128724831)
            ·
              refine ⟨34151806562789676193087247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22767871041859784128724831 34151806562789676193087247)
              ·
                refine ⟨51227709844184514289630871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34151806562789676193087247 51227709844184514289630871)
                ·
                  refine ⟨76841564766276771434446307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51227709844184514289630871 76841564766276771434446307)
                  ·
                    refine ⟨115262347149415157151669461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76841564766276771434446307 115262347149415157151669461)
                    ·
                      refine ⟨2701461261314417745742253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115262347149415157151669461 2701461261314417745742253)
                      ·
                        rfl

theorem cell23_5261077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_5261077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261077 prefixEnd_5261077 := by exact prefixLift 5261077
  have htrace : WordTrace (prefixWord ++ tailWord_5261077) baseStart_5261077 baseEnd_5261077 := by
    simpa [prefixWord, tailWord_5261077, baseEnd_5261077] using wordTrace_append hprefix tailTrace_5261077
  have hstable : (prefixWord ++ tailWord_5261077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261077).length < 2 ^ (prefixWord ++ tailWord_5261077).sum := by decide
  have hdescent : baseEnd_5261077 < baseStart_5261077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261104 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 6, 4, 2]
def baseStart_5261104 : Nat := 118140960795 + 5261104 * 2 ^ 59
def prefixEnd_5261104 : Nat := 4983230072969 + 3 ^ 40 * 5261104 * 2
def baseEnd_5261104 : Nat := 2701475125292089140104629

theorem tailTrace_5261104 : CollatzResearch.WordTrace tailWord_5261104 prefixEnd_5261104 2701475125292089140104629 := by
  unfold tailWord_5261104
  simp only [CollatzResearch.WordTrace]
  refine ⟨95944113565963103936539183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127925484754617471915385577 95944113565963103936539183)
  ·
    refine ⟨143916170348944655904808775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95944113565963103936539183 143916170348944655904808775)
    ·
      refine ⟨215874255523416983857213163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143916170348944655904808775 215874255523416983857213163)
      ·
        refine ⟨323811383285125475785819745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215874255523416983857213163 323811383285125475785819745)
        ·
          refine ⟨242858537463844106839364809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323811383285125475785819745 242858537463844106839364809)
          ·
            refine ⟨182143903097883080129523607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242858537463844106839364809 182143903097883080129523607)
            ·
              refine ⟨273215854646824620194285411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182143903097883080129523607 273215854646824620194285411)
              ·
                refine ⟨409823781970236930291428117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273215854646824620194285411 409823781970236930291428117)
                ·
                  refine ⟨19210489779854856107410693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 409823781970236930291428117 19210489779854856107410693)
                  ·
                    refine ⟨3601966833722785520139505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19210489779854856107410693 3601966833722785520139505)
                    ·
                      refine ⟨2701475125292089140104629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3601966833722785520139505 2701475125292089140104629)
                      ·
                        rfl

theorem cell23_5261104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 6, 4, 2].length) (baseStart_5261104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261104 prefixEnd_5261104 := by exact prefixLift 5261104
  have htrace : WordTrace (prefixWord ++ tailWord_5261104) baseStart_5261104 baseEnd_5261104 := by
    simpa [prefixWord, tailWord_5261104, baseEnd_5261104] using wordTrace_append hprefix tailTrace_5261104
  have hstable : (prefixWord ++ tailWord_5261104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261104).length < 2 ^ (prefixWord ++ tailWord_5261104).sum := by decide
  have hdescent : baseEnd_5261104 < baseStart_5261104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261127 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 8]
def baseStart_5261127 : Nat := 118140960795 + 5261127 * 2 ^ 59
def prefixEnd_5261127 : Nat := 4983230072969 + 3 ^ 40 * 5261127 * 2
def baseEnd_5261127 : Nat := 300165215038571394457447

theorem tailTrace_5261127 : CollatzResearch.WordTrace tailWord_5261127 prefixEnd_5261127 300165215038571394457447 := by
  unfold tailWord_5261127
  simp only [CollatzResearch.WordTrace]
  refine ⟨191889066010842882801165635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127926044007228588534110423 191889066010842882801165635)
  ·
    refine ⟨287833599016264324201748453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191889066010842882801165635 287833599016264324201748453)
    ·
      refine ⟨53968799815549560787827835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 287833599016264324201748453 53968799815549560787827835)
      ·
        refine ⟨80953199723324341181741753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53968799815549560787827835 80953199723324341181741753)
        ·
          refine ⟨60714899792493255886306315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80953199723324341181741753 60714899792493255886306315)
          ·
            refine ⟨91072349688739883829459473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60714899792493255886306315 91072349688739883829459473)
            ·
              refine ⟨68304262266554912872094605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91072349688739883829459473 68304262266554912872094605)
              ·
                refine ⟨25614098349958092327035477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68304262266554912872094605 25614098349958092327035477)
                ·
                  refine ⟨300165215038571394457447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25614098349958092327035477 300165215038571394457447)
                  ·
                    rfl

theorem cell23_5261127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 8].length) (baseStart_5261127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261127 prefixEnd_5261127 := by exact prefixLift 5261127
  have htrace : WordTrace (prefixWord ++ tailWord_5261127) baseStart_5261127 baseEnd_5261127 := by
    simpa [prefixWord, tailWord_5261127, baseEnd_5261127] using wordTrace_append hprefix tailTrace_5261127
  have hstable : (prefixWord ++ tailWord_5261127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261127).length < 2 ^ (prefixWord ++ tailWord_5261127).sum := by decide
  have hdescent : baseEnd_5261127 < baseStart_5261127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261148 : List Nat := [2, 2, 4, 2, 2, 1, 1, 2, 3, 4]
def baseStart_5261148 : Nat := 118140960795 + 5261148 * 2 ^ 59
def prefixEnd_5261148 : Nat := 4983230072969 + 3 ^ 40 * 5261148 * 2
def baseEnd_5261148 : Nat := 900499239480295655984809

theorem tailTrace_5261148 : CollatzResearch.WordTrace tailWord_5261148 prefixEnd_5261148 900499239480295655984809 := by
  unfold tailWord_5261148
  simp only [CollatzResearch.WordTrace]
  refine ⟨95944915971883401693840049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127926554629177868925120065 95944915971883401693840049)
  ·
    refine ⟨71958686978912551270380037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95944915971883401693840049 71958686978912551270380037)
    ·
      refine ⟨13492253808546103363196257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71958686978912551270380037 13492253808546103363196257)
      ·
        refine ⟨10119190356409577522397193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13492253808546103363196257 10119190356409577522397193)
        ·
          refine ⟨7589392767307183141797895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10119190356409577522397193 7589392767307183141797895)
          ·
            refine ⟨11384089150960774712696843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7589392767307183141797895 11384089150960774712696843)
            ·
              refine ⟨17076133726441162069045265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11384089150960774712696843 17076133726441162069045265)
              ·
                refine ⟨12807100294830871551783949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17076133726441162069045265 12807100294830871551783949)
                ·
                  refine ⟨4802662610561576831918981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12807100294830871551783949 4802662610561576831918981)
                  ·
                    refine ⟨900499239480295655984809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4802662610561576831918981 900499239480295655984809)
                    ·
                      rfl

theorem cell23_5261148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_5261148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261148 prefixEnd_5261148 := by exact prefixLift 5261148
  have htrace : WordTrace (prefixWord ++ tailWord_5261148) baseStart_5261148 baseEnd_5261148 := by
    simpa [prefixWord, tailWord_5261148, baseEnd_5261148] using wordTrace_append hprefix tailTrace_5261148
  have hstable : (prefixWord ++ tailWord_5261148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261148).length < 2 ^ (prefixWord ++ tailWord_5261148).sum := by decide
  have hdescent : baseEnd_5261148 < baseStart_5261148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261167 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 5]
def baseStart_5261167 : Nat := 118140960795 + 5261167 * 2 ^ 59
def prefixEnd_5261167 : Nat := 4983230072969 + 3 ^ 40 * 5261167 * 2
def baseEnd_5261167 : Nat := 2701507474573322393616839

theorem tailTrace_5261167 : CollatzResearch.WordTrace tailWord_5261167 prefixEnd_5261167 2701507474573322393616839 := by
  unfold tailWord_5261167
  simp only [CollatzResearch.WordTrace]
  refine ⟨191890524930697969632621755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127927016620465313088414503 191890524930697969632621755)
  ·
    refine ⟨287835787396046954448932633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191890524930697969632621755 287835787396046954448932633)
    ·
      refine ⟨215876840547035215836699475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287835787396046954448932633 215876840547035215836699475)
      ·
        refine ⟨323815260820552823755049213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215876840547035215836699475 323815260820552823755049213)
        ·
          refine ⟨121430722807707308908143455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 323815260820552823755049213 121430722807707308908143455)
          ·
            refine ⟨182146084211560963362215183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121430722807707308908143455 182146084211560963362215183)
            ·
              refine ⟨273219126317341445043322775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182146084211560963362215183 273219126317341445043322775)
              ·
                refine ⟨409828689476012167564984163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273219126317341445043322775 409828689476012167564984163)
                ·
                  refine ⟨614743034214018251347476245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 409828689476012167564984163 614743034214018251347476245)
                  ·
                    refine ⟨28816079728782105531912949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 614743034214018251347476245 28816079728782105531912949)
                    ·
                      refine ⟨2701507474573322393616839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28816079728782105531912949 2701507474573322393616839)
                      ·
                        rfl

theorem cell23_5261167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_5261167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261167 prefixEnd_5261167 := by exact prefixLift 5261167
  have htrace : WordTrace (prefixWord ++ tailWord_5261167) baseStart_5261167 baseEnd_5261167 := by
    simpa [prefixWord, tailWord_5261167, baseEnd_5261167] using wordTrace_append hprefix tailTrace_5261167
  have hstable : (prefixWord ++ tailWord_5261167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261167).length < 2 ^ (prefixWord ++ tailWord_5261167).sum := by decide
  have hdescent : baseEnd_5261167 < baseStart_5261167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261181 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 4, 3, 2]
def baseStart_5261181 : Nat := 118140960795 + 5261181 * 2 ^ 59
def prefixEnd_5261181 : Nat := 4983230072969 + 3 ^ 40 * 5261181 * 2
def baseEnd_5261181 : Nat := 2701514663302485338841775

theorem tailTrace_5261181 : CollatzResearch.WordTrace tailWord_5261181 prefixEnd_5261181 2701514663302485338841775 := by
  unfold tailWord_5261181
  simp only [CollatzResearch.WordTrace]
  refine ⟨191891035552647250023631397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127927357035098166682420931 191891035552647250023631397)
  ·
    refine ⟨35979569166121359379430887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191891035552647250023631397 35979569166121359379430887)
    ·
      refine ⟨53969353749182039069146331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35979569166121359379430887 53969353749182039069146331)
      ·
        refine ⟨80954030623773058603719497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53969353749182039069146331 80954030623773058603719497)
        ·
          refine ⟨60715522967829793952789623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80954030623773058603719497 60715522967829793952789623)
          ·
            refine ⟨91073284451744690929184435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60715522967829793952789623 91073284451744690929184435)
            ·
              refine ⟨136609926677617036393776653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91073284451744690929184435 136609926677617036393776653)
              ·
                refine ⟨51228722504106388647666245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136609926677617036393776653 51228722504106388647666245)
                ·
                  refine ⟨9605385469519947871437421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51228722504106388647666245 9605385469519947871437421)
                  ·
                    refine ⟨3602019551069980451789033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9605385469519947871437421 3602019551069980451789033)
                    ·
                      refine ⟨2701514663302485338841775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3602019551069980451789033 2701514663302485338841775)
                      ·
                        rfl

theorem cell23_5261181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 3, 2].length) (baseStart_5261181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261181 prefixEnd_5261181 := by exact prefixLift 5261181
  have htrace : WordTrace (prefixWord ++ tailWord_5261181) baseStart_5261181 baseEnd_5261181 := by
    simpa [prefixWord, tailWord_5261181, baseEnd_5261181] using wordTrace_append hprefix tailTrace_5261181
  have hstable : (prefixWord ++ tailWord_5261181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261181).length < 2 ^ (prefixWord ++ tailWord_5261181).sum := by decide
  have hdescent : baseEnd_5261181 < baseStart_5261181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261231 : List Nat := [1, 1, 2, 1, 2, 2, 3, 5, 1, 2, 3]
def baseStart_5261231 : Nat := 118140960795 + 5261231 * 2 ^ 59
def prefixEnd_5261231 : Nat := 4983230072969 + 3 ^ 40 * 5261231 * 2
def baseEnd_5261231 : Nat := 2701540337335210143216545

theorem tailTrace_5261231 : CollatzResearch.WordTrace tailWord_5261231 prefixEnd_5261231 2701540337335210143216545 := by
  unfold tailWord_5261231
  simp only [CollatzResearch.WordTrace]
  refine ⟨191892859202466108562951547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127928572801644072375301031 191892859202466108562951547)
  ·
    refine ⟨287839288803699162844427321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191892859202466108562951547 287839288803699162844427321)
    ·
      refine ⟨215879466602774372133320491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287839288803699162844427321 215879466602774372133320491)
      ·
        refine ⟨323819199904161558199980737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215879466602774372133320491 323819199904161558199980737)
        ·
          refine ⟨242864399928121168649985553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323819199904161558199980737 242864399928121168649985553)
          ·
            refine ⟨182148299946090876487489165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242864399928121168649985553 182148299946090876487489165)
            ·
              refine ⟨68305612479784078682808437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182148299946090876487489165 68305612479784078682808437)
              ·
                refine ⟨6403651169979757376513291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68305612479784078682808437 6403651169979757376513291)
                ·
                  refine ⟨9605476754969636064769937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6403651169979757376513291 9605476754969636064769937)
                  ·
                    refine ⟨7204107566227227048577453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9605476754969636064769937 7204107566227227048577453)
                    ·
                      refine ⟨2701540337335210143216545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7204107566227227048577453 2701540337335210143216545)
                      ·
                        rfl

theorem cell23_5261231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 2, 3].length) (baseStart_5261231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261231 prefixEnd_5261231 := by exact prefixLift 5261231
  have htrace : WordTrace (prefixWord ++ tailWord_5261231) baseStart_5261231 baseEnd_5261231 := by
    simpa [prefixWord, tailWord_5261231, baseEnd_5261231] using wordTrace_append hprefix tailTrace_5261231
  have hstable : (prefixWord ++ tailWord_5261231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261231).length < 2 ^ (prefixWord ++ tailWord_5261231).sum := by decide
  have hdescent : baseEnd_5261231 < baseStart_5261231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261245 : List Nat := [1, 4, 1, 2, 3, 1, 3, 1, 3, 2, 2]
def baseStart_5261245 : Nat := 118140960795 + 5261245 * 2 ^ 59
def prefixEnd_5261245 : Nat := 4983230072969 + 3 ^ 40 * 5261245 * 2
def baseEnd_5261245 : Nat := 2701547526064373088441481

theorem tailTrace_5261245 : CollatzResearch.WordTrace tailWord_5261245 prefixEnd_5261245 2701547526064373088441481 := by
  unfold tailWord_5261245
  simp only [CollatzResearch.WordTrace]
  refine ⟨191893369824415388953961189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127928913216276925969307459 191893369824415388953961189)
  ·
    refine ⟨35980006842077885428867723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191893369824415388953961189 35980006842077885428867723)
    ·
      refine ⟨53970010263116828143301585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35980006842077885428867723 53970010263116828143301585)
      ·
        refine ⟨40477507697337621107476189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53970010263116828143301585 40477507697337621107476189)
        ·
          refine ⟨15179065386501607915303571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40477507697337621107476189 15179065386501607915303571)
          ·
            refine ⟨22768598079752411872955357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15179065386501607915303571 22768598079752411872955357)
            ·
              refine ⟨8538224279907154452358259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22768598079752411872955357 8538224279907154452358259)
              ·
                refine ⟨12807336419860731678537389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8538224279907154452358259 12807336419860731678537389)
                ·
                  refine ⟨4802751157447774379451521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12807336419860731678537389 4802751157447774379451521)
                  ·
                    refine ⟨3602063368085830784588641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4802751157447774379451521 3602063368085830784588641)
                    ·
                      refine ⟨2701547526064373088441481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3602063368085830784588641 2701547526064373088441481)
                      ·
                        rfl

theorem cell23_5261245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_5261245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261245 prefixEnd_5261245 := by exact prefixLift 5261245
  have htrace : WordTrace (prefixWord ++ tailWord_5261245) baseStart_5261245 baseEnd_5261245 := by
    simpa [prefixWord, tailWord_5261245, baseEnd_5261245] using wordTrace_append hprefix tailTrace_5261245
  have hstable : (prefixWord ++ tailWord_5261245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261245).length < 2 ^ (prefixWord ++ tailWord_5261245).sum := by decide
  have hdescent : baseEnd_5261245 < baseStart_5261245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261282 : List Nat := [3, 3, 3, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_5261282 : Nat := 118140960795 + 5261282 * 2 ^ 59
def prefixEnd_5261282 : Nat := 4983230072969 + 3 ^ 40 * 5261282 * 2
def baseEnd_5261282 : Nat := 2701566524848589443678811

theorem tailTrace_5261282 : CollatzResearch.WordTrace tailWord_5261282 prefixEnd_5261282 2701566524848589443678811 := by
  unfold tailWord_5261282
  simp only [CollatzResearch.WordTrace]
  refine ⟨47973679831320336068264525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127929812883520896182038733 47973679831320336068264525)
  ·
    refine ⟨17990129936745126025599197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47973679831320336068264525 17990129936745126025599197)
    ·
      refine ⟨6746298726279422259599699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17990129936745126025599197 6746298726279422259599699)
      ·
        refine ⟨10119448089419133389399549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6746298726279422259599699 10119448089419133389399549)
        ·
          refine ⟨3794793033532175021024831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10119448089419133389399549 3794793033532175021024831)
          ·
            refine ⟨5692189550298262531537247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3794793033532175021024831 5692189550298262531537247)
            ·
              refine ⟨8538284325447393797305871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5692189550298262531537247 8538284325447393797305871)
              ·
                refine ⟨12807426488171090695958807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8538284325447393797305871 12807426488171090695958807)
                ·
                  refine ⟨19211139732256636043938211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12807426488171090695958807 19211139732256636043938211)
                  ·
                    refine ⟨28816709598384954065907317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19211139732256636043938211 28816709598384954065907317)
                    ·
                      refine ⟨2701566524848589443678811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28816709598384954065907317 2701566524848589443678811)
                      ·
                        rfl

theorem cell23_5261282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_5261282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261282 prefixEnd_5261282 := by exact prefixLift 5261282
  have htrace : WordTrace (prefixWord ++ tailWord_5261282) baseStart_5261282 baseEnd_5261282 := by
    simpa [prefixWord, tailWord_5261282, baseEnd_5261282] using wordTrace_append hprefix tailTrace_5261282
  have hstable : (prefixWord ++ tailWord_5261282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261282).length < 2 ^ (prefixWord ++ tailWord_5261282).sum := by decide
  have hdescent : baseEnd_5261282 < baseStart_5261282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261304 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 1, 3, 5]
def baseStart_5261304 : Nat := 118140960795 + 5261304 * 2 ^ 59
def prefixEnd_5261304 : Nat := 4983230072969 + 3 ^ 40 * 5261304 * 2
def baseEnd_5261304 : Nat := 2701577821422988357603709

theorem tailTrace_5261304 : CollatzResearch.WordTrace tailWord_5261304 prefixEnd_5261304 2701577821422988357603709 := by
  unfold tailWord_5261304
  simp only [CollatzResearch.WordTrace]
  refine ⟨95947760865600821015179483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127930347820801094686905977 95947760865600821015179483)
  ·
    refine ⟨143921641298401231522769225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95947760865600821015179483 143921641298401231522769225)
    ·
      refine ⟨107941230973800923642076919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143921641298401231522769225 107941230973800923642076919)
      ·
        refine ⟨161911846460701385463115379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107941230973800923642076919 161911846460701385463115379)
        ·
          refine ⟨242867769691052078194673069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161911846460701385463115379 242867769691052078194673069)
          ·
            refine ⟨91075413634144529323002401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242867769691052078194673069 91075413634144529323002401)
            ·
              refine ⟨68306560225608396992251801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91075413634144529323002401 68306560225608396992251801)
              ·
                refine ⟨51229920169206297744188851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68306560225608396992251801 51229920169206297744188851)
                ·
                  refine ⟨76844880253809446616283277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51229920169206297744188851 76844880253809446616283277)
                  ·
                    refine ⟨28816830095178542481106229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76844880253809446616283277 28816830095178542481106229)
                    ·
                      refine ⟨2701577821422988357603709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28816830095178542481106229 2701577821422988357603709)
                      ·
                        rfl

theorem cell23_5261304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_5261304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261304 prefixEnd_5261304 := by exact prefixLift 5261304
  have htrace : WordTrace (prefixWord ++ tailWord_5261304) baseStart_5261304 baseEnd_5261304 := by
    simpa [prefixWord, tailWord_5261304, baseEnd_5261304] using wordTrace_append hprefix tailTrace_5261304
  have hstable : (prefixWord ++ tailWord_5261304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261304).length < 2 ^ (prefixWord ++ tailWord_5261304).sum := by decide
  have hdescent : baseEnd_5261304 < baseStart_5261304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261358 : List Nat := [4, 1, 3, 1, 1, 3, 2, 1, 7]
def baseStart_5261358 : Nat := 118140960795 + 5261358 * 2 ^ 59
def prefixEnd_5261358 : Nat := 4983230072969 + 3 ^ 40 * 5261358 * 2
def baseEnd_5261358 : Nat := 300178394375370127369829

theorem tailTrace_5261358 : CollatzResearch.WordTrace tailWord_5261358 prefixEnd_5261358 300178394375370127369829 := by
  unfold tailWord_5261358
  simp only [CollatzResearch.WordTrace]
  refine ⟨23987186409125751156603091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127931660848670672835216485 23987186409125751156603091)
  ·
    refine ⟨35980779613688626734904637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23987186409125751156603091 35980779613688626734904637)
    ·
      refine ⟨13492792355133235025589239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35980779613688626734904637 13492792355133235025589239)
      ·
        refine ⟨20239188532699852538383859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13492792355133235025589239 20239188532699852538383859)
        ·
          refine ⟨30358782799049778807575789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20239188532699852538383859 30358782799049778807575789)
          ·
            refine ⟨11384543549643667052840921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30358782799049778807575789 11384543549643667052840921)
            ·
              refine ⟨8538407662232750289630691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11384543549643667052840921 8538407662232750289630691)
              ·
                refine ⟨12807611493349125434446037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8538407662232750289630691 12807611493349125434446037)
                ·
                  refine ⟨300178394375370127369829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12807611493349125434446037 300178394375370127369829)
                  ·
                    rfl

theorem cell23_5261358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_5261358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261358 prefixEnd_5261358 := by exact prefixLift 5261358
  have htrace : WordTrace (prefixWord ++ tailWord_5261358) baseStart_5261358 baseEnd_5261358 := by
    simpa [prefixWord, tailWord_5261358, baseEnd_5261358] using wordTrace_append hprefix tailTrace_5261358
  have hstable : (prefixWord ++ tailWord_5261358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261358).length < 2 ^ (prefixWord ++ tailWord_5261358).sum := by decide
  have hdescent : baseEnd_5261358 < baseStart_5261358 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261369 : List Nat := [1, 2, 1, 5, 3, 1, 3, 1, 2, 2, 2]
def baseStart_5261369 : Nat := 118140960795 + 5261369 * 2 ^ 59
def prefixEnd_5261369 : Nat := 4983230072969 + 3 ^ 40 * 5261369 * 2
def baseEnd_5261369 : Nat := 2701611197665530603290911

theorem tailTrace_5261369 : CollatzResearch.WordTrace tailWord_5261369 prefixEnd_5261369 2701611197665530603290911 := by
  unfold tailWord_5261369
  simp only [CollatzResearch.WordTrace]
  refine ⟨191897892475966158131475161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127931928317310772087650107 191897892475966158131475161)
  ·
    refine ⟨143923419356974618598606371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191897892475966158131475161 143923419356974618598606371)
    ·
      refine ⟨215885129035461927897909557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143923419356974618598606371 215885129035461927897909557)
      ·
        refine ⟨20239230847074555740429021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 215885129035461927897909557 20239230847074555740429021)
        ·
          refine ⟨7589711567652958402660883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20239230847074555740429021 7589711567652958402660883)
          ·
            refine ⟨11384567351479437603991325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7589711567652958402660883 11384567351479437603991325)
            ·
              refine ⟨4269212756804789101496747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11384567351479437603991325 4269212756804789101496747)
              ·
                refine ⟨6403819135207183652245121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4269212756804789101496747 6403819135207183652245121)
                ·
                  refine ⟨4802864351405387739183841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6403819135207183652245121 4802864351405387739183841)
                  ·
                    refine ⟨3602148263554040804387881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4802864351405387739183841 3602148263554040804387881)
                    ·
                      refine ⟨2701611197665530603290911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3602148263554040804387881 2701611197665530603290911)
                      ·
                        rfl

theorem cell23_5261369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_5261369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261369 prefixEnd_5261369 := by exact prefixLift 5261369
  have htrace : WordTrace (prefixWord ++ tailWord_5261369) baseStart_5261369 baseEnd_5261369 := by
    simpa [prefixWord, tailWord_5261369, baseEnd_5261369] using wordTrace_append hprefix tailTrace_5261369
  have hstable : (prefixWord ++ tailWord_5261369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261369).length < 2 ^ (prefixWord ++ tailWord_5261369).sum := by decide
  have hdescent : baseEnd_5261369 < baseStart_5261369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261405 : List Nat := [1, 4, 4, 1, 1, 2, 1, 2, 2, 5]
def baseStart_5261405 : Nat := 118140960795 + 5261405 * 2 ^ 59
def prefixEnd_5261405 : Nat := 4983230072969 + 3 ^ 40 * 5261405 * 2
def baseEnd_5261405 : Nat := 900543227656364154146915

theorem tailTrace_5261405 : CollatzResearch.WordTrace tailWord_5261405 prefixEnd_5261405 900543227656364154146915 := by
  unfold tailWord_5261405
  simp only [CollatzResearch.WordTrace]
  refine ⟨191899205503835736279785669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127932803669223824186523779 191899205503835736279785669)
  ·
    refine ⟨35981101031969200552459813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191899205503835736279785669 35981101031969200552459813)
    ·
      refine ⟨6746456443494225103586215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35981101031969200552459813 6746456443494225103586215)
      ·
        refine ⟨10119684665241337655379323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6746456443494225103586215 10119684665241337655379323)
        ·
          refine ⟨15179526997862006483068985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10119684665241337655379323 15179526997862006483068985)
          ·
            refine ⟨11384645248396504862301739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15179526997862006483068985 11384645248396504862301739)
            ·
              refine ⟨17076967872594757293452609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11384645248396504862301739 17076967872594757293452609)
              ·
                refine ⟨12807725904446067970089457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17076967872594757293452609 12807725904446067970089457)
                ·
                  refine ⟨9605794428334550977567093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12807725904446067970089457 9605794428334550977567093)
                  ·
                    refine ⟨900543227656364154146915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9605794428334550977567093 900543227656364154146915)
                    ·
                      rfl

theorem cell23_5261405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_5261405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261405 prefixEnd_5261405 := by exact prefixLift 5261405
  have htrace : WordTrace (prefixWord ++ tailWord_5261405) baseStart_5261405 baseEnd_5261405 := by
    simpa [prefixWord, tailWord_5261405, baseEnd_5261405] using wordTrace_append hprefix tailTrace_5261405
  have hstable : (prefixWord ++ tailWord_5261405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261405).length < 2 ^ (prefixWord ++ tailWord_5261405).sum := by decide
  have hdescent : baseEnd_5261405 < baseStart_5261405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261408 : List Nat := [2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 4]
def baseStart_5261408 : Nat := 118140960795 + 5261408 * 2 ^ 59
def prefixEnd_5261408 : Nat := 4983230072969 + 3 ^ 40 * 5261408 * 2
def baseEnd_5261408 : Nat := 2701631223411055950703231

theorem tailTrace_5261408 : CollatzResearch.WordTrace tailWord_5261408 prefixEnd_5261408 2701631223411055950703231 := by
  unfold tailWord_5261408
  simp only [CollatzResearch.WordTrace]
  refine ⟨95949657461412433896072439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127932876615216578528096585 95949657461412433896072439)
  ·
    refine ⟨143924486192118650844108659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95949657461412433896072439 143924486192118650844108659)
    ·
      refine ⟨215886729288177976266162989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143924486192118650844108659 215886729288177976266162989)
      ·
        refine ⟨80957523483066741099811121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215886729288177976266162989 80957523483066741099811121)
        ·
          refine ⟨60718142612300055824858341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80957523483066741099811121 60718142612300055824858341)
          ·
            refine ⟨11384651739806260467160939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60718142612300055824858341 11384651739806260467160939)
            ·
              refine ⟨17076977609709390700741409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11384651739806260467160939 17076977609709390700741409)
              ·
                refine ⟨12807733207282043025556057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17076977609709390700741409 12807733207282043025556057)
                ·
                  refine ⟨9605799905461532269167043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12807733207282043025556057 9605799905461532269167043)
                  ·
                    refine ⟨14408699858192298403750565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9605799905461532269167043 14408699858192298403750565)
                    ·
                      refine ⟨2701631223411055950703231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14408699858192298403750565 2701631223411055950703231)
                      ·
                        rfl

theorem cell23_5261408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_5261408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261408 prefixEnd_5261408 := by exact prefixLift 5261408
  have htrace : WordTrace (prefixWord ++ tailWord_5261408) baseStart_5261408 baseEnd_5261408 := by
    simpa [prefixWord, tailWord_5261408, baseEnd_5261408] using wordTrace_append hprefix tailTrace_5261408
  have hstable : (prefixWord ++ tailWord_5261408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261408).length < 2 ^ (prefixWord ++ tailWord_5261408).sum := by decide
  have hdescent : baseEnd_5261408 < baseStart_5261408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261445 : List Nat := [1, 3, 1, 1, 5, 2, 2, 1, 2, 2, 3]
def baseStart_5261445 : Nat := 118140960795 + 5261445 * 2 ^ 59
def prefixEnd_5261445 : Nat := 4983230072969 + 3 ^ 40 * 5261445 * 2
def baseEnd_5261445 : Nat := 2701650222195272305940561

theorem tailTrace_5261445 : CollatzResearch.WordTrace tailWord_5261445 prefixEnd_5261445 2701650222195272305940561 := by
  unfold tailWord_5261445
  simp only [CollatzResearch.WordTrace]
  refine ⟨191900664423690823111241789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127933776282460548740827859 191900664423690823111241789)
  ·
    refine ⟨71962749158884058666715671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191900664423690823111241789 71962749158884058666715671)
    ·
      refine ⟨107944123738326088000073507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71962749158884058666715671 107944123738326088000073507)
      ·
        refine ⟨161916185607489132000110261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107944123738326088000073507 161916185607489132000110261)
        ·
          refine ⟨15179642400702106125010337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 161916185607489132000110261 15179642400702106125010337)
          ·
            refine ⟨11384731800526579593757753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15179642400702106125010337 11384731800526579593757753)
            ·
              refine ⟨8538548850394934695318315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11384731800526579593757753 8538548850394934695318315)
              ·
                refine ⟨12807823275592402042977473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8538548850394934695318315 12807823275592402042977473)
                ·
                  refine ⟨9605867456694301532233105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12807823275592402042977473 9605867456694301532233105)
                  ·
                    refine ⟨7204400592520726149174829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9605867456694301532233105 7204400592520726149174829)
                    ·
                      refine ⟨2701650222195272305940561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7204400592520726149174829 2701650222195272305940561)
                      ·
                        rfl

theorem cell23_5261445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 2, 3].length) (baseStart_5261445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261445 prefixEnd_5261445 := by exact prefixLift 5261445
  have htrace : WordTrace (prefixWord ++ tailWord_5261445) baseStart_5261445 baseEnd_5261445 := by
    simpa [prefixWord, tailWord_5261445, baseEnd_5261445] using wordTrace_append hprefix tailTrace_5261445
  have hstable : (prefixWord ++ tailWord_5261445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261445).length < 2 ^ (prefixWord ++ tailWord_5261445).sum := by decide
  have hdescent : baseEnd_5261445 < baseStart_5261445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261469 : List Nat := [1, 4, 2, 1, 1, 5, 2, 2, 1, 4]
def baseStart_5261469 : Nat := 118140960795 + 5261469 * 2 ^ 59
def prefixEnd_5261469 : Nat := 4983230072969 + 3 ^ 40 * 5261469 * 2
def baseEnd_5261469 : Nat := 900554181910326737346817

theorem tailTrace_5261469 : CollatzResearch.WordTrace tailWord_5261469 prefixEnd_5261469 900554181910326737346817 := by
  unfold tailWord_5261469
  simp only [CollatzResearch.WordTrace]
  refine ⟨191901539775603875210115461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127934359850402583473410307 191901539775603875210115461)
  ·
    refine ⟨35981538707925726601896649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191901539775603875210115461 35981538707925726601896649)
    ·
      refine ⟨26986154030944294951422487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35981538707925726601896649 26986154030944294951422487)
      ·
        refine ⟨40479231046416442427133731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26986154030944294951422487 40479231046416442427133731)
        ·
          refine ⟨60718846569624663640700597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40479231046416442427133731 60718846569624663640700597)
          ·
            refine ⟨5692391865902312216315681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60718846569624663640700597 5692391865902312216315681)
            ·
              refine ⟨4269293899426734162236761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5692391865902312216315681 4269293899426734162236761)
              ·
                refine ⟨3201970424570050621677571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4269293899426734162236761 3201970424570050621677571)
                ·
                  refine ⟨4802955636855075932516357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3201970424570050621677571 4802955636855075932516357)
                  ·
                    refine ⟨900554181910326737346817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4802955636855075932516357 900554181910326737346817)
                    ·
                      rfl

theorem cell23_5261469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_5261469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261469 prefixEnd_5261469 := by exact prefixLift 5261469
  have htrace : WordTrace (prefixWord ++ tailWord_5261469) baseStart_5261469 baseEnd_5261469 := by
    simpa [prefixWord, tailWord_5261469, baseEnd_5261469] using wordTrace_append hprefix tailTrace_5261469
  have hstable : (prefixWord ++ tailWord_5261469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261469).length < 2 ^ (prefixWord ++ tailWord_5261469).sum := by decide
  have hdescent : baseEnd_5261469 < baseStart_5261469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261498 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4]
def baseStart_5261498 : Nat := 118140960795 + 5261498 * 2 ^ 59
def prefixEnd_5261498 : Nat := 4983230072969 + 3 ^ 40 * 5261498 * 2
def baseEnd_5261498 : Nat := 2701677436669960598577817

theorem tailTrace_5261498 : CollatzResearch.WordTrace tailWord_5261498 prefixEnd_5261498 2701677436669960598577817 := by
  unfold tailWord_5261498
  simp only [CollatzResearch.WordTrace]
  refine ⟨47975649373124703290730287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127935064994999208775280765 47975649373124703290730287)
  ·
    refine ⟨71963474059687054936095431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47975649373124703290730287 71963474059687054936095431)
    ·
      refine ⟨107945211089530582404143147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71963474059687054936095431 107945211089530582404143147)
      ·
        refine ⟨161917816634295873606214721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107945211089530582404143147 161917816634295873606214721)
        ·
          refine ⟨121438362475721905204661041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161917816634295873606214721 121438362475721905204661041)
          ·
            refine ⟨91078771856791428903495781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121438362475721905204661041 91078771856791428903495781)
            ·
              refine ⟨17077269723148392919405459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91078771856791428903495781 17077269723148392919405459)
              ·
                refine ⟨25615904584722589379108189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17077269723148392919405459 25615904584722589379108189)
                ·
                  refine ⟨9605964219270971017165571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25615904584722589379108189 9605964219270971017165571)
                  ·
                    refine ⟨14408946328906456525748357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9605964219270971017165571 14408946328906456525748357)
                    ·
                      refine ⟨2701677436669960598577817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14408946328906456525748357 2701677436669960598577817)
                      ·
                        rfl

theorem cell23_5261498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_5261498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261498 prefixEnd_5261498 := by exact prefixLift 5261498
  have htrace : WordTrace (prefixWord ++ tailWord_5261498) baseStart_5261498 baseEnd_5261498 := by
    simpa [prefixWord, tailWord_5261498, baseEnd_5261498] using wordTrace_append hprefix tailTrace_5261498
  have hstable : (prefixWord ++ tailWord_5261498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261498).length < 2 ^ (prefixWord ++ tailWord_5261498).sum := by decide
  have hdescent : baseEnd_5261498 < baseStart_5261498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261502 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2]
def baseStart_5261502 : Nat := 118140960795 + 5261502 * 2 ^ 59
def prefixEnd_5261502 : Nat := 4983230072969 + 3 ^ 40 * 5261502 * 2
def baseEnd_5261502 : Nat := 2701679490592578582927799

theorem tailTrace_5261502 : CollatzResearch.WordTrace tailWord_5261502 prefixEnd_5261502 2701679490592578582927799 := by
  unfold tailWord_5261502
  simp only [CollatzResearch.WordTrace]
  refine ⟨23987842923060540230758345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127935162256322881230711173 23987842923060540230758345)
  ·
    refine ⟨17990882192295405173068759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23987842923060540230758345 17990882192295405173068759)
    ·
      refine ⟨26986323288443107759603139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17990882192295405173068759 26986323288443107759603139)
      ·
        refine ⟨40479484932664661639404709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26986323288443107759603139 40479484932664661639404709)
        ·
          refine ⟨7589903424874624057388383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40479484932664661639404709 7589903424874624057388383)
          ·
            refine ⟨11384855137311936086082575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7589903424874624057388383 11384855137311936086082575)
            ·
              refine ⟨17077282705967904129123863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11384855137311936086082575 17077282705967904129123863)
              ·
                refine ⟨25615924058951856193685795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17077282705967904129123863 25615924058951856193685795)
                ·
                  refine ⟨38423886088427784290528693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25615924058951856193685795 38423886088427784290528693)
                  ·
                    refine ⟨3602239320790104777237065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38423886088427784290528693 3602239320790104777237065)
                    ·
                      refine ⟨2701679490592578582927799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3602239320790104777237065 2701679490592578582927799)
                      ·
                        rfl

theorem cell23_5261502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_5261502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261502 prefixEnd_5261502 := by exact prefixLift 5261502
  have htrace : WordTrace (prefixWord ++ tailWord_5261502) baseStart_5261502 baseEnd_5261502 := by
    simpa [prefixWord, tailWord_5261502, baseEnd_5261502] using wordTrace_append hprefix tailTrace_5261502
  have hstable : (prefixWord ++ tailWord_5261502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261502).length < 2 ^ (prefixWord ++ tailWord_5261502).sum := by decide
  have hdescent : baseEnd_5261502 < baseStart_5261502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261511 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 6]
def baseStart_5261511 : Nat := 118140960795 + 5261511 * 2 ^ 59
def prefixEnd_5261511 : Nat := 4983230072969 + 3 ^ 40 * 5261511 * 2
def baseEnd_5261511 : Nat := 2701684111918469047715257

theorem tailTrace_5261511 : CollatzResearch.WordTrace tailWord_5261511 prefixEnd_5261511 2701684111918469047715257 := by
  unfold tailWord_5261511
  simp only [CollatzResearch.WordTrace]
  refine ⟨191903071641451716383144387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127935381094301144255429591 191903071641451716383144387)
  ·
    refine ⟨287854607462177574574716581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191903071641451716383144387 287854607462177574574716581)
    ·
      refine ⟨53972738899158295232759359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 287854607462177574574716581 53972738899158295232759359)
      ·
        refine ⟨80959108348737442849139039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53972738899158295232759359 80959108348737442849139039)
        ·
          refine ⟨121438662523106164273708559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80959108348737442849139039 121438662523106164273708559)
          ·
            refine ⟨182157993784659246410562839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121438662523106164273708559 182157993784659246410562839)
            ·
              refine ⟨273236990676988869615844259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182157993784659246410562839 273236990676988869615844259)
              ·
                refine ⟨409855486015483304423766389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273236990676988869615844259 409855486015483304423766389)
                ·
                  refine ⟨38423951813951559789728099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 409855486015483304423766389 38423951813951559789728099)
                  ·
                    refine ⟨57635927720927339684592149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38423951813951559789728099 57635927720927339684592149)
                    ·
                      refine ⟨2701684111918469047715257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57635927720927339684592149 2701684111918469047715257)
                      ·
                        rfl

theorem cell23_5261511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_5261511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261511 prefixEnd_5261511 := by exact prefixLift 5261511
  have htrace : WordTrace (prefixWord ++ tailWord_5261511) baseStart_5261511 baseEnd_5261511 := by
    simpa [prefixWord, tailWord_5261511, baseEnd_5261511] using wordTrace_append hprefix tailTrace_5261511
  have hstable : (prefixWord ++ tailWord_5261511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261511).length < 2 ^ (prefixWord ++ tailWord_5261511).sum := by decide
  have hdescent : baseEnd_5261511 < baseStart_5261511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261515 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 5, 2, 2]
def baseStart_5261515 : Nat := 118140960795 + 5261515 * 2 ^ 59
def prefixEnd_5261515 : Nat := 4983230072969 + 3 ^ 40 * 5261515 * 2
def baseEnd_5261515 : Nat := 2701686165841087032065239

theorem tailTrace_5261515 : CollatzResearch.WordTrace tailWord_5261515 prefixEnd_5261515 2701686165841087032065239 := by
  unfold tailWord_5261515
  simp only [CollatzResearch.WordTrace]
  refine ⟨191903217533437225066289999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127935478355624816710859999 191903217533437225066289999)
  ·
    refine ⟨287854826300155837599434999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191903217533437225066289999 287854826300155837599434999)
    ·
      refine ⟨431782239450233756399152499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287854826300155837599434999 431782239450233756399152499)
      ·
        refine ⟨647673359175350634598728749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431782239450233756399152499 647673359175350634598728749)
        ·
          refine ⟨242877509690756487974523281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 647673359175350634598728749 242877509690756487974523281)
          ·
            refine ⟨182158132268067365980892461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242877509690756487974523281 182158132268067365980892461)
            ·
              refine ⟨68309299600525262242834673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182158132268067365980892461 68309299600525262242834673)
              ·
                refine ⟨51231974700393946682126005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68309299600525262242834673 51231974700393946682126005)
                ·
                  refine ⟨4802997628161932501449313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51231974700393946682126005 4802997628161932501449313)
                  ·
                    refine ⟨3602248221121449376086985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4802997628161932501449313 3602248221121449376086985)
                    ·
                      refine ⟨2701686165841087032065239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3602248221121449376086985 2701686165841087032065239)
                      ·
                        rfl

theorem cell23_5261515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 2, 2].length) (baseStart_5261515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261515 prefixEnd_5261515 := by exact prefixLift 5261515
  have htrace : WordTrace (prefixWord ++ tailWord_5261515) baseStart_5261515 baseEnd_5261515 := by
    simpa [prefixWord, tailWord_5261515, baseEnd_5261515] using wordTrace_append hprefix tailTrace_5261515
  have hstable : (prefixWord ++ tailWord_5261515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261515).length < 2 ^ (prefixWord ++ tailWord_5261515).sum := by decide
  have hdescent : baseEnd_5261515 < baseStart_5261515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261526 : List Nat := [5, 2, 1, 2, 1, 1, 2, 4, 1, 1, 3]
def baseStart_5261526 : Nat := 118140960795 + 5261526 * 2 ^ 59
def prefixEnd_5261526 : Nat := 4983230072969 + 3 ^ 40 * 5261526 * 2
def baseEnd_5261526 : Nat := 2701691814128286489027689

theorem tailTrace_5261526 : CollatzResearch.WordTrace tailWord_5261526 prefixEnd_5261526 2701691814128286489027689 := by
  unfold tailWord_5261526
  simp only [CollatzResearch.WordTrace]
  refine ⟨11993976171024835871558777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127935745824264915963293621 11993976171024835871558777)
  ·
    refine ⟨8995482128268626903669083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11993976171024835871558777 8995482128268626903669083)
    ·
      refine ⟨13493223192402940355503625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8995482128268626903669083 13493223192402940355503625)
      ·
        refine ⟨10119917394302205266627719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13493223192402940355503625 10119917394302205266627719)
        ·
          refine ⟨15179876091453307899941579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10119917394302205266627719 15179876091453307899941579)
          ·
            refine ⟨22769814137179961849912369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15179876091453307899941579 22769814137179961849912369)
            ·
              refine ⟨17077360602884971387434277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22769814137179961849912369 17077360602884971387434277)
              ·
                refine ⟨3202005113040932135143927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17077360602884971387434277 3202005113040932135143927)
                ·
                  refine ⟨4803007669561398202715891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3202005113040932135143927 4803007669561398202715891)
                  ·
                    refine ⟨7204511504342097304073837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4803007669561398202715891 7204511504342097304073837)
                    ·
                      refine ⟨2701691814128286489027689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7204511504342097304073837 2701691814128286489027689)
                      ·
                        rfl

theorem cell23_5261526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_5261526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261526 prefixEnd_5261526 := by exact prefixLift 5261526
  have htrace : WordTrace (prefixWord ++ tailWord_5261526) baseStart_5261526 baseEnd_5261526 := by
    simpa [prefixWord, tailWord_5261526, baseEnd_5261526] using wordTrace_append hprefix tailTrace_5261526
  have hstable : (prefixWord ++ tailWord_5261526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261526).length < 2 ^ (prefixWord ++ tailWord_5261526).sum := by decide
  have hdescent : baseEnd_5261526 < baseStart_5261526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261582 : List Nat := [4, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3]
def baseStart_5261582 : Nat := 118140960795 + 5261582 * 2 ^ 59
def prefixEnd_5261582 : Nat := 4983230072969 + 3 ^ 40 * 5261582 * 2
def baseEnd_5261582 : Nat := 2701720569044938269927431

theorem tailTrace_5261582 : CollatzResearch.WordTrace tailWord_5261582 prefixEnd_5261582 2701720569044938269927431 := by
  unfold tailWord_5261582
  simp only [CollatzResearch.WordTrace]
  refine ⟨23988207653024311938622375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127937107482796330339319333 23988207653024311938622375)
  ·
    refine ⟨35982311479536467907933563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23988207653024311938622375 35982311479536467907933563)
    ·
      refine ⟨53973467219304701861900345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35982311479536467907933563 53973467219304701861900345)
      ·
        refine ⟨40480100414478526396425259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53973467219304701861900345 40480100414478526396425259)
        ·
          refine ⟨60720150621717789594637889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40480100414478526396425259 60720150621717789594637889)
          ·
            refine ⟨45540112966288342195978417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60720150621717789594637889 45540112966288342195978417)
            ·
              refine ⟨34155084724716256646983813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45540112966288342195978417 34155084724716256646983813)
              ·
                refine ⟨6404078385884298121309465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34155084724716256646983813 6404078385884298121309465)
                ·
                  refine ⟨4803058789413223590982099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6404078385884298121309465 4803058789413223590982099)
                  ·
                    refine ⟨7204588184119835386473149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4803058789413223590982099 7204588184119835386473149)
                    ·
                      refine ⟨2701720569044938269927431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7204588184119835386473149 2701720569044938269927431)
                      ·
                        rfl

theorem cell23_5261582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_5261582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261582 prefixEnd_5261582 := by exact prefixLift 5261582
  have htrace : WordTrace (prefixWord ++ tailWord_5261582) baseStart_5261582 baseEnd_5261582 := by
    simpa [prefixWord, tailWord_5261582, baseEnd_5261582] using wordTrace_append hprefix tailTrace_5261582
  have hstable : (prefixWord ++ tailWord_5261582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261582).length < 2 ^ (prefixWord ++ tailWord_5261582).sum := by decide
  have hdescent : baseEnd_5261582 < baseStart_5261582 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261599 : List Nat := [1, 1, 2, 4, 3, 1, 4, 1, 2, 1, 3]
def baseStart_5261599 : Nat := 118140960795 + 5261599 * 2 ^ 59
def prefixEnd_5261599 : Nat := 4983230072969 + 3 ^ 40 * 5261599 * 2
def baseEnd_5261599 : Nat := 2701729298216064703414853

theorem tailTrace_5261599 : CollatzResearch.WordTrace tailWord_5261599 prefixEnd_5261599 2701729298216064703414853 := by
  unfold tailWord_5261599
  simp only [CollatzResearch.WordTrace]
  refine ⟨191906281265132907412347851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127937520843421938274898567 191906281265132907412347851)
  ·
    refine ⟨287859421897699361118521777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191906281265132907412347851 287859421897699361118521777)
    ·
      refine ⟨215894566423274520838891333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287859421897699361118521777 215894566423274520838891333)
      ·
        refine ⟨40480231204363972657292125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 215894566423274520838891333 40480231204363972657292125)
        ·
          refine ⟨15180086701636489746484547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40480231204363972657292125 15180086701636489746484547)
          ·
            refine ⟨22770130052454734619726821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15180086701636489746484547 22770130052454734619726821)
            ·
              refine ⟨4269399384835262741198779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22770130052454734619726821 4269399384835262741198779)
              ·
                refine ⟨6404099077252894111798169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4269399384835262741198779 6404099077252894111798169)
                ·
                  refine ⟨4803074307939670583848627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6404099077252894111798169 4803074307939670583848627)
                  ·
                    refine ⟨7204611461909505875772941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4803074307939670583848627 7204611461909505875772941)
                    ·
                      refine ⟨2701729298216064703414853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7204611461909505875772941 2701729298216064703414853)
                      ·
                        rfl

theorem cell23_5261599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_5261599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261599 prefixEnd_5261599 := by exact prefixLift 5261599
  have htrace : WordTrace (prefixWord ++ tailWord_5261599) baseStart_5261599 baseEnd_5261599 := by
    simpa [prefixWord, tailWord_5261599, baseEnd_5261599] using wordTrace_append hprefix tailTrace_5261599
  have hstable : (prefixWord ++ tailWord_5261599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261599).length < 2 ^ (prefixWord ++ tailWord_5261599).sum := by decide
  have hdescent : baseEnd_5261599 < baseStart_5261599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261625 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 2, 1, 5]
def baseStart_5261625 : Nat := 118140960795 + 5261625 * 2 ^ 59
def prefixEnd_5261625 : Nat := 4983230072969 + 3 ^ 40 * 5261625 * 2
def baseEnd_5261625 : Nat := 2701742648713081601689733

theorem tailTrace_5261625 : CollatzResearch.WordTrace tailWord_5261625 prefixEnd_5261625 2701742648713081601689733 := by
  unfold tailWord_5261625
  simp only [CollatzResearch.WordTrace]
  refine ⟨191907229563038713852794329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127938153042025809235196219 191907229563038713852794329)
  ·
    refine ⟨143930422172279035389595747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191907229563038713852794329 143930422172279035389595747)
    ·
      refine ⟨215895633258418553084393621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143930422172279035389595747 215895633258418553084393621)
      ·
        refine ⟨10120107808988369675830951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 215895633258418553084393621 10120107808988369675830951)
        ·
          refine ⟨15180161713482554513746427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10120107808988369675830951 15180161713482554513746427)
          ·
            refine ⟨22770242570223831770619641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15180161713482554513746427 22770242570223831770619641)
            ·
              refine ⟨17077681927667873827964731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22770242570223831770619641 17077681927667873827964731)
              ·
                refine ⟨25616522891501810741947097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17077681927667873827964731 25616522891501810741947097)
                ·
                  refine ⟨19212392168626358056460323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25616522891501810741947097 19212392168626358056460323)
                  ·
                    refine ⟨28818588252939537084690485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19212392168626358056460323 28818588252939537084690485)
                    ·
                      refine ⟨2701742648713081601689733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28818588252939537084690485 2701742648713081601689733)
                      ·
                        rfl

theorem cell23_5261625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_5261625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261625 prefixEnd_5261625 := by exact prefixLift 5261625
  have htrace : WordTrace (prefixWord ++ tailWord_5261625) baseStart_5261625 baseEnd_5261625 := by
    simpa [prefixWord, tailWord_5261625, baseEnd_5261625] using wordTrace_append hprefix tailTrace_5261625
  have hstable : (prefixWord ++ tailWord_5261625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261625).length < 2 ^ (prefixWord ++ tailWord_5261625).sum := by decide
  have hdescent : baseEnd_5261625 < baseStart_5261625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261639 : List Nat := [1, 1, 4, 1, 2, 2, 4, 2, 2, 2, 2]
def baseStart_5261639 : Nat := 118140960795 + 5261639 * 2 ^ 59
def prefixEnd_5261639 : Nat := 4983230072969 + 3 ^ 40 * 5261639 * 2
def baseEnd_5261639 : Nat := 2701749837442244546914669

theorem tailTrace_5261639 : CollatzResearch.WordTrace tailWord_5261639 prefixEnd_5261639 2701749837442244546914669 := by
  unfold tailWord_5261639
  simp only [CollatzResearch.WordTrace]
  refine ⟨191907740184987994243803971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127938493456658662829202647 191907740184987994243803971)
  ·
    refine ⟨287861610277481991365705957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191907740184987994243803971 287861610277481991365705957)
    ·
      refine ⟨53974051927027873381069867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 287861610277481991365705957 53974051927027873381069867)
      ·
        refine ⟨80961077890541810071604801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53974051927027873381069867 80961077890541810071604801)
        ·
          refine ⟨60720808417906357553703601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80961077890541810071604801 60720808417906357553703601)
          ·
            refine ⟨45540606313429768165277701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60720808417906357553703601 45540606313429768165277701)
            ·
              refine ⟨8538863683768081530989569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45540606313429768165277701 8538863683768081530989569)
              ·
                refine ⟨6404147762826061148242177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8538863683768081530989569 6404147762826061148242177)
                ·
                  refine ⟨4803110822119545861181633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6404147762826061148242177 4803110822119545861181633)
                  ·
                    refine ⟨3602333116589659395886225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4803110822119545861181633 3602333116589659395886225)
                    ·
                      refine ⟨2701749837442244546914669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3602333116589659395886225 2701749837442244546914669)
                      ·
                        rfl

theorem cell23_5261639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 2, 2].length) (baseStart_5261639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261639 prefixEnd_5261639 := by exact prefixLift 5261639
  have htrace : WordTrace (prefixWord ++ tailWord_5261639) baseStart_5261639 baseEnd_5261639 := by
    simpa [prefixWord, tailWord_5261639, baseEnd_5261639] using wordTrace_append hprefix tailTrace_5261639
  have hstable : (prefixWord ++ tailWord_5261639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261639).length < 2 ^ (prefixWord ++ tailWord_5261639).sum := by decide
  have hdescent : baseEnd_5261639 < baseStart_5261639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261655 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 3]
def baseStart_5261655 : Nat := 118140960795 + 5261655 * 2 ^ 59
def prefixEnd_5261655 : Nat := 4983230072969 + 3 ^ 40 * 5261655 * 2
def baseEnd_5261655 : Nat := 2701758053132716484314595

theorem tailTrace_5261655 : CollatzResearch.WordTrace tailWord_5261655 prefixEnd_5261655 2701758053132716484314595 := by
  unfold tailWord_5261655
  simp only [CollatzResearch.WordTrace]
  refine ⟨191908323752930028976386419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127938882501953352650924279 191908323752930028976386419)
  ·
    refine ⟨287862485629395043464579629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191908323752930028976386419 287862485629395043464579629)
    ·
      refine ⟨107948432111023141299217361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287862485629395043464579629 107948432111023141299217361)
      ·
        refine ⟨80961324083267355974413021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107948432111023141299217361 80961324083267355974413021)
        ·
          refine ⟨30360496531225258490404883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80961324083267355974413021 30360496531225258490404883)
          ·
            refine ⟨45540744796837887735607325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30360496531225258490404883 45540744796837887735607325)
            ·
              refine ⟨17077779298814207900852747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45540744796837887735607325 17077779298814207900852747)
              ·
                refine ⟨25616668948221311851279121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17077779298814207900852747 25616668948221311851279121)
                ·
                  refine ⟨19212501711165983888459341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25616668948221311851279121 19212501711165983888459341)
                  ·
                    refine ⟨7204688141687243958172253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19212501711165983888459341 7204688141687243958172253)
                    ·
                      refine ⟨2701758053132716484314595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7204688141687243958172253 2701758053132716484314595)
                      ·
                        rfl

theorem cell23_5261655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_5261655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261655 prefixEnd_5261655 := by exact prefixLift 5261655
  have htrace : WordTrace (prefixWord ++ tailWord_5261655) baseStart_5261655 baseEnd_5261655 := by
    simpa [prefixWord, tailWord_5261655, baseEnd_5261655] using wordTrace_append hprefix tailTrace_5261655
  have hstable : (prefixWord ++ tailWord_5261655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261655).length < 2 ^ (prefixWord ++ tailWord_5261655).sum := by decide
  have hdescent : baseEnd_5261655 < baseStart_5261655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261658 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 1, 7]
def baseStart_5261658 : Nat := 118140960795 + 5261658 * 2 ^ 59
def prefixEnd_5261658 : Nat := 4983230072969 + 3 ^ 40 * 5261658 * 2
def baseEnd_5261658 : Nat := 900586531191559990859027

theorem tailTrace_5261658 : CollatzResearch.WordTrace tailWord_5261658 prefixEnd_5261658 900586531191559990859027 := by
  unfold tailWord_5261658
  simp only [CollatzResearch.WordTrace]
  refine ⟨47977108292979790122186407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127938955447946106992497085 47977108292979790122186407)
  ·
    refine ⟨71965662439469685183279611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47977108292979790122186407 71965662439469685183279611)
    ·
      refine ⟨107948493659204527774919417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71965662439469685183279611 107948493659204527774919417)
      ·
        refine ⟨80961370244403395831189563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107948493659204527774919417 80961370244403395831189563)
        ·
          refine ⟨121442055366605093746784345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80961370244403395831189563 121442055366605093746784345)
          ·
            refine ⟨91081541524953820310088259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121442055366605093746784345 91081541524953820310088259)
            ·
              refine ⟨136622312287430730465132389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91081541524953820310088259 136622312287430730465132389)
              ·
                refine ⟨25616683553893261962212323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136622312287430730465132389 25616683553893261962212323)
                ·
                  refine ⟨38425025330839892943318485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25616683553893261962212323 38425025330839892943318485)
                  ·
                    refine ⟨900586531191559990859027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38425025330839892943318485 900586531191559990859027)
                    ·
                      rfl

theorem cell23_5261658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_5261658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261658 prefixEnd_5261658 := by exact prefixLift 5261658
  have htrace : WordTrace (prefixWord ++ tailWord_5261658) baseStart_5261658 baseEnd_5261658 := by
    simpa [prefixWord, tailWord_5261658, baseEnd_5261658] using wordTrace_append hprefix tailTrace_5261658
  have hstable : (prefixWord ++ tailWord_5261658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261658).length < 2 ^ (prefixWord ++ tailWord_5261658).sum := by decide
  have hdescent : baseEnd_5261658 < baseStart_5261658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261695 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 3, 6, 2]
def baseStart_5261695 : Nat := 118140960795 + 5261695 * 2 ^ 59
def prefixEnd_5261695 : Nat := 4983230072969 + 3 ^ 40 * 5261695 * 2
def baseEnd_5261695 : Nat := 2701778592358896327814411

theorem tailTrace_5261695 : CollatzResearch.WordTrace tailWord_5261695 prefixEnd_5261695 2701778592358896327814411 := by
  unfold tailWord_5261695
  simp only [CollatzResearch.WordTrace]
  refine ⟨191909782672785115807842539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127939855115190077205228359 191909782672785115807842539)
  ·
    refine ⟨287864674009177673711763809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191909782672785115807842539 287864674009177673711763809)
    ·
      refine ⟨215898505506883255283822857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287864674009177673711763809 215898505506883255283822857)
      ·
        refine ⟨161923879130162441462867143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215898505506883255283822857 161923879130162441462867143)
        ·
          refine ⟨242885818695243662194300715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161923879130162441462867143 242885818695243662194300715)
          ·
            refine ⟨364328728042865493291451073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242885818695243662194300715 364328728042865493291451073)
            ·
              refine ⟨273246546032149119968588305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 364328728042865493291451073 273246546032149119968588305)
              ·
                refine ⟨204934909524111839976441229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273246546032149119968588305 204934909524111839976441229)
                ·
                  refine ⟨76850591071541939991165461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204934909524111839976441229 76850591071541939991165461)
                  ·
                    refine ⟨3602371456478528437085881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76850591071541939991165461 3602371456478528437085881)
                    ·
                      refine ⟨2701778592358896327814411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3602371456478528437085881 2701778592358896327814411)
                      ·
                        rfl

theorem cell23_5261695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 6, 2].length) (baseStart_5261695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261695 prefixEnd_5261695 := by exact prefixLift 5261695
  have htrace : WordTrace (prefixWord ++ tailWord_5261695) baseStart_5261695 baseEnd_5261695 := by
    simpa [prefixWord, tailWord_5261695, baseEnd_5261695] using wordTrace_append hprefix tailTrace_5261695
  have hstable : (prefixWord ++ tailWord_5261695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261695).length < 2 ^ (prefixWord ++ tailWord_5261695).sum := by decide
  have hdescent : baseEnd_5261695 < baseStart_5261695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261722 : List Nat := [3, 1, 1, 4, 1, 2, 2, 2, 3, 4]
def baseStart_5261722 : Nat := 118140960795 + 5261722 * 2 ^ 59
def prefixEnd_5261722 : Nat := 4983230072969 + 3 ^ 40 * 5261722 * 2
def baseEnd_5261722 : Nat := 900597485445522574058929

theorem tailTrace_5261722 : CollatzResearch.WordTrace tailWord_5261722 prefixEnd_5261722 900597485445522574058929 := by
  unfold tailWord_5261722
  simp only [CollatzResearch.WordTrace]
  refine ⟨47977691860921824854768855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127940511629124866279383613 47977691860921824854768855)
  ·
    refine ⟨71966537791382737282153283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47977691860921824854768855 71966537791382737282153283)
    ·
      refine ⟨107949806687074105923229925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71966537791382737282153283 107949806687074105923229925)
      ·
        refine ⟨20240588753826394860605611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107949806687074105923229925 20240588753826394860605611)
        ·
          refine ⟨30360883130739592290908417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20240588753826394860605611 30360883130739592290908417)
          ·
            refine ⟨22770662348054694218181313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30360883130739592290908417 22770662348054694218181313)
            ·
              refine ⟨17077996761041020663635985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22770662348054694218181313 17077996761041020663635985)
              ·
                refine ⟨12808497570780765497726989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17077996761041020663635985 12808497570780765497726989)
                ·
                  refine ⟨4803186589042787061647621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12808497570780765497726989 4803186589042787061647621)
                  ·
                    refine ⟨900597485445522574058929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4803186589042787061647621 900597485445522574058929)
                    ·
                      rfl

theorem cell23_5261722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 3, 4].length) (baseStart_5261722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261722 prefixEnd_5261722 := by exact prefixLift 5261722
  have htrace : WordTrace (prefixWord ++ tailWord_5261722) baseStart_5261722 baseEnd_5261722 := by
    simpa [prefixWord, tailWord_5261722, baseEnd_5261722] using wordTrace_append hprefix tailTrace_5261722
  have hstable : (prefixWord ++ tailWord_5261722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261722).length < 2 ^ (prefixWord ++ tailWord_5261722).sum := by decide
  have hdescent : baseEnd_5261722 < baseStart_5261722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261735 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 8]
def baseStart_5261735 : Nat := 118140960795 + 5261735 * 2 ^ 59
def prefixEnd_5261735 : Nat := 4983230072969 + 3 ^ 40 * 5261735 * 2
def baseEnd_5261735 : Nat := 300199903509452907923803

theorem tailTrace_5261735 : CollatzResearch.WordTrace tailWord_5261735 prefixEnd_5261735 300199903509452907923803 := by
  unfold tailWord_5261735
  simp only [CollatzResearch.WordTrace]
  refine ⟨191911241592640202639298659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127940827728426801759532439 191911241592640202639298659)
  ·
    refine ⟨287866862388960303958947989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191911241592640202639298659 287866862388960303958947989)
    ·
      refine ⟨13493759174482514248075687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 287866862388960303958947989 13493759174482514248075687)
      ·
        refine ⟨20240638761723771372113531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13493759174482514248075687 20240638761723771372113531)
        ·
          refine ⟨30360958142585657058170297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20240638761723771372113531 30360958142585657058170297)
          ·
            refine ⟨22770718606939242793627723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30360958142585657058170297 22770718606939242793627723)
            ·
              refine ⟨34156077910408864190441585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22770718606939242793627723 34156077910408864190441585)
              ·
                refine ⟨25617058432806648142831189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34156077910408864190441585 25617058432806648142831189)
                ·
                  refine ⟨300199903509452907923803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25617058432806648142831189 300199903509452907923803)
                  ·
                    rfl

theorem cell23_5261735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 8].length) (baseStart_5261735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261735 prefixEnd_5261735 := by exact prefixLift 5261735
  have htrace : WordTrace (prefixWord ++ tailWord_5261735) baseStart_5261735 baseEnd_5261735 := by
    simpa [prefixWord, tailWord_5261735, baseEnd_5261735] using wordTrace_append hprefix tailTrace_5261735
  have hstable : (prefixWord ++ tailWord_5261735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261735).length < 2 ^ (prefixWord ++ tailWord_5261735).sum := by decide
  have hdescent : baseEnd_5261735 < baseStart_5261735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261749 : List Nat := [1, 3, 3, 2, 3, 1, 1, 2, 2, 2, 3]
def baseStart_5261749 : Nat := 118140960795 + 5261749 * 2 ^ 59
def prefixEnd_5261749 : Nat := 4983230072969 + 3 ^ 40 * 5261749 * 2
def baseEnd_5261749 : Nat := 2701806320314239116539163

theorem tailTrace_5261749 : CollatzResearch.WordTrace tailWord_5261749 prefixEnd_5261749 2701806320314239116539163 := by
  unfold tailWord_5261749
  simp only [CollatzResearch.WordTrace]
  refine ⟨191911752214589483030308301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127941168143059655353538867 191911752214589483030308301)
  ·
    refine ⟨71966907080471056136365613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191911752214589483030308301 71966907080471056136365613)
    ·
      refine ⟨26987590155176646051137105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71966907080471056136365613 26987590155176646051137105)
      ·
        refine ⟨20240692616382484538352829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26987590155176646051137105 20240692616382484538352829)
        ·
          refine ⟨7590259731143431701882311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20240692616382484538352829 7590259731143431701882311)
          ·
            refine ⟨11385389596715147552823467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7590259731143431701882311 11385389596715147552823467)
            ·
              refine ⟨17078084395072721329235201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11385389596715147552823467 17078084395072721329235201)
              ·
                refine ⟨12808563296304540996926401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17078084395072721329235201 12808563296304540996926401)
                ·
                  refine ⟨9606422472228405747694801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12808563296304540996926401 9606422472228405747694801)
                  ·
                    refine ⟨7204816854171304310771101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9606422472228405747694801 7204816854171304310771101)
                    ·
                      refine ⟨2701806320314239116539163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7204816854171304310771101 2701806320314239116539163)
                      ·
                        rfl

theorem cell23_5261749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_5261749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261749 prefixEnd_5261749 := by exact prefixLift 5261749
  have htrace : WordTrace (prefixWord ++ tailWord_5261749) baseStart_5261749 baseEnd_5261749 := by
    simpa [prefixWord, tailWord_5261749, baseEnd_5261749] using wordTrace_append hprefix tailTrace_5261749
  have hstable : (prefixWord ++ tailWord_5261749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261749).length < 2 ^ (prefixWord ++ tailWord_5261749).sum := by decide
  have hdescent : baseEnd_5261749 < baseStart_5261749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
